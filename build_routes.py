#!/usr/bin/env python3
"""
build_routes.py — make routes.json for the live bus map (oxon-bus-live).

Downloads the BODS South East GTFS timetable file, keeps every bus route that
stops inside the Oxford / Witney area, and writes a small routes.json with each
route's line shape and stops. The map page loads routes.json and draws a route
when you click a bus.

Run on your VM (Python 3.8+, no extra packages):
    python3 build_routes.py                     # download + build
    python3 build_routes.py --zip south_east.zip  # use a file you already have
    python3 build_routes.py --out /home/USER/public_html/buses/routes.json

Re-run monthly (timetables change), e.g. cron:
    15 4 1 * * /usr/bin/python3 /home/USER/build_routes.py --out /home/USER/public_html/buses/routes.json
"""

import argparse
import csv
import io
import json
import math
import os
import sys
import time
import urllib.request
import zipfile
from collections import Counter, defaultdict

GTFS_URL = "https://data.bus-data.dft.gov.uk/timetable/download/gtfs-file/south_east/"

# Area of interest (minLon, minLat, maxLon, maxLat): routes with at least one
# stop inside this box are kept — their full length is kept, even outside it.
AREA = (-1.62, 51.66, -1.12, 51.86)  # Oxford + Witney + Carterton/Eynsham/Woodstock

MAX_PATTERNS = 4        # stop patterns kept per line + operator + direction
MIN_SHARE = 0.10        # ignore patterns used by < 10% of that line's trips
SIMPLIFY_METRES = 8     # shape simplification tolerance

csv.field_size_limit(10 ** 8)


def log(msg):
    print(time.strftime("%H:%M:%S"), msg, flush=True)


# ---------------------------------------------------------------- download
def download(url, dest, api_key=None):
    if api_key:
        url += ("&" if "?" in url else "?") + "api_key=" + api_key
    log("Downloading GTFS (can be a few hundred MB)...")
    req = urllib.request.Request(url, headers={"User-Agent": "oxon-bus-live/1.0"})
    tmp = dest + ".part"
    with urllib.request.urlopen(req, timeout=600) as r, open(tmp, "wb") as f:
        total = 0
        while True:
            chunk = r.read(1 << 20)
            if not chunk:
                break
            f.write(chunk)
            total += len(chunk)
            if total % (50 << 20) < (1 << 20):
                log(f"  {total >> 20} MB")
    os.replace(tmp, dest)
    log(f"Saved {dest} ({os.path.getsize(dest) >> 20} MB)")


# ---------------------------------------------------------------- csv helpers
def rows(zf, name):
    """Stream rows of a GTFS file inside the zip as dicts (handles BOM)."""
    names = {os.path.basename(n): n for n in zf.namelist()}
    if name not in names:
        return
    with zf.open(names[name]) as raw:
        text = io.TextIOWrapper(raw, encoding="utf-8-sig", newline="")
        for row in csv.DictReader(text):
            yield row


def has_file(zf, name):
    return any(os.path.basename(n) == name for n in zf.namelist())


# ---------------------------------------------------------------- geometry
def to_xy(lat, lon, lat0):
    k = 111320.0
    return (lon * k * math.cos(math.radians(lat0)), lat * k)


def simplify(points, tol):
    """Douglas-Peucker on [lat, lon] points, tolerance in metres."""
    if len(points) < 3:
        return points
    lat0 = points[0][0]
    xy = [to_xy(p[0], p[1], lat0) for p in points]
    keep = [False] * len(points)
    keep[0] = keep[-1] = True
    stack = [(0, len(points) - 1)]
    while stack:
        a, b = stack.pop()
        ax, ay = xy[a]
        bx, by = xy[b]
        dx, dy = bx - ax, by - ay
        seg = dx * dx + dy * dy
        best, idx = -1.0, -1
        for i in range(a + 1, b):
            px, py = xy[i]
            if seg == 0:
                d = math.hypot(px - ax, py - ay)
            else:
                t = max(0, min(1, ((px - ax) * dx + (py - ay) * dy) / seg))
                d = math.hypot(px - (ax + t * dx), py - (ay + t * dy))
            if d > best:
                best, idx = d, i
        if best > tol and idx > 0:
            keep[idx] = True
            stack.append((a, idx))
            stack.append((idx, b))
    return [p for p, k in zip(points, keep) if k]


def r5(x):
    return round(float(x), 5)


# ---------------------------------------------------------------- build
def build(zip_path, out_path):
    zf = zipfile.ZipFile(zip_path)

    # agencies → NOC (BODS GTFS has agency_noc; fall back to agency_id)
    agency_noc = {}
    for a in rows(zf, "agency.txt"):
        agency_noc[a.get("agency_id", "")] = (a.get("agency_noc") or a.get("agency_id") or "").strip()
    log(f"{len(agency_noc)} operators")

    # stops
    stops = {}
    in_area = set()
    for s in rows(zf, "stops.txt"):
        try:
            lat, lon = float(s["stop_lat"]), float(s["stop_lon"])
        except (KeyError, ValueError):
            continue
        sid = s["stop_id"]
        stops[sid] = (s.get("stop_name", "").strip(), lat, lon)
        if AREA[0] <= lon <= AREA[2] and AREA[1] <= lat <= AREA[3]:
            in_area.add(sid)
    log(f"{len(stops)} stops, {len(in_area)} in area")

    # routes
    routes = {}
    for r in rows(zf, "routes.txt"):
        line = (r.get("route_short_name") or r.get("route_long_name") or "").strip()
        noc = agency_noc.get(r.get("agency_id", ""), r.get("agency_id", ""))
        routes[r["route_id"]] = (line, noc, r.get("route_type", "3"))

    # pass 1: which trips touch the area?
    log("Scanning stop_times (pass 1)...")
    wanted = set()
    n = 0
    for st in rows(zf, "stop_times.txt"):
        n += 1
        if st["stop_id"] in in_area:
            wanted.add(st["trip_id"])
    log(f"  {n} stop_times rows, {len(wanted)} trips touch the area")

    # trips info for wanted trips
    trips = {}
    for t in rows(zf, "trips.txt"):
        tid = t["trip_id"]
        if tid in wanted and t["route_id"] in routes:
            trips[tid] = (
                t["route_id"],
                (t.get("direction_id") or "").strip(),
                (t.get("shape_id") or "").strip(),
                (t.get("trip_headsign") or "").strip(),
            )
    wanted &= set(trips)

    # pass 2: stop sequences for wanted trips
    log("Reading stop sequences (pass 2)...")
    seqs = defaultdict(list)
    for st in rows(zf, "stop_times.txt"):
        tid = st["trip_id"]
        if tid in wanted:
            try:
                seqs[tid].append((int(st["stop_sequence"]), st["stop_id"]))
            except ValueError:
                pass

    # group trips into patterns per (line, operator, direction)
    groups = defaultdict(Counter)       # key -> Counter(pattern)
    example = {}                        # (key, pattern) -> (shape_id, headsign)
    headsigns = defaultdict(Counter)
    for tid, seq in seqs.items():
        route_id, direction, shape_id, headsign = trips[tid]
        line, noc, rtype = routes[route_id]
        if not line:
            continue
        pattern = tuple(s for _, s in sorted(seq))
        if len(pattern) < 2:
            continue
        key = (line, noc, direction)
        groups[key][pattern] += 1
        example.setdefault((key, pattern), shape_id)
        headsigns[(key, pattern)][headsign] += 1
    log(f"{len(groups)} line/operator/direction groups")

    # choose patterns, collect shape ids
    chosen = []
    need_shapes = set()
    for key, counter in groups.items():
        total = sum(counter.values())
        for pattern, count in counter.most_common(MAX_PATTERNS):
            if count / total < MIN_SHARE and count != counter.most_common(1)[0][1]:
                continue
            sid = example[(key, pattern)]
            if sid:
                need_shapes.add(sid)
            chosen.append((key, pattern, count, sid))

    # shapes (optional in GTFS)
    shapes = defaultdict(list)
    if need_shapes and has_file(zf, "shapes.txt"):
        log(f"Reading {len(need_shapes)} shapes...")
        for sh in rows(zf, "shapes.txt"):
            if sh["shape_id"] in need_shapes:
                try:
                    shapes[sh["shape_id"]].append(
                        (int(float(sh["shape_pt_sequence"])), float(sh["shape_pt_lat"]), float(sh["shape_pt_lon"]))
                    )
                except ValueError:
                    pass

    # output
    out = defaultdict(list)
    for (line, noc, direction), pattern, count, shape_id in chosen:
        stop_list = [[stops[s][0], r5(stops[s][1]), r5(stops[s][2])] for s in pattern if s in stops]
        if len(stop_list) < 2:
            continue
        if shape_id and len(shapes.get(shape_id, [])) >= 2:
            pts = [[p[1], p[2]] for p in sorted(shapes[shape_id])]
            shape_src = "shape"
        else:
            pts = [[s[1], s[2]] for s in stop_list]
            shape_src = "stops"
        pts = [[r5(a), r5(b)] for a, b in simplify(pts, SIMPLIFY_METRES)]
        headsign = headsigns[((line, noc, direction), pattern)].most_common(1)[0][0]
        out[line].append({
            "op": noc,
            "dir": {"0": "outbound", "1": "inbound"}.get(direction, direction),
            "headsign": headsign,
            "from": stop_list[0][0],
            "to": stop_list[-1][0],
            "trips": count,
            "geom": shape_src,
            "shape": pts,
            "stops": stop_list,
        })

    result = {
        "generated": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "source": "Bus Open Data Service (DfT), Open Government Licence v3.0",
        "area": AREA,
        "lines": dict(sorted(out.items())),
    }
    tmp = out_path + ".part"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(result, f, separators=(",", ":"), ensure_ascii=False)
    os.replace(tmp, out_path)
    n_pat = sum(len(v) for v in out.values())
    log(f"Wrote {out_path}: {len(out)} lines, {n_pat} patterns, {os.path.getsize(out_path) // 1024} KB")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--zip", help="use an existing GTFS zip instead of downloading")
    ap.add_argument("--keep-zip", default="south_east_gtfs.zip", help="where to save the download")
    ap.add_argument("--api-key", default=os.environ.get("BODS_API_KEY"), help="only if the download asks for one")
    ap.add_argument("--out", default="routes.json")
    a = ap.parse_args()

    zip_path = a.zip
    if not zip_path:
        zip_path = a.keep_zip
        download(GTFS_URL, zip_path, a.api_key)
    build(zip_path, a.out)


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        sys.exit(1)
