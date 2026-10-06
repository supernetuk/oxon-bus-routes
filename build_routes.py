#!/usr/bin/env python3
"""
build_routes.py — England-wide bus route files for the live bus map (oxon-bus-live).

For each BODS GTFS region it downloads the timetable zip, works out the main
stop patterns of every bus line, and writes one small JSON file per
operator + line into a site folder that GitHub Actions publishes to GitHub Pages:

    site/r/<NOC>/<LINE>.json   route shapes + stops for one operator's line
    site/l/<LINE>.json         which operators run a line of that name, and where
    site/info.json             build date and totals

The map page loads only the file for the bus you click, so it stays fast.

Usage (normally run by GitHub Actions, see .github/workflows/build.yml):
    python build_routes.py --site site
    python build_routes.py --site site --regions south_east,london
    python build_routes.py --site site --zip a.zip --zip b.zip   # local files, no download
"""

import argparse
import csv
import io
import json
import math
import os
import shutil
import sys
import time
import urllib.error
import urllib.request
import zipfile
from collections import Counter, defaultdict

GTFS_BASE = "https://data.bus-data.dft.gov.uk/timetable/download/gtfs-file/"
# England regions; scotland / wales are tried too and skipped if BODS has no file.
REGIONS = [
    "east_anglia", "east_midlands", "london", "north_east", "north_west",
    "south_east", "south_west", "west_midlands", "yorkshire",
    "scotland", "wales",
]

MAX_PATTERNS = 3        # stop patterns kept per operator + line + direction
MIN_SHARE = 0.10        # drop patterns used by < 10% of that group's trips
SIMPLIFY_METRES = 12    # shape simplification tolerance

csv.field_size_limit(10 ** 8)


def log(msg):
    print(time.strftime("%H:%M:%S"), msg, flush=True)


# ---------------------------------------------------------------- download
def download(region, dest, api_key=None):
    url = GTFS_BASE + region + "/"
    if api_key:
        url += "?api_key=" + api_key
    req = urllib.request.Request(url, headers={"User-Agent": "oxon-bus-live/1.0"})
    tmp = dest + ".part"
    try:
        with urllib.request.urlopen(req, timeout=900) as r, open(tmp, "wb") as f:
            shutil.copyfileobj(r, f, 1 << 20)
    except urllib.error.HTTPError as e:
        if os.path.exists(tmp):
            os.remove(tmp)
        if e.code in (403, 404):
            log(f"  {region}: no file on BODS (HTTP {e.code}), skipping")
            return False
        raise
    os.replace(tmp, dest)
    if not zipfile.is_zipfile(dest):
        log(f"  {region}: download is not a zip, skipping")
        os.remove(dest)
        return False
    log(f"  {region}: {os.path.getsize(dest) >> 20} MB")
    return True


# ---------------------------------------------------------------- csv helpers
def rows(zf, name):
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
def simplify(points, tol):
    """Douglas-Peucker on [lat, lon] points, tolerance in metres."""
    if len(points) < 3:
        return points
    k = 111320.0
    c = math.cos(math.radians(points[0][0]))
    xy = [(p[1] * k * c, p[0] * k) for p in points]
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
                t = max(0.0, min(1.0, ((px - ax) * dx + (py - ay) * dy) / seg))
                d = math.hypot(px - (ax + t * dx), py - (ay + t * dy))
            if d > best:
                best, idx = d, i
        if best > tol and idx > 0:
            keep[idx] = True
            stack.append((a, idx))
            stack.append((idx, b))
    return [p for p, kp in zip(points, keep) if kp]


def encode_polyline(points):
    """Google encoded polyline, precision 5 — about 4x smaller than JSON numbers."""
    out = []
    plat = plon = 0
    for lat, lon in points:
        ilat, ilon = int(round(lat * 1e5)), int(round(lon * 1e5))
        for v in (ilat - plat, ilon - plon):
            v = ~(v << 1) if v < 0 else (v << 1)
            while v >= 0x20:
                out.append(chr((0x20 | (v & 0x1F)) + 63))
                v >>= 5
            out.append(chr(v + 63))
        plat, plon = ilat, ilon
    return "".join(out)


# ---------------------------------------------------------------- file names
def safe_name(s):
    """Same rule as the map page: keep A-Z a-z 0-9 - _, encode anything else as ~HH."""
    out = []
    for ch in s:
        if ch.isascii() and (ch.isalnum() or ch in "-_"):
            out.append(ch)
        else:
            out.extend("~%02X" % b for b in ch.encode("utf-8"))
    return "".join(out) or "~"


# ---------------------------------------------------------------- one region
def process_zip(zip_path, label):
    """Return {(noc, line): [pattern dicts]} for one GTFS zip."""
    zf = zipfile.ZipFile(zip_path)

    agency_noc = {}
    for a in rows(zf, "agency.txt"):
        agency_noc[a.get("agency_id", "")] = (a.get("agency_noc") or a.get("agency_id") or "").strip()

    stops = {}
    for s in rows(zf, "stops.txt"):
        try:
            stops[s["stop_id"]] = (s.get("stop_name", "").strip(), float(s["stop_lat"]), float(s["stop_lon"]))
        except (KeyError, ValueError):
            pass

    routes = {}
    for r in rows(zf, "routes.txt"):
        line = (r.get("route_short_name") or r.get("route_long_name") or "").strip()
        if line:
            routes[r["route_id"]] = (line, agency_noc.get(r.get("agency_id", ""), r.get("agency_id", "")).strip())

    trips = {}
    for t in rows(zf, "trips.txt"):
        if t["route_id"] in routes:
            trips[t["trip_id"]] = (
                t["route_id"],
                (t.get("direction_id") or "").strip(),
                (t.get("shape_id") or "").strip(),
                (t.get("trip_headsign") or "").strip(),
            )
    log(f"  {label}: {len(routes)} routes, {len(trips)} trips, {len(stops)} stops")

    # Stream stop_times once. BODS files are grouped by trip, so each trip is
    # finished as soon as the next one starts; anything out of order is merged.
    pattern_ids = {}                    # stop tuple -> id
    pattern_list = []                   # id -> stop tuple
    groups = defaultdict(Counter)       # (noc, line, dir) -> Counter(pattern id)
    extra = {}                          # (group, pid) -> (shape_id, Counter(headsign))
    done = set()
    counted = {}                        # trip -> (group, pattern id, headsign), to undo if needed
    late = set()                        # trips whose rows were split up in the file (rare)
    cur_tid, cur = None, []
    n = 0

    def finish(tid, seq):
        info = trips.get(tid)
        if not info or len(seq) < 2:
            return
        route_id, direction, shape_id, headsign = info
        line, noc = routes[route_id]
        pattern = tuple(s for _, s in sorted(seq))
        pid = pattern_ids.get(pattern)
        if pid is None:
            pid = pattern_ids[pattern] = len(pattern_list)
            pattern_list.append(pattern)
        g = (noc, line, direction)
        groups[g][pid] += 1
        e = extra.get((g, pid))
        if e is None:
            e = extra[(g, pid)] = (shape_id, Counter())
        e[1][headsign] += 1
        counted[tid] = (g, pid, headsign)

    for st in rows(zf, "stop_times.txt"):
        n += 1
        tid = st["trip_id"]
        if tid not in trips:
            continue
        try:
            item = (int(st["stop_sequence"]), st["stop_id"])
        except ValueError:
            continue
        if tid == cur_tid:
            cur.append(item)
            continue
        if cur_tid is not None:
            done.add(cur_tid)
            finish(cur_tid, cur)
        if tid in done:
            late.add(tid)
            cur_tid, cur = None, []
        else:
            cur_tid, cur = tid, [item]
        if n % 5_000_000 == 0:
            log(f"    {n // 1_000_000}M stop_times rows")
    if cur_tid is not None:
        finish(cur_tid, cur)
    if late:
        # re-read the split trips in full, undo their partial counts, count them properly
        log(f"    {len(late)} trips were split up in the file; re-reading them")
        full = defaultdict(list)
        for st in rows(zf, "stop_times.txt"):
            if st["trip_id"] in late:
                try:
                    full[st["trip_id"]].append((int(st["stop_sequence"]), st["stop_id"]))
                except ValueError:
                    pass
        for tid in late:
            prev = counted.pop(tid, None)
            if prev:
                g, pid, hs = prev
                groups[g][pid] -= 1
                if groups[g][pid] <= 0:
                    del groups[g][pid]
                extra[(g, pid)][1][hs] -= 1
            finish(tid, full[tid])
    del done, late, trips, counted

    chosen = []
    need_shapes = set()
    for g, counter in groups.items():
        total = sum(counter.values())
        if not total:
            continue
        top = counter.most_common(MAX_PATTERNS)
        for i, (pid, count) in enumerate(top):
            if i and count / total < MIN_SHARE:
                continue
            shape_id = extra[(g, pid)][0]
            if shape_id:
                need_shapes.add(shape_id)
            chosen.append((g, pid, count))

    shapes = defaultdict(list)
    if need_shapes and has_file(zf, "shapes.txt"):
        for sh in rows(zf, "shapes.txt"):
            if sh["shape_id"] in need_shapes:
                try:
                    shapes[sh["shape_id"]].append(
                        (float(sh["shape_pt_sequence"]), float(sh["shape_pt_lat"]), float(sh["shape_pt_lon"])))
                except ValueError:
                    pass

    result = defaultdict(list)
    for (noc, line, direction), pid, count in chosen:
        stop_rows = [stops[s] for s in pattern_list[pid] if s in stops]
        if len(stop_rows) < 2:
            continue
        shape_id, heads = extra[((noc, line, direction), pid)]
        if shape_id and len(shapes.get(shape_id, ())) >= 2:
            pts = [[p[1], p[2]] for p in sorted(shapes[shape_id])]
            geom = "shape"
        else:
            pts = [[s[1], s[2]] for s in stop_rows]   # no road path published: the map asks TomTom for one
            geom = "stops"
        pts = simplify(pts, SIMPLIFY_METRES)
        lats = [p[0] for p in pts] + [s[1] for s in stop_rows]
        lons = [p[1] for p in pts] + [s[2] for s in stop_rows]
        heads = +heads                      # drop zero counts
        result[(noc, line)].append({
            "dir": {"0": "outbound", "1": "inbound"}.get(direction, direction),
            "headsign": heads.most_common(1)[0][0] if heads else "",
            "from": stop_rows[0][0],
            "to": stop_rows[-1][0],
            "trips": count,
            "shape": encode_polyline(pts),
            "geom": geom,
            "stops": encode_polyline([(s[1], s[2]) for s in stop_rows]),
            "names": [s[0] for s in stop_rows],
            "bbox": [round(min(lats), 4), round(min(lons), 4), round(max(lats), 4), round(max(lons), 4)],
        })
    log(f"  {label}: {len(result)} operator lines, {sum(len(v) for v in result.values())} patterns")
    return result


# ---------------------------------------------------------------- main
def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--site", default="site", help="output folder (published to GitHub Pages)")
    ap.add_argument("--regions", default=",".join(REGIONS), help="comma-separated BODS GTFS regions")
    ap.add_argument("--zip", action="append", help="use local GTFS zip(s) instead of downloading")
    ap.add_argument("--work", default="/tmp/gtfs", help="where downloads go (deleted after use)")
    ap.add_argument("--api-key", default=os.environ.get("BODS_API_KEY") or None)
    a = ap.parse_args()

    allroutes = defaultdict(dict)   # (noc, line) -> {stops polyline: pattern}  (dedupes across regions)
    regions_done = []

    def merge(res):
        for key, pats in res.items():
            for p in pats:
                existing = allroutes[key].get(p["stops"])
                if existing is None or p["trips"] > existing["trips"]:
                    allroutes[key][p["stops"]] = p

    if a.zip:
        for z in a.zip:
            log(f"Processing {z}")
            merge(process_zip(z, os.path.basename(z)))
            regions_done.append(os.path.basename(z))
    else:
        os.makedirs(a.work, exist_ok=True)
        for region in [r.strip() for r in a.regions.split(",") if r.strip()]:
            log(f"Region {region}: downloading")
            path = os.path.join(a.work, region + ".zip")
            try:
                if not download(region, path, a.api_key):
                    continue
                merge(process_zip(path, region))
                regions_done.append(region)
            except Exception as e:                      # one bad region shouldn't stop the rest
                log(f"  {region}: FAILED ({e.__class__.__name__}: {e}), skipping")
            finally:
                if os.path.exists(path):
                    os.remove(path)

    if not allroutes:
        log("No routes built — nothing to publish.")
        sys.exit(1)

    # write site
    if os.path.exists(a.site):
        shutil.rmtree(a.site)
    os.makedirs(os.path.join(a.site, "r"))
    os.makedirs(os.path.join(a.site, "l"))
    by_line = defaultdict(list)
    total_bytes = 0
    for (noc, line), pats in allroutes.items():
        pats = sorted(pats.values(), key=lambda p: -p["trips"])
        bbox = [min(p["bbox"][0] for p in pats), min(p["bbox"][1] for p in pats),
                max(p["bbox"][2] for p in pats), max(p["bbox"][3] for p in pats)]
        by_line[line].append({"op": noc, "bbox": bbox})
        d = os.path.join(a.site, "r", safe_name(noc))
        os.makedirs(d, exist_ok=True)
        path = os.path.join(d, safe_name(line) + ".json")
        with open(path, "w", encoding="utf-8") as f:
            json.dump({"op": noc, "line": line, "patterns": pats}, f, separators=(",", ":"), ensure_ascii=False)
        total_bytes += os.path.getsize(path)
    for line, ops in by_line.items():
        path = os.path.join(a.site, "l", safe_name(line) + ".json")
        with open(path, "w", encoding="utf-8") as f:
            json.dump(ops, f, separators=(",", ":"), ensure_ascii=False)
        total_bytes += os.path.getsize(path)

    info = {
        "generated": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "source": "Bus Open Data Service (DfT), Open Government Licence v3.0",
        "regions": regions_done,
        "operator_lines": len(allroutes),
        "line_names": len(by_line),
        "megabytes": round(total_bytes / 1e6, 1),
    }
    with open(os.path.join(a.site, "info.json"), "w") as f:
        json.dump(info, f, indent=1)
    with open(os.path.join(a.site, "index.html"), "w") as f:
        f.write("<!doctype html><meta charset=utf-8><title>Bus route data</title>"
                "<p>Bus route data for the live bus map. Built from BODS (DfT), OGL v3. "
                "See <a href='info.json'>info.json</a>.</p>")
    log(f"Done: {len(allroutes)} operator lines, {len(by_line)} line names, "
        f"{info['megabytes']} MB, regions: {', '.join(regions_done)}")


if __name__ == "__main__":
    main()
