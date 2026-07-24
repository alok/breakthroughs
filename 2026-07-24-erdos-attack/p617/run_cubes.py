#!/usr/bin/env python3
"""Cube-and-conquer driver for #617 K26: one cube per sorted vertex-0 profile."""
import subprocess, sys, os
from concurrent.futures import ThreadPoolExecutor

def profiles(total=25, parts=5, mx=25):
    if parts == 1:
        if total <= mx:
            yield (total,)
        return
    for first in range(min(mx, total), (total + parts - 1) // parts - 1, -1):
        for rest in profiles(total - first, parts - 1, first):
            yield (first,) + rest

profs = list(profiles())
print(f"{len(profs)} cubes", file=sys.stderr)
os.makedirs("cubes", exist_ok=True)
TIME = int(sys.argv[1]) if len(sys.argv) > 1 else 1800

def run(prof):
    name = "-".join(map(str, prof))
    cnf, res = f"cubes/p{name}.cnf", f"cubes/p{name}.out"
    if not os.path.exists(cnf):
        subprocess.run(["/opt/homebrew/bin/python3", "gen_sat2.py", "profile",
                        ",".join(map(str, prof)), cnf], check=True,
                       capture_output=True)
    r = subprocess.run(["kissat", "-q", f"--time={TIME}", cnf],
                       capture_output=True, text=True)
    open(res, "w").write(r.stdout)
    status = ("SAT!!" if r.returncode == 10 else
              "UNSAT" if r.returncode == 20 else "TIMEOUT")
    print(f"{name}: {status}", flush=True)
    return prof, status

with ThreadPoolExecutor(max_workers=13) as ex:
    results = list(ex.map(run, profs))

sat = [p for p, s in results if s == "SAT!!"]
to = [p for p, s in results if s == "TIMEOUT"]
print(f"\nDONE. SAT: {sat}\nTIMEOUT({len(to)}): {to[:20]}")
