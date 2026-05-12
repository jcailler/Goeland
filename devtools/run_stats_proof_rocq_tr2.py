import os
import sys
import csv
import collections
import subprocess
import time
import glob
import re
import tempfile


# ---- Count branches in a proof file
def count_branches(path):
    count = 0
    with open(path) as f:
        for line in f:
            if (
                "auto." in line
                or "congruence." in line
                or "mkClosure" in line
            ):
                count += 1
    return count


# ---- Parse chrono header lines from _rocq.v files
#      Expects lines like:  % Chrono - GS3 - 4
#                           % Chrono - Rocq - 4
def parse_chrono_headers(path):
    chrono_gs3 = ""
    chrono_rocq = ""
    pattern = re.compile(r"%\s*Chrono\s*-\s*(\w+)\s*-\s*([\d.]+)", re.IGNORECASE)
    with open(path) as f:
        for i, line in enumerate(f):
            if i >= 10:          # headers are at the very top
                break
            m = pattern.search(line)
            if m:
                label = m.group(1).upper()
                value = m.group(2)
                if label == "GS3":
                    chrono_gs3 = value
                elif label == "ROCQ":
                    chrono_rocq = value
    return chrono_gs3, chrono_rocq


# ---- Remove Rocq/Coq generated artifacts
def cleanup_rocq_artifacts(vfile):
    base, _ = os.path.splitext(vfile)
    for ext in [".vo", ".vok", ".vos", ".glob"]:
        f = base + ext
        if os.path.exists(f):
            os.remove(f)
    folder = os.path.dirname(vfile) or "."
    for f in glob.glob(os.path.join(folder, ".*.aux")):
        if os.path.exists(f):
            os.remove(f)


# ---- Strip chrono header lines and write a temp file for compilation
#      Returns the path to the temp file (caller must delete it).
def make_stripped_tempfile(path):
    chrono_pattern = re.compile(r"%\s*Chrono\s*-", re.IGNORECASE)
    lines = []
    with open(path) as f:
        for line in f:
            if not chrono_pattern.match(line.strip()):
                lines.append(line)
    # Keep temp file in the same directory so relative imports still work
    folder = os.path.dirname(os.path.abspath(path))
    fd, tmp_path = tempfile.mkstemp(suffix=".v", dir=folder)
    with os.fdopen(fd, "w") as tmp:
        tmp.writelines(lines)
    return tmp_path


# ---- Measure Rocq check time (strips chrono headers before compiling)
def rocq_check_time(path, timeout=300):
    cleanup_rocq_artifacts(path)

    tmp_path = make_stripped_tempfile(path)
    try:
        start = time.time()
        proc = subprocess.run(
            ["rocq", "c", tmp_path],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            universal_newlines=True,
            timeout=timeout,
        )
        end = time.time()
        cleanup_rocq_artifacts(tmp_path)

        if proc.returncode != 0:
            print(f"ERROR while checking {path}")
            print(proc.stderr)
            return "ERROR"

        return end - start

    except subprocess.TimeoutExpired:
        cleanup_rocq_artifacts(tmp_path)
        return "TIMEOUT"

    finally:
        if os.path.exists(tmp_path):
            os.remove(tmp_path)
        cleanup_rocq_artifacts(tmp_path)


# ---- Normalize filenames to problem name
def problem_name(filename):
    for suffix in ["_rocq.v", "_tableauxrocq.v"]:
        if filename.endswith(suffix):
            return filename[: -len(suffix)]
    return filename


# ---- Main script
if len(sys.argv) != 2:
    print(f"Usage: python3 {sys.argv[0]} proof_folder")
    sys.exit(1)

folder = sys.argv[1]
outfile = os.path.join(folder, "stats.csv")
data = collections.defaultdict(dict)

# ---- Scan proof files
for file in sorted(os.listdir(folder)):
    path = os.path.join(folder, file)
    key = problem_name(file)

    if file.endswith("_rocq.v"):
        gs3, rocq_chrono = parse_chrono_headers(path)
        data[key]["chrono_gs3"] = gs3
        data[key]["chrono_rocq"] = rocq_chrono
        data[key]["rocq"] = count_branches(path)
        data[key]["rocq_check_time"] = rocq_check_time(path)

    elif file.endswith("_tableauxrocq.v"):
        data[key]["tableauxrocq"] = count_branches(path)
        data[key]["tableauxrocq_check_time"] = rocq_check_time(path)

# ---- Write CSV
with open(outfile, "w", newline="") as csvfile:
    writer = csv.writer(csvfile)
    writer.writerow([
        "problem",
        "chrono_gs3",
        "chrono_rocq",
        "branches_rocq",
        "branches_tableauxrocq",
        "rocq_ratio",
        "rocq_check_time",
        "tableauxrocq_check_time",
    ])

    for k, v in sorted(data.items()):
        br  = v.get("rocq", "")
        bt  = v.get("tableauxrocq", "")
        rt  = v.get("rocq_check_time", "")
        tt  = v.get("tableauxrocq_check_time", "")
        gs3 = v.get("chrono_gs3", "")
        rc  = v.get("chrono_rocq", "")

        ratio = ""
        if br != "" and bt != "" and float(bt)!= 0:
            ratio = float(br) / float(bt)

        writer.writerow([k, gs3, rc, br, bt, ratio, rt, tt])

print(f"Stats written to {outfile}")