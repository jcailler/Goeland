import os
import sys
import csv
import collections
import subprocess
import time
import glob


# ---- Count branches in a proof file
def count_branches(path):
    count = 0
    with open(path) as f:
        for line in f:
            if (
                "auto." in line
                or "congruence." in line
                or "CLOSURE" in line
                or "hasTableauContr" in line
            ):
                count += 1
    return count


# ---- Remove Rocq/Coq generated artifacts

def cleanup_rocq_artifacts(vfile):
    base, _ = os.path.splitext(vfile)
    # remove standard Rocq/Coq files
    for ext in [".vo", ".vok", ".vos", ".glob"]:
        f = base + ext
        if os.path.exists(f):
            os.remove(f)
    # remove hidden .*.aux files in the same folder
    folder = os.path.dirname(vfile)
    for f in glob.glob(os.path.join(folder, ".*.aux")):
        if os.path.exists(f):
            os.remove(f)


# ---- Measure Rocq check time
def rocq_check_time(path, timeout=300):
    cleanup_rocq_artifacts(path)  

    start = time.time()
    try:
        proc = subprocess.run(
            ["rocq", "c", path],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            universal_newlines=True,
            timeout=timeout,
        )
        end = time.time()
        cleanup_rocq_artifacts(path)  

        if proc.returncode != 0:
            print(f"ERROR while checking {path}")
            print(proc.stderr)
            return "ERROR"

        return end - start

    except subprocess.TimeoutExpired:
        cleanup_rocq_artifacts(path)  
        return "TIMEOUT"


# ---- Normalize filenames to problem name
def problem_name(filename):
    for suffix in [".proof", "_rocq.v", "_tableauxrocq.v"]:
        if filename.endswith(suffix):
            return filename[:-len(suffix)]
    return filename


# ---- Main script
if len(sys.argv) != 2:
    print(f"Usage: python3 {sys.argv[0]} proof_folder")
    sys.exit(1)

folder = sys.argv[1]
outfile = folder + "/stats.csv"
data = collections.defaultdict(dict)

# ---- GS3 times
gs3_path = os.path.join(folder, "gs3_times.csv")
if os.path.exists(gs3_path):
    with open(gs3_path) as f:
        for line in f:
            prob, t = line.strip().split(",")
            data[prob]["gs3"] = t

# ---- Scan proof files
for file in os.listdir(folder):
    path = os.path.join(folder, file)
    key = problem_name(file)

    if file.endswith(".proof"):
        data[key]["normal"] = count_branches(path)

    elif file.endswith("_rocq.v"):
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
        "branches_normal",
        "branches_rocq",
        "branches_tableauxrocq",
        "rocq_ratio",
        "gs3_time",
        "rocq_check_time",
        "tableauxrocq_check_time",
    ])

    for k, v in sorted(data.items()):
        bn = v.get("normal", "")
        br = v.get("rocq", "")
        bt = v.get("tableauxrocq", "")
        gs3 = v.get("gs3", "")
        rt = v.get("rocq_check_time", "")
        tt = v.get("tableauxrocq_check_time", "")

        ratio = ""
        if bn != "" and br != "":
            ratio = float(br) / float(bn)

        writer.writerow([k, bn, br, bt, ratio, gs3, rt, tt])
