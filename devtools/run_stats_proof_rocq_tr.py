import os, sys, csv, collections

def count_branches(path):
    count = 0
    with open(path) as f:
        for line in f:
            if ("auto." in line or
                "congruence." in line or
                "CLOSURE" in line or
                "hasTableauContr" in line):
                count += 1
    return count

if len(sys.argv) != 3:
    print("Usage: python3 merge_results.py proof_folder output.csv")
    exit(1)

folder, outfile = sys.argv[1], sys.argv[2]

data = collections.defaultdict(dict)

# Load GS3 times
gs3_path = os.path.join(folder, "gs3_times.csv")
if os.path.exists(gs3_path):
    with open(gs3_path) as f:
        for line in f:
            prob, t = line.strip().split(",")
            data[prob]["gs3"] = t

for file in os.listdir(folder):
    path = os.path.join(folder, file)
    key = file.split(".")[0]

    if file.endswith(".proof"):
        data[key]["normal"] = count_branches(path)

    elif file.endswith("_rocq.v"):
        data[key]["rocq"] = count_branches(path)

    elif file.endswith("_tableaurocq.v"):
        data[key]["tableaurocq"] = count_branches(path)

with open(outfile, "w", newline="") as csvfile:
    writer = csv.writer(csvfile)
    writer.writerow([
        "problem",
        "branches_normal",
        "branches_rocq",
        "branches_tableaurocq",
        "rocq_ratio",
        "gs3_time"
    ])

    for k, v in sorted(data.items()):
        bn = v.get("normal", "")
        br = v.get("rocq", "")
        bt = v.get("tableaurocq", "")
        gs3 = v.get("gs3", "")

        ratio = ""
        if bn and br:
            ratio = float(br) / float(bn)

        writer.writerow([k, bn, br, bt, ratio, gs3])
