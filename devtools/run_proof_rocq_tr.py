import os, sys, re, csv
from subprocess import run, PIPE

def Out(cmd):
    return run(cmd, stdout=PIPE, stderr=PIPE,
               universal_newlines=True, shell=True).stdout

def extract_normal_proof(output, outdir, base):
    path = os.path.join(outdir, base + ".proof")
    in_proof = False
    with open(path, "w") as f:
        for line in output.splitlines():
            if "% SZS output start Proof" in line:
                in_proof = True
                continue
            if "% SZS output end Proof" in line:
                in_proof = False
            if in_proof:
                f.write(line + "\n")

def extract_rocq(output, outdir, base):
    gs3 = None
    in_rocq = False
    path = os.path.join(outdir, base + "_rocq.v")

    with open(path, "w") as f:
        for line in output.splitlines():
            if "% Chrono - GS3 -" in line:
                gs3 = line.split("-")[-1].strip()
            if "% Chrono - Rocq -" in line:
                in_rocq = True
                continue
            if "% SZS output end Proof" in line:
                in_rocq = False
            if in_rocq:
                f.write(line + "\n")

    return gs3

def extract_tableauxrocq(output, outdir, base):
    in_proof = False
    path = os.path.join(outdir, base + "_tableauxrocq.v")
    with open(path, "w") as f:
        for line in output.splitlines():
            if "% SZS output start Proof" in line:
                in_proof = True
                continue
            if "% SZS output end Proof" in line:
                in_proof = False
            if in_proof:
                f.write(line + "\n")


if len(sys.argv) < 4:
    print(f"Usage: python3 {sys.argv[0]} problem_folder timeout outdir goeland_options")
    exit(1)

folder = sys.argv[1]
timeout = sys.argv[2]
outdir = sys.argv[3]
exe = " ../tool/goeland -noeq " + " ".join(sys.argv[4:]) + " "
os.makedirs(outdir, exist_ok=True)

entries = [f for f in os.listdir(folder) if f.endswith(".p")]

for file in entries:
    base = file[:-2].replace("+", "_").replace(".", "_")
    full = os.path.join(folder, file)

    print(f"Processing {file}")

    # NORMAL
    out = Out(f"{exe} -proof -pretty {full}")
    if "% RES : VALID" in out:
        extract_normal_proof(out, outdir, base)

    # ROCQ
    out = Out(f"{exe} -orocq -context -chrono {full}")
    if "% RES : VALID" in out:
        gs3 = extract_rocq(out, outdir, base)
        if gs3:
            with open(os.path.join(outdir, "gs3_times.csv"), "a") as f:
                f.write(f"{base},{gs3}\n")

    # TABLEAUX ROCQ
    out = Out(f"{exe} -otableauxrocq {full}")
    if "% RES : VALID" in out:
        extract_tableauxrocq(out, outdir, base)


