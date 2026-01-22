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

def extract_tableaurocq(output, outdir, base):
    in_proof = False
    path = os.path.join(outdir, base + "_tableaurocq.v")
    with open(path, "w") as f:
        for line in output.splitlines():
            if "% SZS output start Proof" in line:
                in_proof = True
                continue
            if "% SZS output end Proof" in line:
                in_proof = False
            if in_proof:
                f.write(line + "\n")

def rocq_check(path):
    err = run(f"rocq -c {path}", stdout=PIPE, stderr=PIPE,
              universal_newlines=True, shell=True).stderr
    return "Error" not in err


if len(sys.argv) < 5:
    print("Usage: python3 run_goeland_proofs.py goeland_exec problem_folder timeout outdir")
    exit(1)

exe, folder, timeout, outdir = sys.argv[1:5]
os.makedirs(outdir, exist_ok=True)

entries = [f for f in os.listdir(folder) if f.endswith(".p")]

for file in entries:
    base = file[:-2].replace("+", "_").replace(".", "_")
    full = os.path.join(folder, file)

    print(f"Processing {file}")

    # NORMAL
    out = Out(f"timeout {timeout} {exe} -proof -pretty {full}")
    if "% RES : VALID" in out:
        extract_normal_proof(out, outdir, base)

    # ROCQ
    out = Out(f"timeout {timeout} {exe} -orocq -context -chrono {full}")
    if "% RES : VALID" in out:
        gs3 = extract_rocq(out, outdir, base)
        if not rocq_check(os.path.join(outdir, base + "_rocq.v")):
            print(f"Invalid Rocq proof: {file}")
        if gs3:
            with open(os.path.join(outdir, "gs3_times.csv"), "a") as f:
                f.write(f"{base},{gs3}\n")

    # TABLEAU ROCQ
    out = Out(f"timeout {timeout} {exe} -otableaurocq {full}")
    if "% RES : VALID" in out:
        extract_tableaurocq(out, outdir, base)
        if not rocq_check(os.path.join(outdir, base + "_tableaurocq.v")):
            print(f"Invalid TableauRocq proof: {file}")


