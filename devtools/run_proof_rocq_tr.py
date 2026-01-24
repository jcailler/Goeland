#!/usr/bin/env python3

import os
import sys
from subprocess import run, PIPE, TimeoutExpired

TIMEOUT = 350          # seconds
RETRY_FOREVER = True


# ============================================================
# Run Goéland with timeout + retry
# ============================================================
def run_goeland(problem_path, prover_option=None):
    opt = f"{prover_option} " if prover_option else ""

    cmd = (
        f"../tool/goeland -noeq "
        f"{opt}"
        f"-otableauxrocq -pretty -proof -context -orocq -chrono "
        f"{problem_path}"
    )

    attempt = 0
    while True:
        attempt += 1
        try:
            print(f"  → Goéland attempt {attempt}")
            res = run(
                cmd,
                shell=True,
                stdout=PIPE,
                stderr=PIPE,
                universal_newlines=True,
                timeout=TIMEOUT,
            )
            return res.stdout

        except TimeoutExpired:
            print(f"  [TIMEOUT] {TIMEOUT}s exceeded")

        except Exception as e:
            print(f"  [ERROR] {e}")

        if not RETRY_FOREVER:
            return ""


# ============================================================
# Parse Goéland output
# ============================================================
def parse_goeland_output(text):
    tr_tableaux_rocq = []
    normal_proof = []
    rocq_proof = []
    gs3_time = None

    section = None       # None | TR | PR
    collecting = None    # None | TR_TABLEAUX | NORMAL | ROCQ

    for line in text.splitlines():
        # -------------------------
        # Section delimiters
        # -------------------------
        if "% SZS output start TR" in line:
            section = "TR"
            collecting = None
            continue

        if "% SZS output end TR" in line:
            section = None
            collecting = None
            continue

        if "% SZS output start Proof and R" in line:
            section = "PR"
            collecting = None
            continue

        if "% SZS output end Proof and R" in line:
            section = None
            collecting = None
            continue

        # -------------------------
        # TR section
        # -------------------------
        if section == "TR":
            if 'Set Warnings "-native-compiler"' in line:
                collecting = "TR_TABLEAUX"
                tr_tableaux_rocq.append(line)
                continue

            if collecting == "TR_TABLEAUX":
                tr_tableaux_rocq.append(line)
                if line.strip() == "Qed.":
                    collecting = None
                continue

        # -------------------------
        # Proof and R section
        # -------------------------
        if section == "PR":
            if "% SZS output start Proof for" in line:
                collecting = "NORMAL"
                continue

            if "% Chrono - GS3 -" in line:
                gs3_time = line.split("-")[-1].strip()
                collecting = None
                continue

            if "% Chrono - Rocq -" in line:
                collecting = "ROCQ"
                continue

            if 'Set Warnings "-native-compiler"' in line:
                collecting = None
                continue

            if collecting == "NORMAL":
                normal_proof.append(line)
            elif collecting == "ROCQ":
                rocq_proof.append(line)

    return {
        "tr_tableaux_rocq": "\n".join(tr_tableaux_rocq).strip(),
        "normal_proof": "\n".join(normal_proof).strip(),
        "rocq_proof": "\n".join(rocq_proof).strip(),
        "gs3_time": gs3_time,
    }


# ============================================================
# Main
# ============================================================
def main():
    if len(sys.argv) not in (3, 4):
        print(
            f"Usage:\n"
            f"  {sys.argv[0]} problem_folder output_folder [prover_option]\n\n"
            f"Examples:\n"
            f"  {sys.argv[0]} problems out\n"
            f"  {sys.argv[0]} problems out -inner\n"
        )
        sys.exit(1)

    problem_dir = sys.argv[1]
    outdir = sys.argv[2]
    prover_option = sys.argv[3] if len(sys.argv) == 4 else None

    os.makedirs(outdir, exist_ok=True)

    gs3_csv = os.path.join(outdir, "gs3_times.csv")

    problems = sorted(f for f in os.listdir(problem_dir) if f.endswith(".p"))

    for prob in problems:
        base = prob[:-2].replace("+", "_").replace(".", "_")
        prob_path = os.path.join(problem_dir, prob)

        print(f"\n=== Processing {prob} ===")

        output = run_goeland(prob_path, prover_option)
        if not output:
            print("  [SKIPPED] No output")
            continue

        parsed = parse_goeland_output(output)

        # -------------------------
        # Write proofs
        # -------------------------
        if parsed["tr_tableaux_rocq"]:
            with open(os.path.join(outdir, f"{base}_tableauxrocq.v"), "w") as f:
                f.write(parsed["tr_tableaux_rocq"] + "\n")

        if parsed["normal_proof"]:
            with open(os.path.join(outdir, f"{base}.proof"), "w") as f:
                f.write(parsed["normal_proof"] + "\n")

        if parsed["rocq_proof"]:
            with open(os.path.join(outdir, f"{base}_rocq.v"), "w") as f:
                f.write(parsed["rocq_proof"] + "\n")

        # -------------------------
        # GS3 time (single CSV)
        # -------------------------
        if parsed["gs3_time"] is not None:
            with open(gs3_csv, "a") as f:
                f.write(f"{base},{parsed['gs3_time']}\n")


if __name__ == "__main__":
    main()
