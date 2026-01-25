#!/usr/bin/env python3

import os
import sys
from subprocess import run, PIPE, TimeoutExpired

TIMEOUT = 500          # seconds
RETRY_FOREVER = False

# ============================================================
# Global temp output file (set in main)
# ============================================================
TMP_OUTPUT_FILE = None


# ============================================================
# Run Goéland with timeout + retry
# ============================================================
def run_goeland(problem_path, prover_option=None):
    opt = f"{prover_option} " if prover_option else ""

    cmd = (
        f"../src/_build/goeland -noeq -inner "
        f"{opt}"
        f"-otableauxrocq -pretty -proof -context -orocq -chrono "
        f"{problem_path}"
    )

    attempt = 0
    while attempt < 10:
        attempt += 1
        try:
            print(f"  → Goéland attempt {attempt}")

            with open(TMP_OUTPUT_FILE, "w") as out:
                run(
                    cmd,
                    shell=True,
                    stdout=out,
                    stderr=PIPE,
                    universal_newlines=True,
                    timeout=TIMEOUT,
                )

            return True

        except TimeoutExpired:
            print(f"  [TIMEOUT] {TIMEOUT}s exceeded")

        except Exception as e:
            print(f"  [ERROR] {e}")

    if not RETRY_FOREVER:
        return False


# ============================================================
# Parse Goéland output (FROM GLOBAL FILE)
# ============================================================
def parse_goeland_output():
    print(f"  Parsing...")
    tr_tableaux_rocq = []
    normal_proof = []
    rocq_proof = []
    gs3_time = None

    section = None       # None | TR | PR
    collecting = None    # None | TR_TABLEAUX | NORMAL | ROCQ

    with open(TMP_OUTPUT_FILE, "r") as f:
        for line in f:
            line = line.rstrip("\n")

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
    global TMP_OUTPUT_FILE

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
        # Visible, persistent raw output file
        TMP_OUTPUT_FILE = os.path.join(outdir, f"{base}_raw.out")

        print(f"\n=== Processing {prob} ===")

        ok = run_goeland(prob_path, prover_option)
        if not ok:
            print("  [SKIPPED] No output")
            continue

        parsed = parse_goeland_output()

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
