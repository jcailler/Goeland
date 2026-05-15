#!/usr/bin/env python3

import os
import sys
import csv
from subprocess import run, PIPE, TimeoutExpired

TIMEOUT = 300 # seconds


# ============================================================
# Run Goéland
# ============================================================
def run_goeland(problem_path, mode):
    if mode == "rocq":
        cmd = f"../tool/goeland -context -orocq -noeq {problem_path}"
    elif mode == "tableauxRocq":
        cmd = f"../tool/goeland -noeq -otableauxrocq {problem_path}"
    else:
        raise ValueError(f"Unknown mode: {mode}")

    try:
        print(f"  → {mode}: {cmd}")
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
        return ""

    except Exception as e:
        print(f"  [ERROR] {e}")
        return ""


# ============================================================
# Extract proof
# ============================================================
def extract_proof(text):
    collecting = False
    proof = []

    for line in text.splitlines():
        if "% SZS output start Proof" in line:
            collecting = True
            continue
        if "% SZS output end Proof" in line:
            break
        if collecting:
            proof.append(line)

    return "\n".join(proof).strip()


# ============================================================
# Extract GS3 chrono
# ============================================================
def extract_gs3_chrono(text):
    """
    Extracts '% Chrono - GS3 - <time>' from Goéland output.
    Returns int or None.
    """
    for line in text.splitlines():
        line = line.strip()
        if line.startswith("% Chrono - GS3 -"):
            try:
                return int(line.split("-")[-1].strip())
            except ValueError:
                return None
    return None


# ============================================================
# Main
# ============================================================
def main():
    if len(sys.argv) != 3:
        print(f"Usage:\n  {sys.argv[0]} <problem_folder> <output_folder>")
        sys.exit(1)

    problem_dir = sys.argv[1]
    outdir = sys.argv[2]

    os.makedirs(outdir, exist_ok=True)

    # CSV setup
    csv_path = os.path.join(outdir, "gs3_chrono.csv")
    csv_exists = os.path.exists(csv_path)

    csvfile = open(csv_path, "a", newline="")
    writer = csv.writer(csvfile)

    if not csv_exists:
        writer.writerow(["problem", "gs3_time"])

    problems = sorted(f for f in os.listdir(problem_dir) if f.endswith(".p"))

    for prob in problems:
        base = prob[:-2].replace("+", "_").replace(".", "_")
        prob_path = os.path.join(problem_dir, prob)

        print(f"\n=== Processing {prob} ===")

        # Rocq
        rocq_out = run_goeland(prob_path, "rocq")
        rocq_proof = extract_proof(rocq_out)
        gs3_time = extract_gs3_chrono(rocq_out)

        if rocq_proof:
            with open(os.path.join(outdir, f"{base}_rocq.v"), "w") as f:
                f.write(rocq_proof + "\n")
            print("  ✓ Rocq proof written")
        else:
            print("  [NO ROCQ PROOF]")

        writer.writerow([prob, gs3_time if gs3_time is not None else ""])

        # Tableaux Rocq
        tab_out = run_goeland(prob_path, "tableauxRocq")
        tab_proof = extract_proof(tab_out)

        if tab_proof:
            with open(os.path.join(outdir, f"{base}_tableauxrocq.v"), "w") as f:
                f.write(tab_proof + "\n")
            print("  ✓ Tableaux Rocq proof written")
        else:
            print("  [NO TABLEAUX PROOF]")

    csvfile.close()


if __name__ == "__main__":
    main()
