#!/usr/bin/env python3
import subprocess
import sys
import os

# List of folders to process
folders = [
    "../benchs/SCALING_SUCCESS_PROOF/",
    "../benchs/SCALING_SUCCESS_INNER_PROOF/",
    "../benchs/SET_THM_INCLUDE_SUCCESS_PROOF",
    "../benchs/SET_THM_INCLUDE_SUCCESS_INNER_PROOF",
    "../benchs/SYN_THM_INCLUDE_SUCCESS_PROOF",
    "../benchs/SYN_THM_INCLUDE_SUCCESS_INNER_PROOF"
]

script = "run_stats_proof_rocq_tr.py"  # your main script

for folder in folders:
    # generate output filename
    output_csv = os.path.join(folder, "stats_output.csv")
    print(f"Processing folder: {folder}")
    cmd = ["python3", script, folder, output_csv]
    result = subprocess.run(cmd)
    if result.returncode != 0:
        print(f"Error processing folder {folder}")
    else:
        print(f"Finished folder {folder}")
