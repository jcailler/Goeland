import os
import sys
from collections import defaultdict

if len(sys.argv) != 2:
    print(f"Usage: {sys.argv[0]} <folder>")
    sys.exit(1)

FOLDER = sys.argv[1]

EXPECTED_FILES = {
    "rocq": "_rocq.v",
    "tableauxrocq": "_tableauxrocq.v",
}

problems = defaultdict(set)

# Scan files in the folder
for filename in os.listdir(FOLDER):
    if filename.endswith("_rocq.v"):
        base = filename[:-7]
        problems[base].add("rocq")
    elif filename.endswith("_tableauxrocq.v"):
        base = filename[:-15]
        problems[base].add("tableauxrocq")

# Check for missing files
for problem, present in sorted(problems.items()):
    missing = set(EXPECTED_FILES.keys()) - present
    if missing:
        print(f"Problem '{problem}' is missing:")
        for m in missing:
            print(f"  - {problem}{EXPECTED_FILES[m]}")
