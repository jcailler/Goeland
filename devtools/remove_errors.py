import os
import sys

ERROR_SIGNATURE = "Please report at https://github.com/GoelandProver/Goeland/issues"

if len(sys.argv) != 2:
    print("Usage: python clean_goeland_errors.py <directory>")
    sys.exit(1)

DIRECTORY = sys.argv[1]

if not os.path.isdir(DIRECTORY):
    print(f"Error: '{DIRECTORY}' is not a valid directory")
    sys.exit(1)


def file_contains_error(path):
    try:
        with open(path, "r", errors="ignore") as f:
            return ERROR_SIGNATURE in f.read()
    except FileNotFoundError:
        return False


for filename in os.listdir(DIRECTORY):
    if filename.endswith("_rocq.v"):
        rocq_path = os.path.join(DIRECTORY, filename)
        tableaux_filename = filename.replace("_rocq.v", "_tableauxrocq.v")
        tableaux_path = os.path.join(DIRECTORY, tableaux_filename)

        rocq_has_error = file_contains_error(rocq_path)
        tableaux_has_error = file_contains_error(tableaux_path)

        if rocq_has_error or tableaux_has_error:
            print(f"❌ Error detected in pair:")
            if rocq_has_error:
                print(f"   - {filename}")
            if tableaux_has_error:
                print(f"   - {tableaux_filename}")

            # Delete rocq file
            if os.path.exists(rocq_path):
                os.remove(rocq_path)
                print(f"🗑️ Deleted {filename}")

            # Delete tableauxrocq file
            if os.path.exists(tableaux_path):
                os.remove(tableaux_path)
                print(f"🗑️ Deleted {tableaux_filename}")
