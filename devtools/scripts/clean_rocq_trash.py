import os
import glob
import sys

def cleanup_rocq_artifacts(vfile):
    base, _ = os.path.splitext(vfile)

    # Remove standard Rocq/Coq files
    for ext in [".vo", ".vok", ".vos", ".glob"]:
        f = base + ext
        if os.path.exists(f):
            os.remove(f)

    # Remove hidden .*.aux files in the same folder
    folder = os.path.dirname(vfile) or "."
    for f in glob.glob(os.path.join(folder, ".*.aux")):
        if os.path.exists(f):
            os.remove(f)

def cleanup_folder(folder_path):
    for filename in os.listdir(folder_path):
        if filename.endswith(".v"):
            vfile = os.path.join(folder_path, filename)
            cleanup_rocq_artifacts(vfile)
            print(f"Cleaned artifacts for {filename}")

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python cleanup_rocq.py <folder_path>")
        sys.exit(1)

    cleanup_folder(sys.argv[1])
