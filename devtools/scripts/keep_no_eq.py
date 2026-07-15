import sys
import os
import shutil

if len(sys.argv) != 3:
    print(f"Usage: python3 {sys.argv[0]} input_folder output_folder")
    exit(1)

input_folder = sys.argv[1]
output_root = sys.argv[2]

total_kept = 0
total_skipped = 0

for parent, _, filenames in os.walk(input_folder):
    for fn in filenames:
        full_path = os.path.join(parent, fn)
        try:
            with open(full_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            keep_file = False
            for line in content.splitlines():
                line = line.strip()
                # Keep the file if it contains "Number of atoms" and "0 equ"
                if line.startswith("%") and "Number of atoms" in line and "(   0 equ" in line:
                    keep_file = True
                    break

            if keep_file:
                # Copy to output folder, preserving folder structure
                relative_path = os.path.relpath(full_path, input_folder)
                relative_dir = os.path.dirname(relative_path)
                output_dir = os.path.join(output_root, relative_dir)
                os.makedirs(output_dir, exist_ok=True)
                shutil.copy2(full_path, os.path.join(output_dir, fn))
                total_kept += 1
            else:
                total_skipped += 1

        except Exception as e:
            print(f"Failed to process {full_path}: {e}")

print(f"Total files kept (0 equalities): {total_kept}")
print(f"Total files skipped (contain equalities): {total_skipped}")
