import os
import sys

TARGET_TEXT = "[MakeProofAux - TR]"

if len(sys.argv) != 2:
    print("Usage: python clean_folder.py <folder_path>")
    sys.exit(1)

folder_path = sys.argv[1]

if not os.path.isdir(folder_path):
    print("Error: provided path is not a folder")
    sys.exit(1)

for filename in os.listdir(folder_path):
    file_path = os.path.join(folder_path, filename)

    if not os.path.isfile(file_path):
        continue

    with open(file_path, "r", encoding="utf-8") as f:
        lines = f.readlines()

    filtered_lines = [line for line in lines if TARGET_TEXT not in line]

    with open(file_path, "w", encoding="utf-8") as f:
        f.writelines(filtered_lines)

print("Done removing lines.")
