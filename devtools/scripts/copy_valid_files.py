import sys
import os
import shutil

if len(sys.argv) != 4:
    print("Usage: python copy_valid_files.py <evaluation.csv> <source_folder> <destination_folder>")
    sys.exit(1)

csv_file = sys.argv[1]
source_folder = sys.argv[2]
destination_folder = sys.argv[3]

# Create destination folder if it doesn't exist
os.makedirs(destination_folder+"_problems", exist_ok=True)
os.makedirs(destination_folder+"_proofs", exist_ok=True)

valid_files = []

# Step 1: Read CSV and collect filenames without ERROR
with open(csv_file, "r") as f:
    for line in f:
        if "ERROR" not in line:
            # Adjust column index if needed
            filename = line.strip().split(",")[0]
            valid_files.append(filename)

print(f"Found {len(valid_files)} valid files.")

# Step 2: Copy corresponding files
copied = 0
missing = 0

for filename in valid_files:
    src_path1 = os.path.join(source_folder+"_proofs", filename+"_rocq.v")
    src_path2 = os.path.join(source_folder+"_proofs", filename+"_tableauxrocq.v")
    dst_path1 = os.path.join(destination_folder+"_proofs", filename+"_rocq.v")
    dst_path2 = os.path.join(destination_folder+"_proofs", filename+"_tableauxrocq.v")
    
    transformed_name = filename.replace("_", "+") + ".p"
    src_path3 = os.path.join(source_folder+"_problems", transformed_name)
    dst_path3 = os.path.join(destination_folder+"_problems", transformed_name)

    if os.path.isfile(src_path1) and os.path.isfile(src_path2): # and os.path.isfile(src_path3):
        shutil.copy2(src_path1, dst_path1)
        shutil.copy2(src_path2, dst_path2)
        # shutil.copy2(src_path3, dst_path3)
        copied += 1    
    else:
        print(f"File not found: {filename}")
        missing += 1



print(f"Copied: {copied}")
print(f"Missing: {missing}")