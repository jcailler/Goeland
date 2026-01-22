import os
import sys
import re
import shutil
from subprocess import PIPE, run

def Out(command):
    result = run(command, stdout=PIPE, stderr=PIPE, universal_newlines=True, shell=True, encoding='utf-8')
    return result.stdout

def LaunchTest(prover_name, command_line, success, memory_limit=None, failure=None):
    output = Out(command_line).encode('utf-8', errors='ignore').decode(errors='ignore')
    res = False

    if re.search(success, output):
        print(f"Found proof. Good job, {prover_name} !")
        res = True
    else:
        print("Proof not found")
    
    return res

if len(sys.argv) < 4: 
    print(f"python3 {sys.argv[0]} problem_folder output_folder_suffix timeout goeland_options")
else:
    folder = sys.argv[1]
    folder_split = folder.split("/")
    folder += "/"
   
    suffix = sys.argv[2]
    entries = os.listdir(folder)
    timeout = sys.argv[3]

    # Create the success folder name
    success_folder = folder.rstrip("/") + f"_{suffix}/"
    os.makedirs(success_folder, exist_ok=True)

    cpt = 0
    total = len(entries)

    for index, file in enumerate(entries):
        problem_path = folder + file
        print(f"Problem {index+1}/{total} : {problem_path}")

        if LaunchTest("Goéland", "timeout "+timeout+" ../tool/goeland -noeq" + " ".join(sys.argv[4:]) + " " + problem_path, "% RES : VALID", None, "% RES : NOT VALID"):
            cpt += 1
            # Copy the file to the success folder
            shutil.move(problem_path, success_folder)
            print(f"Copied {file} to {success_folder}")

    print(f"Number of problems solved : {cpt}/{total}")
