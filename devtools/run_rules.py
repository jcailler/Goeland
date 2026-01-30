import os
import subprocess
import sys

START_MARKER = "% SZS output start"
END_MARKER = "% SZS output end"

def extract_proof(output: str) -> str:
    lines = output.splitlines()
    inside = False
    proof_lines = []

    for line in lines:
        if line.startswith(START_MARKER):
            inside = True
            continue
        if line.startswith(END_MARKER):
            break
        if inside:
            proof_lines.append(line)

    return "\n".join(proof_lines).strip() + "\n"

def run_goeland_and_rocq(folder_path):
    for filename in os.listdir(folder_path):
        if not filename.endswith(".p"):
            continue

        input_path = os.path.join(folder_path, filename)
        v_filename = filename.replace(".p", ".v")
        v_path = os.path.join(folder_path, v_filename)

        # --- Run Goeland ---
        goeland_cmd = [
            "../src/_build/goeland",
            "-otableauxrocq",
            "-noeq",
            input_path
        ]

        result = subprocess.run(
            goeland_cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True
        )

        proof = extract_proof(result.stdout)

        if not proof.strip():
            print(f"⚠️  No proof found in {filename}")
            continue

        with open(v_path, "w") as f:
            f.write(proof)

        print(f"Generated {v_filename}")

        # --- Run rocq ---
        rocq_cmd = ["rocq", "c", v_filename]

        rocq_result = subprocess.run(
            rocq_cmd,
            cwd=folder_path,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True
        )

        if rocq_result.returncode == 0:
            print(f"✔ rocq succeeded on {v_filename}")
        else:
            print(f"❌ rocq failed on {v_filename}")
            print(rocq_result.stderr)

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python run_rules.py <folder_path>")
        sys.exit(1)

    run_goeland_and_rocq(sys.argv[1])
