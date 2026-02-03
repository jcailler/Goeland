import sys

if len(sys.argv) != 2:
    print("Usage: python remove_error_lines.py <input.csv>")
    sys.exit(1)

input_file = sys.argv[1]
output_file = input_file.replace(".csv", "_no_error.csv")

with open(input_file, "r") as fin, open(output_file, "w") as fout:
    for line in fin:
        if "ERROR" not in line:
            fout.write(line)

print(f"Cleaned file written to: {output_file}")
