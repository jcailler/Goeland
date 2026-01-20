#!/usr/bin/env bash

set -euo pipefail

# Check argument
if [ "$#" -ne 1 ]; then
  echo "Usage: $0 <file.p>"
  exit 1
fi

INPUT_FILE="$1"
INPUT_PATH="${INPUT_FILE}"
OUTPUT_PATH="../example/proof.v"

make

./_build/goeland -otableauxrocq "$INPUT_PATH" \
  | grep -v '^%' \
  | sed 's/\x1b\[[0-9;]*m//g' \
  | grep -Ev '^\[[^]]+\]' \
  > "$OUTPUT_PATH"