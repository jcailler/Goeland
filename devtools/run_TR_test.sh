#!/usr/bin/env bash

set -euo pipefail

QUIET=0

# Parse options
while [[ $# -gt 0 ]]; do
  case "$1" in
    -q|--quiet)
      QUIET=1
      shift
      ;;
    -*)
      echo "Unknown option: $1"
      exit 1
      ;;
    *)
      break
      ;;
  esac
done

# Check argument
if [ "$#" -ne 1 ]; then
  echo "Usage: $0 [-q|--quiet] <file.p>"
  exit 1
fi

INPUT_PATH="$1"
OUTPUT_PATH="../benchs/proof.v"

cd ../src/ && make

if [[ "$QUIET" -eq 1 ]]; then
  # No stdout at all
  # ./_build/goeland -otableauxrocq "$INPUT_PATH" \
  ../src/_build/goeland -context -orocq -noeq "$INPUT_PATH" \
    | grep -v '^%' \
    | sed 's/\x1b\[[0-9;]*m//g' \
    | grep -Ev '^\[[^]]+\]' \
    > "$OUTPUT_PATH"
else
  # Stdout = filtered-out lines only
  # ../src/_build/goeland -context -orocq -noeq "$INPUT_PATH" \
  ../src/_build/goeland -otableauxrocq -inner -noeq "$INPUT_PATH" \
    | tee >(
        grep -v '^%' \
        | sed 's/\x1b\[[0-9;]*m//g' \
        | grep -Ev '^\[[^]]+\]' \
        > "$OUTPUT_PATH"
      ) \
    | grep -E '^%|\x1b\[[0-9;]*m|\[[^]]+\]'
fi

# rocq c ../benchs/proof.v
