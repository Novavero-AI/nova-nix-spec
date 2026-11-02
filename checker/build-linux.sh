#!/bin/sh
# Builds mmcheck as a static 32-bit Linux binary with the M2-Planet and
# mescc-tools in a stage0-pe32 checkout, which must already be built.
#
# Usage: build-linux.sh STAGE0_PE32_DIR OUTPUT

set -eu

if [ "$#" -ne 2 ]; then
  echo "usage: build-linux.sh STAGE0_PE32_DIR OUTPUT" >&2
  exit 2
fi

source_file=$(cd "$(dirname "$0")" && pwd)/mmcheck.c
stage0=$(cd "$1" && pwd)
output=$2
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

tools=$stage0/mescc-tools/bin
cd "$stage0/M2-Planet"

./bin/M2-Planet --architecture x86 --expand-includes "$source_file" -o "$work/mmcheck.M1"
"$tools/M1" --little-endian --architecture x86 \
  -f M2libc/x86/x86_defs.M1 \
  -f M2libc/x86/libc-full.M1 \
  -f "$work/mmcheck.M1" \
  -o "$work/mmcheck.hex2"
"$tools/hex2" --little-endian --architecture x86 --base-address 0x08048000 \
  -f M2libc/x86/ELF-x86.hex2 \
  -f "$work/mmcheck.hex2" \
  -o "$output"
