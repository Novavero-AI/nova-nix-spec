"""Runs a real hex0 seed and Hex0.decode on the same inputs and compares them.

Usage: seed_behaviour.py SEED DECODE KNOWN

SEED is the seed binary, and DECODE is `lake build decode`'s executable.
KNOWN names the inputs on which this seed is known to differ from decode, as a
comma-separated list, or "none". Any other difference fails, and so does a
known one that has gone away.
"""
import os
import pathlib
import subprocess
import sys
import tempfile

CASES = {
    "empty": b"",
    "one byte": b"4D",
    "two bytes": b"4D5A",
    "lower case": b"4d5a",
    "pending digit at end": b"4",
    "digits split by space": b"4 D",
    "digits split by newline": b"4\nD",
    "hash comment": b"# 41\n42",
    "semicolon comment": b"; 41\n42",
    "comment after a digit": b"4#x\nD",
    "comment at end of file": b"41 # no newline",
    "carriage returns": b"4\r\nD\r\n",
    "every other byte as filler": bytes(b for b in range(256) if b not in b"0123456789ABCDEFGabcdefg#;\n") + b"7E",
    "G before a digit": b"GA",
    "g before a digit": b"gA",
    "G after a digit": b"AG",
    "G in a comment": b"# G\n41",
}


def run_seed(seed, data, directory):
    source = pathlib.Path(directory, "in")
    output = pathlib.Path(directory, "out")
    source.write_bytes(data)
    if output.exists():
        output.unlink()
    result = subprocess.run([seed, str(source), str(output)], capture_output=True, timeout=60)
    if result.returncode != 0:
        return f"exit {result.returncode}"
    return output.read_bytes()


def run_decode(decode, data, directory):
    source = pathlib.Path(directory, "in")
    output = pathlib.Path(directory, "spec")
    source.write_bytes(data)
    subprocess.run([decode, str(source), str(output)], check=True, capture_output=True, timeout=60)
    return output.read_bytes()


def main():
    if len(sys.argv) != 4:
        sys.exit("usage: seed_behaviour.py SEED DECODE KNOWN")
    seed = os.path.abspath(sys.argv[1])
    decode = os.path.abspath(sys.argv[2])
    known = set() if sys.argv[3] == "none" else set(sys.argv[3].split(","))
    unknown = known - set(CASES)
    if unknown:
        sys.exit(f"no such cases: {sorted(unknown)}")
    failed = 0
    with tempfile.TemporaryDirectory() as directory:
        for name, data in CASES.items():
            got = run_seed(seed, data, directory)
            want = run_decode(decode, data, directory)
            differs = got != want
            if differs and name in known:
                print(f"known   {name}: seed {got!r}, decode {want!r}")
            elif differs:
                print(f"DIFFERS {name}: seed {got!r}, decode {want!r}")
                failed += 1
            elif name in known:
                print(f"GONE    {name}: a known difference no longer happens")
                failed += 1
            else:
                print(f"same    {name}")
    print(f"{len(CASES)} inputs, {failed} failed")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
