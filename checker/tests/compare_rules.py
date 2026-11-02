"""Runs a checker over rules_test.py's cases, verdict by exit status.

Exit status other than 0 or 1 is a crash, and a crash is never a refusal.

Usage: compare_rules.py CHECKER
"""
import importlib.util
import pathlib
import subprocess
import sys
import tempfile

# Where the specification leaves room, and mmcheck and verify.py each chose.
KNOWN_DIFFERENCES = {
    "comment close at bare eof": "mmcheck takes end of file as white space",
    "included file ends in bare close": "mmcheck takes end of file as white space",
    "include close at bare eof": "mmcheck takes end of file as white space",
    "include another spelling of the same file": "mmcheck compares names, as the book allows",
    "include directory": "the C subset cannot tell a directory from an empty file",
}


def load_cases():
    path = pathlib.Path(__file__).with_name("rules_test.py")
    spec = importlib.util.spec_from_file_location("rules_test", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.CASES


def status_of(checker, files):
    if not isinstance(files, dict):
        files = {"main.mm": files}
    with tempfile.TemporaryDirectory() as directory:
        for name, content in files.items():
            pathlib.Path(directory, name).write_bytes(content)
        return subprocess.run(
            [checker, "main.mm"], cwd=directory, capture_output=True, text=True, timeout=60
        ).returncode


def main():
    checker = sys.argv[1]
    cases = [case for case in load_cases() if case[0] not in KNOWN_DIFFERENCES]
    failed = 0
    for name, files, expected in cases:
        status = status_of(checker, files)
        if status != (0 if expected is None else 1):
            failed += 1
            print(f"FAILED {name}: status {status}")
    print(f"{len(cases)} cases, {failed} failed, {len(KNOWN_DIFFERENCES)} known differences")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
