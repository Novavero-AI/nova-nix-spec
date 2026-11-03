"""Removes each die() from mmcheck.c in turn, except those LEFT_OUT matches, and
asks whether any test notices.

A surviving variant gets every verdict right with that check gone, so the check
is untested or redundant. Variants build with sanitizers, so a memory guard
counts as noticed when removing it faults. Capacity limits are left out, since
reaching them takes huge inputs, as are invariants nothing can reach and the
checks on opening and reading a file. A variant that does not compile fails the
run, since its check has not been tried.

Usage: kill_checks.py SUITE_DIR WORK_DIR
"""
import concurrent.futures
import importlib.util
import os
import pathlib
import re
import subprocess
import sys
import tempfile

LEFT_OUT = re.compile(
    r"too many|too deep|too deeply|exhausted|\$d too long|expression too long|too large"
    r"|out of memory|cannot read"
    r"|no substitution|before its length|past its length"
)
SANITIZER_STATUS = 99
SANITIZED_ENV = dict(
    os.environ,
    ASAN_OPTIONS=f"exitcode={SANITIZER_STATUS}:detect_leaks=0",
    UBSAN_OPTIONS=f"exitcode={SANITIZER_STATUS}:halt_on_error=1",
)
FAST_SUITE = [
    ("anatomy.mm", True), ("anatomy-bad1.mm", False), ("anatomy-bad2.mm", False),
    ("anatomy-bad3.mm", False), ("big-unifier.mm", True), ("big-unifier-bad1.mm", False),
    ("big-unifier-bad2.mm", False), ("big-unifier-bad3.mm", False), ("demo0.mm", True),
    ("demo0-bad1.mm", False), ("hol.mm", True), ("miu.mm", True), ("ql.mm", True),
    ("set-dist-bad1.mm", False), ("iset.mm", True),
]
WORKERS = os.cpu_count() or 1


def load_cases():
    path = pathlib.Path(__file__).with_name("compare_rules.py")
    spec = importlib.util.spec_from_file_location("compare_rules", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return [c for c in module.load_cases() if c[0] not in module.KNOWN_DIFFERENCES]


def run(binary, directory, name):
    try:
        result = subprocess.run(
            [binary, name],
            cwd=directory,
            capture_output=True,
            text=True,
            timeout=60,
            env=SANITIZED_ENV,
        )
    except subprocess.TimeoutExpired:
        return "hang"
    return result.returncode


def caught(binary, cases, suite):
    """Name of the first test that tells this variant apart, or None."""
    for name, files, expected in cases:
        if not isinstance(files, dict):
            files = {"main.mm": files}
        with tempfile.TemporaryDirectory() as directory:
            for file_name, content in files.items():
                pathlib.Path(directory, file_name).write_bytes(content)
            status = run(binary, directory, "main.mm")
        if status != (0 if expected is None else 1):
            return f"rule: {name} (status {status})"
    for name, accepted in FAST_SUITE:
        status = run(binary, suite, name)
        if status != (0 if accepted else 1):
            return f"suite: {name} (status {status})"
    return None


def one(source_lines, index, work, cases, suite):
    line = source_lines[index]
    variant = list(source_lines)
    variant[index] = re.sub(r"die\(.*\);\s*$", ";", line)
    path = pathlib.Path(work, f"v{index}.c")
    path.write_text("\n".join(variant) + "\n")
    binary = str(path.with_suffix(""))
    subprocess.run(
        [
            "cc", "-std=c99", "-O1", "-g", "-w",
            "-fsanitize=address,undefined", "-fno-sanitize-recover=undefined",
            "-o", binary, str(path),
        ],
        check=True,
    )
    return index, line.strip(), caught(binary, cases, suite)


def main():
    suite, work = (os.path.abspath(a) for a in sys.argv[1:3])
    source = pathlib.Path(__file__).parent.parent / "mmcheck.c"
    pathlib.Path(work).mkdir(parents=True, exist_ok=True)
    lines = pathlib.Path(source).read_text().split("\n")
    cases = load_cases()
    checks = [
        i for i, l in enumerate(lines) if re.search(r"\bdie\(\"", l) and not l.startswith("void die")
    ]
    sites = [i for i in checks if not LEFT_OUT.search(lines[i])]
    print(f"removing {len(sites)} of {len(checks)} checks, {len(cases)} rule cases", flush=True)
    results = []
    with concurrent.futures.ThreadPoolExecutor(WORKERS) as pool:
        futures = [pool.submit(one, lines, i, work, cases, suite) for i in sites]
        for future in concurrent.futures.as_completed(futures):
            results.append(future.result())
    results.sort()
    survivors = [r for r in results if r[2] is None]
    print(f"caught {len(results) - len(survivors)} of {len(results)}")
    for index, line, _ in survivors:
        print(f"SURVIVED line {index + 1}: {line}")
    return 1 if survivors else 0


if __name__ == "__main__":
    sys.exit(main())
