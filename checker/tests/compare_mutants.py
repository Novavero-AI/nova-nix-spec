"""Corrupts real databases and compares a checker with verify.py.

Both verdicts come from exit status alone, and anything but 0 or 1 is a crash.
Any disagreement fails the run. A mutation that leaves a database valid is
accepted by both, so only a disagreement means something.

Usage: compare_mutants.py SEED CHECKER SUITE_DIR DIVISOR
"""
import collections
import concurrent.futures
import os
import pathlib
import random
import subprocess
import sys
import tempfile

KEYWORDS = {"$c", "$v", "$f", "$e", "$d", "$a", "$p", "$=", "$.", "${", "$}"}
BASES = [
    ("anatomy.mm", 300),
    ("demo0.mm", 800),
    ("miu.mm", 400),
    ("hol.mm", 3000),
    ("big-unifier.mm", 300),
    ("ql.mm", 1800),
    ("set.mm", 2500),
]
SET_HEAD_TOKENS = 60000
WORKERS = os.cpu_count() or 1


def strip_comments(text):
    out = []
    in_comment = False
    for token in text.split():
        if token == "$(":
            in_comment = True
        elif token == "$)":
            in_comment = False
        elif not in_comment:
            out.append(token)
    return out


def truncate_at_outermost(tokens, limit):
    depth = 0
    last = 0
    for i, token in enumerate(tokens):
        if token == "${":
            depth += 1
        elif token == "$}":
            depth -= 1
        elif token != "$.":
            continue
        if depth == 0:
            last = i + 1
            if last >= limit:
                break
    return tokens[:last]


def statement_spans(tokens):
    """(start, end) of each labelled or $d statement, end exclusive."""
    spans = []
    start = None
    for i, token in enumerate(tokens):
        if token in ("${", "$}"):
            start = None
            continue
        if start is None:
            start = i
        if token == "$.":
            spans.append((start, i + 1))
            start = None
    return spans


def proof_regions(tokens):
    regions = []
    i = 0
    while i < len(tokens):
        if tokens[i] == "$=":
            j = i + 1
            while tokens[j] != "$.":
                j += 1
            regions.append((i + 1, j))
            i = j
        i += 1
    return regions


def mutate(tokens, spans, regions, symbols, rng):
    t = list(tokens)
    kind = rng.choice(
        [
            "delete", "duplicate", "swap", "replace", "letter", "letter", "letter",
            "drop_statement", "drop_d", "drop_d", "swap_statements", "symbol", "symbol",
            "proof_swap", "proof_swap", "proof_delete", "proof_insert", "paren_swap",
        ]
    )
    if kind in ("delete", "duplicate", "swap", "replace"):
        i = rng.randrange(len(t) - 1)
        if kind == "delete":
            del t[i]
        elif kind == "duplicate":
            t.insert(i, t[i])
        elif kind == "swap":
            t[i], t[i + 1] = t[i + 1], t[i]
        else:
            t[i] = rng.choice(t)
    elif kind in ("drop_statement", "drop_d", "swap_statements"):
        if kind == "drop_d":
            choices = [s for s in spans if t[s[0]] == "$d"]
        else:
            choices = spans
        if not choices:
            return None, kind
        a = rng.choice(choices)
        if kind == "swap_statements":
            b = rng.choice(spans)
            if b[0] < a[0]:
                a, b = b, a
            if a[1] > b[0]:
                return None, kind
            t = t[: a[0]] + t[b[0] : b[1]] + t[a[1] : b[0]] + t[a[0] : a[1]] + t[b[1] :]
        else:
            del t[a[0] : a[1]]
    elif kind == "symbol":
        choices = [s for s in spans if t[s[0] + 1] in ("$e", "$a", "$p")]
        if not choices or not symbols:
            return None, kind
        s = rng.choice(choices)
        end = s[1]
        for j in range(s[0], s[1]):
            if t[j] == "$=":
                end = j
                break
        if end - s[0] < 4:
            return None, kind
        t[rng.randrange(s[0] + 2, end - 1)] = rng.choice(symbols)
    else:
        if not regions:
            return None, kind
        start, end = rng.choice(regions)
        if end - start < 2:
            return None, kind
        compressed = t[start] == "("
        if compressed:
            close = t.index(")", start)
            if kind == "paren_swap":
                if close - start < 3:
                    return None, kind
                i = rng.randrange(start + 1, close - 1)
                t[i], t[i + 1] = t[i + 1], t[i]
                return t, kind
            body = close + 1
            if body >= end:
                return None, kind
            i = rng.randrange(body, end)
            word = list(t[i])
            j = rng.randrange(len(word))
            if kind == "letter" or kind == "proof_insert":
                letter = rng.choice("ABCDEFGHIJKLMNOPQRSTUVWXYZ")
                if kind == "letter":
                    word[j] = letter
                else:
                    word.insert(j, letter)
            elif kind == "proof_delete":
                del word[j]
            elif j + 1 < len(word):
                word[j], word[j + 1] = word[j + 1], word[j]
            else:
                return None, kind
            t[i] = "".join(word) or "A"
        else:
            if kind == "paren_swap" or kind == "letter":
                return None, kind
            i = rng.randrange(start, end - 1)
            if kind == "proof_swap":
                t[i], t[i + 1] = t[i + 1], t[i]
            elif kind == "proof_delete":
                del t[i]
            else:
                t.insert(i, t[rng.randrange(start, end)])
    return t, kind


def run(command, directory):
    return subprocess.run(command, cwd=directory, capture_output=True, text=True, timeout=120)


def trial(mmcheck, verify, data, kind):
    with tempfile.TemporaryDirectory() as directory:
        pathlib.Path(directory, "m.mm").write_bytes(data)
        mine = run([mmcheck, "m.mm"], directory)
        blind = run([sys.executable, "-I", verify, "m.mm"], directory)
    if mine.returncode not in (0, 1) or blind.returncode not in (0, 1):
        outcome = "crash"
    elif mine.returncode == blind.returncode:
        return ("accept" if mine.returncode == 0 else "refuse", kind)
    elif mine.returncode == 0:
        outcome = "MMCHECK_ACCEPTS"
    else:
        outcome = "mmcheck_refuses"
    print(
        f"{outcome} {kind}\n  checker {mine.returncode}: {mine.stderr.strip()[-200:]}\n"
        f"  verify.py {blind.returncode}: {blind.stderr.strip()[-200:]}",
        flush=True,
    )
    return (outcome, kind)


def main():
    seed, mmcheck, suite, divisor = sys.argv[1:5]
    mmcheck = os.path.abspath(mmcheck)
    verify = str(pathlib.Path(__file__).with_name("verify.py"))
    rng = random.Random(int(seed))
    jobs = []
    for name, count in BASES:
        tokens = strip_comments(pathlib.Path(suite, name).read_text())
        if name == "set.mm":
            tokens = truncate_at_outermost(tokens, SET_HEAD_TOKENS)
        spans = statement_spans(tokens)
        regions = proof_regions(tokens)
        symbols = []
        for s, e in spans:
            if tokens[s] in ("$c", "$v"):
                symbols.extend(tokens[s + 1 : e - 1])
        count = max(1, count // int(divisor))
        made = 0
        attempts = 0
        while made < count and attempts < count * 20:
            attempts += 1
            mutant, kind = mutate(tokens, spans, regions, symbols, rng)
            if mutant is None:
                continue
            jobs.append((" ".join(mutant).encode(), kind))
            made += 1
    print(f"{len(jobs)} mutants", flush=True)
    tally = collections.Counter()
    by_kind = collections.Counter()
    with concurrent.futures.ThreadPoolExecutor(WORKERS) as pool:
        futures = [pool.submit(trial, mmcheck, verify, d, k) for d, k in jobs]
        for future in concurrent.futures.as_completed(futures):
            outcome, kind = future.result()
            tally[outcome] += 1
            by_kind[(kind, outcome)] += 1
    print(dict(tally))
    return 1 if set(tally) - {"accept", "refuse"} else 0


if __name__ == "__main__":
    sys.exit(main())
