def check(premises, proof, goal):
    proved = []
    for line, (claim, rule, *refs) in enumerate(proof, 1):
        if rule == "premise":
            ok = claim in premises
        elif rule == "modus_ponens":
            a, b = refs
            ok = a < line and b < line and proved[b - 1] == ("if", proved[a - 1], claim)
        else:
            ok = False
        if not ok:
            return f"REJECTED at line {line}"
        proved.append(claim)
    return "ACCEPTED" if proved and proved[-1] == goal else "REJECTED: goal not reached"

premises = [
    "seed honest",
    ("if", "seed honest", "hex1 honest"),
    ("if", "hex1 honest", "hex2 honest"),
]

good = [
    ("seed honest", "premise"),
    (("if", "seed honest", "hex1 honest"), "premise"),
    ("hex1 honest", "modus_ponens", 1, 2),
    (("if", "hex1 honest", "hex2 honest"), "premise"),
    ("hex2 honest", "modus_ponens", 3, 4),
]
skips_a_step = [
    ("seed honest", "premise"),
    (("if", "hex1 honest", "hex2 honest"), "premise"),
    ("hex2 honest", "modus_ponens", 1, 2),
]
invents_a_fact = [
    ("hex1 honest", "premise"),
    (("if", "hex1 honest", "hex2 honest"), "premise"),
    ("hex2 honest", "modus_ponens", 1, 2),
]
print("good:          ", check(premises, good, "hex2 honest"))
print("skips a step:  ", check(premises, skips_a_step, "hex2 honest"))
print("invents a fact:", check(premises, invents_a_fact, "hex2 honest"))
