#!/usr/bin/env python3
"""Strict Metamath proof verifier, written from the language specification.

Usage: python3 -I verify.py FILE.mm

Exit status 0: every statement is well formed and every $p proof checks.
Exit status 1: refusal, with one line on stderr naming the rule broken.
Exit status 2: wrong command line, no verdict.

Included file names are relative to the current directory.

Comments marked "Open case" record where the specification does not settle a
case and this verifier refuses rather than accepts.
"""

import dataclasses
import itertools
import os
import re
import sys

WHITE_SPACE_BYTES = b" \t\r\n\f"
PRINTABLE_BYTES = bytes(range(0x21, 0x7F))
SOURCE_BYTES = WHITE_SPACE_BYTES + PRINTABLE_BYTES

TOKEN = re.compile(r"[^ \t\r\n\f]+")
LABEL = re.compile(r"[A-Za-z0-9._-]+")
COMPRESSED_LETTERS = re.compile(r"[A-Z]+")

KEYWORDS = frozenset(
    {
        "${",
        "$}",
        "$c",
        "$v",
        "$f",
        "$e",
        "$d",
        "$a",
        "$p",
        "$.",
        "$=",
        "$(",
        "$)",
        "$[",
        "$]",
    }
)
LABELLED_KEYWORDS = ("$f", "$e", "$a", "$p")
END = "$."
UNKNOWN_STEP = "?"

# A compressed integer is zero or more U-Y digits in base 5, then one A-T digit
# in base 20, with digits counting from 1.
LOW_DIGITS = {letter: value for value, letter in enumerate("ABCDEFGHIJKLMNOPQRST", 1)}
HIGH_DIGITS = {letter: value for value, letter in enumerate("UVWXY", 1)}
LOW_BASE = len(LOW_DIGITS)
HIGH_BASE = len(HIGH_DIGITS)


class Refusal(Exception):
    """The database breaks a rule of the specification."""


@dataclasses.dataclass(frozen=True)
class Hypothesis:
    label: str
    expression: tuple[str, ...]
    variable: str | None  # the variable of a $f statement, None for a $e


@dataclasses.dataclass(frozen=True)
class Assertion:
    label: str
    expression: tuple[str, ...]
    hypotheses: tuple[Hypothesis, ...]  # mandatory, in order of occurrence
    disjoint: frozenset[frozenset[str]]  # mandatory $d pairs


@dataclasses.dataclass
class Block:
    hypothesis_count: int  # active hypotheses when the block began
    disjoint_count: int  # active $d pairs when the block began
    variables: list[str]  # symbols declared by $v in this block


def decode_source(data, name):
    """Check the characters of one source file and return it as text."""
    stray = data.translate(None, SOURCE_BYTES)
    if stray:
        raise Refusal(f"{name}: byte 0x{stray[0]:02x} is not allowed in a source file")
    # Open case: the $(, $), $[ and $] keywords "must be surrounded by white
    # space". A database may begin with a comment at its first byte, so the start
    # of a file counts as a boundary. The syntax appendix does not require
    # support for $) at a bare end of file, so that is refused, and $] with it.
    # $( and $[ cannot validly end a file, and other tokens need no white space
    # there because tokens are only "separated by" it.
    if data.endswith((b"$)", b"$]")):
        raise Refusal(f"{name}: a final $) or $] must be followed by white space")
    return data.decode("ascii")


def tokens_of(text, name):
    """Yield the tokens of one source file with its comments removed."""
    in_comment = False
    in_include = False
    for match in TOKEN.finditer(text):
        token = match.group()
        if in_comment:
            if token == "$)":
                in_comment = False
            elif "$(" in token or "$)" in token:
                raise Refusal(f"{name}: a comment may not contain $( or $) ({token})")
        elif token == "$(":
            # Open case: comments count as white space, but the syntax appendix
            # says databases should not put one in a file inclusion command.
            if in_include:
                raise Refusal(f"{name}: comment inside a file inclusion command")
            in_comment = True
        elif token == "$)":
            raise Refusal(f"{name}: $) without a matching $(")
        elif "$" in token and token not in KEYWORDS:
            raise Refusal(f"{name}: {token} is not a keyword, label or math symbol")
        else:
            if token == "$[":
                in_include = True
            elif token == "$]":
                in_include = False
            yield token
    if in_comment:
        raise Refusal(f"{name}: $( without a matching $)")


def read_until(source, terminators, where):
    """Return the tokens before the next terminator, and that terminator."""
    tokens = []
    for token in source:
        if token in terminators:
            return tokens, token
        if token in KEYWORDS:
            raise Refusal(f"{where}: {token} may not occur here in a statement")
        tokens.append(token)
    raise Refusal(f"{where}: the file ends inside a statement")


def read_statement_body(source, where):
    """Return the tokens before the next $. token."""
    tokens, _ = read_until(source, (END,), where)
    return tokens


def substitute(expression, substitution):
    """Replace every variable of an expression at once.

    An assertion's substitution holds all of its variables, so a symbol missing
    from the map is a constant.
    """
    result = []
    for symbol in expression:
        if symbol in substitution:
            result.extend(substitution[symbol])
        else:
            result.append(symbol)
    return tuple(result)


class ProofCheck:
    """One run of the proof stack for the $p statement `proved`."""

    def __init__(self, database, proved):
        self.database = database
        self.proved = proved
        self.stack = []
        self.active_pairs = frozenset(database.active_disjoint)

    def refusal(self, message):
        return Refusal(f"{self.proved.label}: {message}")

    def run(self, proof):
        if proof[:1] == ["("]:
            self.run_compressed(proof[1:])
        else:
            self.run_normal(proof)
        if len(self.stack) != 1:
            raise self.refusal(
                f"the proof must leave one stack entry, not {len(self.stack)}"
            )
        if self.stack[0] != self.proved.expression:
            raise self.refusal("the proof does not prove the $p statement")

    def run_normal(self, proof):
        for label in proof:
            if label == UNKNOWN_STEP:
                raise self.refusal("incomplete proof containing ?")
            if label in self.database.assertions:
                self.take_step(self.database.assertions[label])
            elif label in self.database.active_hypotheses_by_label:
                self.take_step(self.database.active_hypotheses_by_label[label])
            else:
                raise self.refusal(
                    f"proof label {label} is not an active hypothesis or an"
                    " earlier assertion"
                )

    def run_compressed(self, tokens):
        if ")" not in tokens:
            raise self.refusal("compressed proof without a closing parenthesis")
        closing = tokens.index(")")
        listed = [self.listed_statement(label) for label in tokens[:closing]]
        letters = "".join(tokens[closing + 1 :])
        if UNKNOWN_STEP in letters:
            raise self.refusal("incomplete proof containing ?")
        if not COMPRESSED_LETTERS.fullmatch(letters):
            raise self.refusal("a compressed proof must end in letters A to Z")

        statements = [*self.proved.hypotheses, *listed]
        tagged = []
        number = 0
        taggable = False
        for letter in letters:
            if letter in LOW_DIGITS:
                self.take_numbered_step(
                    number * LOW_BASE + LOW_DIGITS[letter], statements, tagged
                )
                number = 0
                taggable = True
            elif letter in HIGH_DIGITS:
                number = number * HIGH_BASE + HIGH_DIGITS[letter]
                taggable = False
            else:
                if not taggable:
                    raise self.refusal(
                        "Z must follow the letter A to T that ends an integer"
                    )
                tagged.append(self.stack[-1])
                taggable = False
        if number != 0:
            raise self.refusal("compressed proof ends inside an integer")

    def listed_statement(self, label):
        """Return the statement of a label in a compressed proof's list."""
        if label in self.database.assertions:
            return self.database.assertions[label]
        if label not in self.database.active_hypotheses_by_label:
            raise self.refusal(
                f"compressed proof label {label} is not an earlier assertion or"
                " an active hypothesis"
            )
        hypothesis = self.database.active_hypotheses_by_label[label]
        if hypothesis in self.proved.hypotheses:
            raise self.refusal(
                f"compressed proof label {label} is a mandatory hypothesis"
            )
        return hypothesis

    def take_numbered_step(self, number, statements, tagged):
        if number <= len(statements):
            self.take_step(statements[number - 1])
            return
        tag_index = number - len(statements) - 1
        if tag_index >= len(tagged):
            raise self.refusal(
                f"compressed integer {number} refers to a step not yet tagged"
            )
        self.stack.append(tagged[tag_index])

    def take_step(self, statement):
        if isinstance(statement, Hypothesis):
            self.stack.append(statement.expression)
        else:
            self.apply_assertion(statement)

    def apply_assertion(self, assertion):
        first_entry = len(self.stack) - len(assertion.hypotheses)
        if first_entry < 0:
            raise self.refusal(
                f"step {assertion.label} needs {len(assertion.hypotheses)} stack"
                f" entries, the stack has {len(self.stack)}"
            )
        substitution = {}
        for hypothesis, entry in zip(assertion.hypotheses, self.stack[first_entry:]):
            if hypothesis.variable is None:
                # A $e variable has its $f earlier in the mandatory hypotheses,
                # so the substitution already covers it.
                if substitute(hypothesis.expression, substitution) != entry:
                    raise self.refusal(
                        f"step {assertion.label}: stack entry does not match"
                        f" hypothesis {hypothesis.label}"
                    )
            else:
                if entry[0] != hypothesis.expression[0]:
                    raise self.refusal(
                        f"step {assertion.label}: typecode {entry[0]} does not"
                        f" match hypothesis {hypothesis.label}"
                    )
                substitution[hypothesis.variable] = entry[1:]
        for pair in assertion.disjoint:
            self.check_disjoint(assertion, pair, substitution)
        del self.stack[first_entry:]
        self.stack.append(substitute(assertion.expression, substitution))

    def check_disjoint(self, assertion, pair, substitution):
        first, second = sorted(pair)
        # Every symbol on the stack is a constant or is active at this $p: the
        # variables of a referenced assertion are all replaced, so the only
        # variables that remain come from this $p's active hypotheses.
        first_variables = self.database.variables_in(substitution[first])
        second_variables = self.database.variables_in(substitution[second])
        common = first_variables & second_variables
        if common:
            raise self.refusal(
                f"step {assertion.label}: $d {first} {second} is broken by"
                f" shared variable {min(common)}"
            )
        for left, right in itertools.product(first_variables, second_variables):
            if frozenset((left, right)) not in self.active_pairs:
                raise self.refusal(
                    f"step {assertion.label}: $d {first} {second} needs an"
                    f" active $d {left} {right}"
                )


class Database:
    """The state of one verification, advanced statement by statement."""

    def __init__(self):
        # Facts about the whole database, which never go out of scope.
        self.constants = set()
        self.declared_variables = set()  # every symbol ever declared by $v
        self.labels = set()  # every label ever defined
        self.variable_typecodes = {}  # variable to the typecode of its $f
        self.assertions = {}  # label to Assertion
        self.included_files = set()  # (device, inode) of every file read

        # Facts about the active scope, restored when a block ends.
        self.active_variables = set()
        self.active_hypotheses = []  # in order of occurrence
        self.active_hypotheses_by_label = {}
        self.floating_variables = set()  # variables with an active $f
        self.active_disjoint = []  # simple $d statements as frozenset pairs
        self.blocks = []

    def variables_in(self, expression):
        return {symbol for symbol in expression if symbol in self.active_variables}

    # -- Files ---------------------------------------------------------------

    def verify(self, top_name):
        sources = [self.open_source(top_name)]
        while sources:
            source = sources[-1]
            token = next(source, None)
            if token is None:
                # Open case: a block opened in one file and closed in another
                # would pass after textual replacement, but the syntax appendix
                # processes an included file "as a database". An inclusion only
                # happens at depth 0, so each file must end at depth 0.
                if self.blocks:
                    raise Refusal("every ${ must have a matching $} in its file")
                sources.pop()
            elif token == "$[":
                included = self.read_inclusion(source)
                if included is not None:
                    sources.append(included)
            else:
                self.read_statement(token, source)

    def open_source(self, name):
        """Return the tokens of a file, or None for a repeated reference.

        Files are identified by device and inode, not by name: the rule is
        about "a given file", and the permission to treat different strings as
        different files is optional.
        """
        try:
            with open(name, "rb") as stream:
                status = os.fstat(stream.fileno())
                identity = (status.st_dev, status.st_ino)
                if identity in self.included_files:
                    return None
                self.included_files.add(identity)
                data = stream.read()
        except OSError as error:
            raise Refusal(f"cannot read file {name!r}: {error.strerror}") from error
        return tokens_of(decode_source(data, name), name)

    def read_inclusion(self, source):
        if self.blocks:
            raise Refusal("a file inclusion command must be in the outermost block")
        names, _ = read_until(source, ("$]",), "file inclusion command")
        if len(names) != 1:
            raise Refusal("a file inclusion command must hold one file name")
        return self.open_source(names[0])

    # -- Statements ----------------------------------------------------------

    def read_statement(self, token, source):
        if token == "${":
            self.blocks.append(
                Block(len(self.active_hypotheses), len(self.active_disjoint), [])
            )
        elif token == "$}":
            self.close_block()
        elif token == "$c":
            self.declare_constants(read_statement_body(source, "$c statement"))
        elif token == "$v":
            self.declare_variables(read_statement_body(source, "$v statement"))
        elif token == "$d":
            self.add_disjoint(read_statement_body(source, "$d statement"))
        elif token in KEYWORDS:
            raise Refusal(f"{token} may not begin a statement")
        else:
            self.read_labelled_statement(token, source)

    def close_block(self):
        if not self.blocks:
            raise Refusal("$} without a matching ${")
        block = self.blocks.pop()
        for hypothesis in self.active_hypotheses[block.hypothesis_count :]:
            del self.active_hypotheses_by_label[hypothesis.label]
            self.floating_variables.discard(hypothesis.variable)
        del self.active_hypotheses[block.hypothesis_count :]
        del self.active_disjoint[block.disjoint_count :]
        self.active_variables.difference_update(block.variables)

    def check_declared_symbols(self, keyword, symbols):
        if not symbols:
            raise Refusal(f"a {keyword} statement needs at least one math symbol")
        if len(set(symbols)) != len(symbols):
            raise Refusal(f"a math symbol occurs twice in a {keyword} statement")
        for symbol in symbols:
            if symbol in self.labels:
                raise Refusal(f"math symbol {symbol} matches a label")

    def declare_constants(self, symbols):
        if self.blocks:
            raise Refusal("a constant must be declared in the outermost block")
        self.check_declared_symbols("$c", symbols)
        for symbol in symbols:
            if symbol in self.constants:
                raise Refusal(f"constant {symbol} is declared a second time")
            if symbol in self.declared_variables:
                raise Refusal(f"variable {symbol} may not be declared as a constant")
        self.constants.update(symbols)

    def declare_variables(self, symbols):
        self.check_declared_symbols("$v", symbols)
        for symbol in symbols:
            if symbol in self.constants:
                raise Refusal(f"constant {symbol} may not be declared as a variable")
            if symbol in self.active_variables:
                raise Refusal(f"active variable {symbol} is declared a second time")
        self.active_variables.update(symbols)
        self.declared_variables.update(symbols)
        if self.blocks:
            self.blocks[-1].variables.extend(symbols)

    def add_disjoint(self, symbols):
        if len(symbols) < 2:
            raise Refusal("a $d statement needs at least two variables")
        if len(set(symbols)) != len(symbols):
            raise Refusal("the variables of a $d statement must all be different")
        for symbol in symbols:
            if symbol not in self.active_variables:
                raise Refusal(f"$d symbol {symbol} is not an active variable")
        self.active_disjoint.extend(
            frozenset(pair) for pair in itertools.combinations(symbols, 2)
        )

    def read_labelled_statement(self, label, source):
        keyword = next(source, None)
        if not LABEL.fullmatch(label):
            raise Refusal(f"token {label} is not a label")
        if keyword not in LABELLED_KEYWORDS:
            raise Refusal(f"label {label} must be followed by $f, $e, $a or $p")
        self.define_label(label)
        if keyword == "$p":
            self.add_provable(label, source)
            return
        body = read_statement_body(source, label)
        if keyword == "$f":
            self.add_floating(label, body)
        elif keyword == "$e":
            self.add_hypothesis(
                Hypothesis(label, self.checked_expression(label, body), None)
            )
        else:
            self.assertions[label] = self.assertion_frame(
                label, self.checked_expression(label, body)
            )

    def define_label(self, label):
        if label in self.labels:
            raise Refusal(f"label {label} is not unique")
        if label in self.constants or label in self.declared_variables:
            raise Refusal(f"label {label} matches a math symbol")
        self.labels.add(label)

    def add_hypothesis(self, hypothesis):
        self.active_hypotheses.append(hypothesis)
        self.active_hypotheses_by_label[hypothesis.label] = hypothesis

    def add_floating(self, label, body):
        if len(body) != 2:
            raise Refusal(f"{label}: a $f statement holds a typecode and a variable")
        typecode, variable = body
        if typecode not in self.constants:
            raise Refusal(f"{label}: typecode {typecode} is not an active constant")
        if variable not in self.active_variables:
            raise Refusal(f"{label}: {variable} is not an active variable")
        if variable in self.floating_variables:
            raise Refusal(f"{label}: variable {variable} already has an active $f")
        # The prose ties the typecode to "a given label", but labels are unique
        # and its example is one variable with two types, so the rule is read
        # as one typecode per variable across the whole database.
        declared_typecode = self.variable_typecodes.setdefault(variable, typecode)
        if declared_typecode != typecode:
            raise Refusal(
                f"{label}: variable {variable} already has typecode"
                f" {declared_typecode}"
            )
        self.floating_variables.add(variable)
        self.add_hypothesis(Hypothesis(label, (typecode, variable), variable))

    def checked_expression(self, label, symbols):
        """Check the typecode and symbols of a $e, $a or $p statement."""
        if not symbols:
            raise Refusal(f"{label}: the statement needs a typecode")
        if symbols[0] not in self.constants:
            raise Refusal(f"{label}: typecode {symbols[0]} is not an active constant")
        for symbol in symbols[1:]:
            if symbol in self.constants:
                continue
            if symbol not in self.active_variables:
                raise Refusal(f"{label}: math symbol {symbol} is not active")
            if symbol not in self.floating_variables:
                raise Refusal(f"{label}: variable {symbol} has no active $f")
        return tuple(symbols)

    def assertion_frame(self, label, expression):
        mandatory_variables = self.variables_in(expression)
        for hypothesis in self.active_hypotheses:
            if hypothesis.variable is None:
                mandatory_variables |= self.variables_in(hypothesis.expression)
        hypotheses = tuple(
            hypothesis
            for hypothesis in self.active_hypotheses
            if hypothesis.variable is None
            or hypothesis.variable in mandatory_variables
        )
        disjoint = frozenset(
            pair for pair in self.active_disjoint if pair <= mandatory_variables
        )
        return Assertion(label, expression, hypotheses, disjoint)

    def add_provable(self, label, source):
        symbols, terminator = read_until(source, ("$=", END), label)
        if terminator != "$=":
            raise Refusal(f"{label}: a $p statement needs $= and a proof")
        proved = self.assertion_frame(label, self.checked_expression(label, symbols))
        ProofCheck(self, proved).run(read_statement_body(source, label))
        # Added only now, so that a proof cannot refer to its own statement.
        self.assertions[label] = proved


def main(arguments):
    if len(arguments) != 2:
        print("usage: python3 -I verify.py FILE.mm", file=sys.stderr)
        return 2
    try:
        Database().verify(arguments[1])
    except Refusal as refusal:
        print(f"refused: {refusal}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
