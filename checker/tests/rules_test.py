#!/usr/bin/env python3
"""One small database per rule of the Metamath specification, for verify.py.

Usage: python3 -I rules_test.py VERIFY_PY

A refusal case names a fragment of the expected message, so that a database
refused for the wrong rule counts as a failure. Accept cases cover what the
specification permits and a too-strict verifier would reject.
"""

import pathlib
import subprocess
import sys
import tempfile

PRELUDE = b"""
$c |- wff set ( ) -> $.
$v p q r s x y $.
wp $f wff p $.
wq $f wff q $.
wr $f wff r $.
ws $f wff s $.
vx $f set x $.
vy $f set y $.
wi $a wff ( p -> q ) $.
"""

DV_AXIOM = b"${ $d p q $. ax-dv $a |- ( p -> q ) $. $}\n"
DROP_AXIOM = b"${ drop.1 $e wff p $. drop $a wff q $. $}\n"


def p(body):
    return PRELUDE + body


# name, files or body, expected refusal fragment (None for accept)
CASES = [
    # -- Characters ----------------------------------------------------------
    ("nul in comment", b"$( a\x00b $)\n", "byte 0x00"),
    ("del in comment", b"$( a\x7fb $)\n", "byte 0x7f"),
    ("high byte in comment", b"$( caf\xc3\xa9 $)\n", "byte 0xc3"),
    ("vertical tab between tokens", b"$c a\x0bb $.\n", "byte 0x0b"),
    ("file separator is not white space", b"$c a\x1cb $.\n", "byte 0x1c"),
    ("bom", b"\xef\xbb\xbf$c a $.\n", "byte 0xef"),
    ("all five white space characters", b"$c\ta\rb\nc\fd $.\n", None),
    # -- Tokens --------------------------------------------------------------
    ("empty file", b"", None),
    ("white space only", b" \n\t\r\f", None),
    ("unknown keyword", b"$x\n", "not a keyword"),
    ("lone dollar", b"$c $ $.\n", "not a keyword"),
    ("dollar inside symbol", b"$c a$b $.\n", "not a keyword"),
    ("keyword glued to symbol", b"$c a$. \n", "not a keyword"),
    ("keyword glued to next", b"$c a $.$c b $.\n", "not a keyword"),
    ("last $. at bare end of file", b"$c a $.", None),
    # -- Comments ------------------------------------------------------------
    ("comment with keywords", b"$( $[ $] ${ $a $. $= $)\n$c a $.\n", None),
    ("comment open glued", b"$(x $)\n", "not a keyword"),
    ("comment close glued left", b"$( x$) \n", "may not contain"),
    ("comment close glued right", b"$( x $)y\n", "may not contain"),
    ("nested comment", b"$( $( $) $)\n", "may not contain"),
    ("sequence $( inside a word", b"$( a$(b $)\n", "may not contain"),
    ("sequence $) inside a word", b"$( a$)b $)\n", "may not contain"),
    ("unterminated comment", b"$( never ends\n", "without a matching $)"),
    ("close without open", b"$)\n", "without a matching $("),
    ("comment close at bare eof", b"$( x $)", "followed by white space"),
    ("comment between label and keyword", p(b"a $( c $) $a wff p $.\n"), None),
    ("comment inside statement", p(b"a $a wff $( c $) p $.\n"), None),
    (
        "comment inside proof",
        p(b"a $p wff p $= $( c $) wp $( d $) $.\n"),
        None,
    ),
    # -- Blocks --------------------------------------------------------------
    ("unmatched close", b"$}\n", "without a matching ${"),
    ("unclosed block", b"${\n", "matching $}"),
    ("empty nested blocks", b"${ ${ $} $}\n", None),
    ("label before block", b"a ${ $}\n", "must be followed by"),
    # -- Declarations --------------------------------------------------------
    ("empty $c", b"$c $.\n", "at least one"),
    ("empty $v", b"$v $.\n", "at least one"),
    ("repeat in $c", b"$c a a $.\n", "occurs twice"),
    ("repeat in $v", b"$v a a $.\n", "occurs twice"),
    ("$c in a block", b"${ $c a $. $}\n", "outermost block"),
    ("constant declared twice", b"$c a $.\n$c a $.\n", "second time"),
    ("constant as variable", b"$c a $.\n$v a $.\n", "as a variable"),
    ("constant as variable in block", b"$c a $.\n${ $v a $. $}\n", "as a variable"),
    ("active variable as constant", b"$v a $.\n$c a $.\n", "as a constant"),
    ("inactive variable as constant", b"${ $v a $. $}\n$c a $.\n", "as a constant"),
    ("variable declared twice", b"$v a $.\n$v a $.\n", "second time"),
    ("variable redeclared in block", b"$v a $.\n${ $v a $. $}\n", "second time"),
    ("variable after it went inactive", b"${ $v a $. $}\n${ $v a $. $}\n$v a $.\n", None),
    ("statement ends at eof", b"$c a b\n", "ends inside a statement"),
    ("keyword in a declaration", b"$c a $a b $.\n", "may not occur here"),
    ("unterminated by next statement", b"$c a\n$v b $.\n", "may not occur here"),
    ("stray terminator", b"$.\n", "may not begin"),
    ("stray $=", b"$=\n", "may not begin"),
    ("unlabelled $a", b"$a wff $.\n", "may not begin"),
    ("unlabelled $f", p(b"$f wff p $.\n"), "may not begin"),
    # -- $f ------------------------------------------------------------------
    ("$f one symbol", p(b"a $f wff $.\n"), "typecode and a variable"),
    ("$f three symbols", p(b"a $f wff p q $.\n"), "typecode and a variable"),
    ("$f no symbols", p(b"a $f $.\n"), "typecode and a variable"),
    ("$f typecode is variable", p(b"$v t $.\na $f p t $.\n"), "not an active constant"),
    ("$f typecode undeclared", p(b"$v t $.\na $f nope t $.\n"), "not an active constant"),
    ("$f on a constant", p(b"a $f wff -> $.\n"), "not an active variable"),
    ("$f on undeclared", p(b"a $f wff t $.\n"), "not an active variable"),
    ("$f on inactive", p(b"${ $v t $. $}\na $f wff t $.\n"), "not an active variable"),
    ("second active $f", p(b"a $f wff p $.\n"), "already has an active $f"),
    (
        "second active $f in a block",
        p(b"${ a $f wff p $. $}\n"),
        "already has an active $f",
    ),
    (
        "typecode conflict across scopes",
        b"$c wff class $.\n$v P $.\n${ a $f wff P $. $}\n${ b $f class P $. $}\n",
        "already has typecode",
    ),
    (
        "typecode conflict across redeclaration",
        b"$c wff class $.\n${ $v P $. a $f wff P $. $}\n${ $v P $. b $f class P $. $}\n",
        "already has typecode",
    ),
    (
        "same typecode across scopes",
        b"$c wff $.\n$v P $.\n${ a $f wff P $. $}\n${ b $f wff P $. $}\n",
        None,
    ),
    # -- $e and $a -----------------------------------------------------------
    ("$e empty", p(b"a $e $.\n"), "needs a typecode"),
    ("$a empty", p(b"a $a $.\n"), "needs a typecode"),
    ("$e only typecode", p(b"a $e wff $.\n"), None),
    ("$a only typecode", p(b"a $a wff $.\n"), None),
    ("$e typecode variable", p(b"a $e p $.\n"), "not an active constant"),
    ("$a typecode variable", p(b"a $a p -> $.\n"), "not an active constant"),
    ("$a typecode undeclared", p(b"a $a nope p $.\n"), "not an active constant"),
    ("$a undeclared symbol", p(b"a $a wff nope $.\n"), "is not active"),
    ("$e inactive variable", p(b"${ $v t $. $}\na $e wff t $.\n"), "is not active"),
    ("$a variable with no $f", p(b"$v t $.\na $a wff t $.\n"), "no active $f"),
    ("$e variable with no $f", p(b"$v t $.\na $e wff t $.\n"), "no active $f"),
    ("$p variable with no $f", p(b"$v t $.\na $p wff t $= wp $.\n"), "no active $f"),
    (
        "$a variable whose $f has gone",
        p(b"$v t $.\n${ wt $f wff t $. $}\na $a wff t $.\n"),
        "no active $f",
    ),
    ("$= in $a", p(b"a $a wff p $= wp $.\n"), "may not occur here"),
    ("$= in $e", p(b"a $e wff p $= wp $.\n"), "may not occur here"),
    ("$p with no $=", p(b"a $p wff p $.\n"), "needs $="),
    ("$= twice", p(b"a $p wff p $= wp $= wp $.\n"), "may not occur here"),
    # -- $d ------------------------------------------------------------------
    ("$d empty", p(b"$d $.\n"), "at least two"),
    ("$d one variable", p(b"$d p $.\n"), "at least two"),
    ("$d same variable", p(b"$d p p $.\n"), "all be different"),
    ("compound $d repeat", p(b"$d p q p $.\n"), "all be different"),
    ("$d constant", p(b"$d p -> $.\n"), "not an active variable"),
    ("$d undeclared", p(b"$d p nope $.\n"), "not an active variable"),
    ("$d inactive", p(b"${ $v t $. $}\n$d p t $.\n"), "not an active variable"),
    ("$d variable with no $f", p(b"$v t $.\n$d p t $.\n"), None),
    ("label before $d", p(b"a $d p q $.\n"), "must be followed by"),
    # -- Labels --------------------------------------------------------------
    ("label characters", p(b"a-b_c.0 $a wff p $.\n"), None),
    ("label bad character", p(b"a+b $a wff p $.\n"), "not a label"),
    ("math symbol as a statement", p(b"-> $a wff p $.\n"), "not a label"),
    ("two labels", p(b"a b $a wff p $.\n"), "must be followed by"),
    ("label then $c", b"a $c b $.\n", "must be followed by"),
    ("label then terminator", b"a $.\n", "must be followed by"),
    ("label at eof", b"a\n", "must be followed by"),
    ("duplicate label", p(b"a $a wff p $.\na $a wff q $.\n"), "not unique"),
    (
        "duplicate of inactive label",
        p(b"${ a $e wff p $. $}\na $a wff q $.\n"),
        "not unique",
    ),
    ("label is a constant", p(b"$c a $.\na $a wff p $.\n"), "matches a math symbol"),
    ("label is a variable", p(b"$v a $.\na $a wff p $.\n"), "matches a math symbol"),
    (
        "label is an inactive variable",
        p(b"${ $v a $. $}\na $a wff p $.\n"),
        "matches a math symbol",
    ),
    ("constant is a label", p(b"a $a wff p $.\n$c a $.\n"), "matches a label"),
    ("variable is a label", p(b"a $a wff p $.\n$v a $.\n"), "matches a label"),
    (
        "variable is an inactive label",
        p(b"${ a $e wff p $. $}\n$v a $.\n"),
        "matches a label",
    ),
    # -- Normal proofs -------------------------------------------------------
    ("proof ok", p(b"a $p wff ( p -> q ) $= wp wq wi $.\n"), None),
    ("? in proof", p(b"a $p wff ( p -> q ) $= wp wq wi ? $.\n"), "incomplete"),
    ("only ?", p(b"a $p wff p $= ? $.\n"), "incomplete"),
    ("empty proof", p(b"a $p wff p $= $.\n"), "one stack entry, not 0"),
    ("self reference", p(b"a $p wff p $= a $.\n"), "not an active hypothesis"),
    (
        "forward reference",
        p(b"a $p wff p $= b $.\nb $a wff p $.\n"),
        "not an active hypothesis",
    ),
    ("unknown label", p(b"a $p wff p $= nope $.\n"), "not an active hypothesis"),
    ("math symbol in proof", p(b"a $p wff p $= -> $.\n"), "not an active hypothesis"),
    (
        "inactive hypothesis",
        p(b"${ e $e wff p $. $}\na $p wff p $= e $.\n"),
        "not an active hypothesis",
    ),
    ("stack underflow", p(b"a $p wff p $= wp wi $.\n"), "stack entries"),
    ("two left on stack", p(b"a $p wff p $= wp wp $.\n"), "not 2"),
    ("wrong result", p(b"a $p wff q $= wp $.\n"), "does not prove"),
    ("wrong typecode result", p(b"a $p |- p $= wp $.\n"), "does not prove"),
    (
        "$f typecode mismatch in step",
        p(b"a $p wff ( x -> q ) $= vx wq wi $.\n"),
        "typecode set does not match",
    ),
    (
        "$e mismatch in step",
        p(b"${ mp.1 $e |- p $. mp $a |- q $. $}\nth.1 $e |- q $.\na $p |- r $= wp wr th.1 mp $.\n"),
        "does not match hypothesis mp.1",
    ),
    (
        "$e match in step",
        p(b"${ mp.1 $e |- p $. mp $a |- q $. $}\nth.1 $e |- q $.\na $p |- r $= wq wr th.1 mp $.\n"),
        None,
    ),
    (
        "$a in closed block stays active",
        p(b"${ $v t $. wt $f wff t $. b $a wff t $. $}\na $p wff p $= wp b $.\n"),
        None,
    ),
    (
        "variable of the assertion inactive at the proof",
        p(b"${ $v t $. wt $f wff t $. b $a wff t $. $}\n${ $v t $. wu $f wff t $. a $p wff t $= wu b $. $}\n"),
        None,
    ),
    (
        "mandatory order is $f order not expression order",
        p(b"wj $a wff ( q -> p ) $.\na $p wff ( r -> s ) $= ws wr wj $.\n"),
        None,
    ),
    (
        "mandatory order wrong way round",
        p(b"wj $a wff ( q -> p ) $.\na $p wff ( r -> s ) $= wr ws wj $.\n"),
        "does not prove",
    ),
    (
        "interleaved mandatory hypotheses",
        p(
            b"$v t $.\n${ e1 $e |- p $. wt $f wff t $. ax $a |- ( p -> t ) $. $}\n"
            b"${ wu $f wff t $. a.1 $e |- r $. a $p |- ( r -> s ) $= wr a.1 ws ax $. $}\n"
        ),
        None,
    ),
    (
        "interleaved hypotheses in the wrong order",
        p(
            b"$v t $.\n${ e1 $e |- p $. wt $f wff t $. ax $a |- ( p -> t ) $. $}\n"
            b"${ wu $f wff t $. a.1 $e |- r $. a $p |- ( r -> s ) $= wr ws a.1 ax $. $}\n"
        ),
        "does not match hypothesis e1",
    ),
    ("empty substitution", p(b"we $a wff $.\na $p wff ( -> ) $= we we wi $.\n"), None),
    (
        "variable mapped to itself, simultaneously",
        p(b"a $p wff ( ( p -> q ) -> p ) $= wp wq wi wp wi $.\n"),
        None,
    ),
    (
        "swap needs simultaneous substitution",
        p(b"a $p wff ( q -> p ) $= wq wp wi $.\n"),
        None,
    ),
    (
        "dummy variable hypothesis in a proof",
        p(DROP_AXIOM + b"a $p wff r $= ws wr ws drop $.\n"),
        None,
    ),
    (
        "an active $e is mandatory even when the assertion ignores it",
        p(b"${ e $e wff s $. b $a wff p $. $}\na $p wff r $= wr b $.\n"),
        "stack entries",
    ),
    (
        "an active $e brings its variable with it",
        p(b"${ e $e wff s $. b $a wff p $. $}\na $p wff r $= wr ws ws b $.\n"),
        None,
    ),
    # -- Disjoint variables --------------------------------------------------
    ("dv shared variable", p(DV_AXIOM + b"a $p |- ( r -> r ) $= wr wr ax-dv $.\n"), "shared variable r"),
    ("dv missing", p(DV_AXIOM + b"a $p |- ( r -> s ) $= wr ws ax-dv $.\n"), "needs an active $d"),
    ("dv present", p(DV_AXIOM + b"${ $d r s $. a $p |- ( r -> s ) $= wr ws ax-dv $. $}\n"), None),
    ("dv from a closed block", p(DV_AXIOM + b"${ $d r s $. $}\na $p |- ( r -> s ) $= wr ws ax-dv $.\n"), "needs an active $d"),
    ("dv $d after the $p", p(DV_AXIOM + b"${ a $p |- ( r -> s ) $= wr ws ax-dv $. $d r s $. $}\n"), "needs an active $d"),
    (
        "dv constants only",
        p(b"$c T $.\nwT $a wff T $.\n" + DV_AXIOM + b"a $p |- ( T -> T ) $= wT wT ax-dv $.\n"),
        None,
    ),
    ("dv empty expressions", p(b"we $a wff $.\n" + DV_AXIOM + b"a $p |- ( -> ) $= we we ax-dv $.\n"), None),
    (
        "dv every cross pair needed",
        p(DV_AXIOM + b"$v t $.\nwt $f wff t $.\n${ $d r t $. a $p |- ( ( r -> s ) -> t ) $= wr ws wi wt ax-dv $. $}\n"),
        "$d s t",
    ),
    (
        "dv cross pairs present, same-side pair not needed",
        p(DV_AXIOM + b"$v t $.\nwt $f wff t $.\n${ $d r t $. $d s t $. a $p |- ( ( r -> s ) -> t ) $= wr ws wi wt ax-dv $. $}\n"),
        None,
    ),
    (
        "dv from a compound $d",
        p(DV_AXIOM + b"$v t $.\nwt $f wff t $.\n${ $d r s t $. a $p |- ( ( r -> s ) -> t ) $= wr ws wi wt ax-dv $. $}\n"),
        None,
    ),
    (
        "dv with non-mandatory variable is not enforced",
        p(b"${ $d p q $. ax $a |- p $. $}\n${ a $p |- r $= wr ax $. $}\n"),
        None,
    ),
    (
        "dv after the assertion is not mandatory for it",
        p(b"${ ax $a |- ( p -> q ) $. $d p q $. a $p |- ( r -> r ) $= wr wr ax $. $}\n"),
        None,
    ),
    (
        "dv in $e variable is mandatory",
        p(
            b"${ $d p q $. ax.1 $e |- q $. ax $a |- p $. $}\n"
            b"a.1 $e |- r $.\na $p |- r $= wr wr a.1 ax $.\n"
        ),
        "shared variable r",
    ),
    # -- Compressed proofs ---------------------------------------------------
    ("compressed ok", p(b"a $p wff ( p -> q ) $= ( wi ) ABC $.\n"), None),
    ("compressed split letters", p(b"a $p wff ( p -> q ) $= ( wi ) A\nB C $.\n"), None),
    ("compressed empty label list", p(b"a $p wff p $= ( ) A $.\n"), None),
    (
        "compressed tag and reference",
        p(b"a $p wff ( ( p -> p ) -> ( p -> p ) ) $= ( wi ) AABZCB $.\n"),
        None,
    ),
    (
        "compressed tag split from its step",
        p(b"a $p wff ( ( p -> p ) -> ( p -> p ) ) $= ( wi ) AAB Z CB $.\n"),
        None,
    ),
    ("compressed unused tag", p(b"a $p wff p $= ( ) AZ $.\n"), None),
    ("compressed unused non-mandatory", p(b"a $p wff p $= ( wq wi ) A $.\n"), None),
    (
        "compressed used non-mandatory",
        p(DROP_AXIOM + b"a $p wff r $= ( ws drop ) BABC $.\n"),
        None,
    ),
    ("compressed repeated list label", p(b"a $p wff ( p -> q ) $= ( wi wi ) ABD $.\n"), None),
    ("compressed mandatory $f in list", p(b"a $p wff p $= ( wp ) B $.\n"), "is a mandatory"),
    (
        "compressed mandatory $e in list",
        p(b"${ e $e wff q $. a $p wff q $= ( e ) C $. $}\n"),
        "is a mandatory",
    ),
    ("compressed self in list", p(b"a $p wff p $= ( a ) A $.\n"), "not an earlier assertion"),
    (
        "compressed later label in list",
        p(b"a $p wff p $= ( b ) A $.\nb $a wff p $.\n"),
        "not an earlier assertion",
    ),
    ("compressed unknown label", p(b"a $p wff p $= ( nope ) A $.\n"), "not an earlier assertion"),
    (
        "compressed inactive hypothesis in list",
        p(b"${ e $e wff p $. $}\na $p wff p $= ( e ) A $.\n"),
        "not an earlier assertion",
    ),
    ("compressed ?", p(b"a $p wff p $= ( ) ? $.\n"), "incomplete"),
    ("compressed ? glued", p(b"a $p wff p $= ( ) A? $.\n"), "incomplete"),
    ("compressed ? in list", p(b"a $p wff p $= ( ? ) A $.\n"), "not an earlier assertion"),
    ("compressed no letters", p(b"a $p wff p $= ( ) $.\n"), "letters A to Z"),
    ("compressed no close", p(b"a $p wff p $= ( wi A $.\n"), "closing parenthesis"),
    ("compressed second close", p(b"a $p wff p $= ( ) ) A $.\n"), "letters A to Z"),
    ("compressed lower case", p(b"a $p wff p $= ( ) a $.\n"), "letters A to Z"),
    ("compressed digit", p(b"a $p wff p $= ( ) A1 $.\n"), "letters A to Z"),
    ("compressed open glued", p(b"a $p wff p $= (wi ) A $.\n"), "not an active hypothesis"),
    ("compressed close glued left", p(b"a $p wff p $= ( wi) A $.\n"), "closing parenthesis"),
    ("compressed close glued right", p(b"a $p wff p $= ( wi )A $.\n"), "closing parenthesis"),
    ("compressed Z first", p(b"a $p wff p $= ( ) ZA $.\n"), "Z must follow"),
    ("compressed Z twice", p(b"a $p wff p $= ( ) AZZ $.\n"), "Z must follow"),
    ("compressed Z twice split", p(b"a $p wff p $= ( ) AZ Z $.\n"), "Z must follow"),
    ("compressed Z after U", p(b"a $p wff p $= ( ) UZA $.\n"), "Z must follow"),
    ("compressed ends in U", p(b"a $p wff p $= ( ) AU $.\n"), "inside an integer"),
    ("compressed ends in Y", p(b"a $p wff p $= ( ) AUY $.\n"), "inside an integer"),
    ("compressed integer too large", p(b"a $p wff p $= ( ) B $.\n"), "not yet tagged"),
    ("compressed vast integer", p(b"a $p wff p $= ( ) " + b"Y" * 400 + b"T $.\n"), "not yet tagged"),
    (
        "compressed reference before its tag",
        p(b"a $p wff ( p -> p ) $= ( wi ) CAABZ $.\n"),
        "not yet tagged",
    ),
    (
        "compressed second tag not yet made",
        p(b"a $p wff p $= ( ) AZD $.\n"),
        "not yet tagged",
    ),
    ("compressed stack underflow", p(b"a $p wff p $= ( wi ) B $.\n"), "stack entries"),
    ("compressed wrong result", p(b"a $p wff q $= ( wp ) B $.\n"), "does not prove"),
    # -- Inclusion -----------------------------------------------------------
    ("include", {"main.mm": b"$[ a.mm $]\n$c b $.\n", "a.mm": b"$c a $.\n"}, None),
    (
        "include at start of file with bare statement end",
        {"main.mm": b"$[ a.mm $]\n", "a.mm": b"$c a $."},
        None,
    ),
    ("include twice", {"main.mm": b"$[ a.mm $] $[ a.mm $]\n", "a.mm": b"$c a $.\n"}, None),
    (
        "include later from another file",
        {"main.mm": b"$[ a.mm $] $[ b.mm $]\n", "a.mm": b"$c a $.\n", "b.mm": b"$[ a.mm $]\n$c b $.\n"},
        None,
    ),
    ("include self", {"main.mm": b"$[ a.mm $]\n", "a.mm": b"$c a $.\n$[ a.mm $]\n"}, None),
    ("include top level", {"main.mm": b"$[ a.mm $]\n", "a.mm": b"$c a $.\n$[ main.mm $]\n"}, None),
    ("top level includes itself", {"main.mm": b"$c a $.\n$[ main.mm $]\n"}, None),
    (
        "include another spelling of the same file",
        {"main.mm": b"$[ a.mm $] $[ ./a.mm $]\n", "a.mm": b"$c a $.\n"},
        None,
    ),
    ("include missing file", b"$[ nope.mm $]\n", "cannot read"),
    ("include directory", b"$[ . $]\n", "cannot read"),
    ("include no name", b"$[ $]\n", "one file name"),
    ("include two names", b"$[ a b $]\n", "one file name"),
    ("include dollar in name", b"$[ a$b $]\n", "not a keyword"),
    ("include never closed", b"$[ a.mm\n", "ends inside a statement"),
    ("include closed by keyword", b"$[ a.mm $.\n", "may not occur here"),
    ("stray include close", b"$]\n", "may not begin"),
    ("include in a block", {"main.mm": b"${ $[ a.mm $] $}\n", "a.mm": b"\n"}, "outermost block"),
    (
        "ignored include in a block",
        {"main.mm": b"$[ a.mm $]\n${ $[ a.mm $] $}\n", "a.mm": b"\n"},
        "outermost block",
    ),
    (
        "self include in a block of the included file",
        {"main.mm": b"$[ a.mm $]\n", "a.mm": b"${ $[ a.mm $] $}\n"},
        "outermost block",
    ),
    ("include after a label", {"main.mm": b"x $[ a.mm $] $a wff $.\n", "a.mm": b"\n"}, "must be followed by"),
    (
        "include inside a statement",
        {"main.mm": b"$c wff $.\nx $a wff $[ a.mm $] $.\n", "a.mm": b"\n"},
        "may not occur here",
    ),
    ("include inside $c", {"main.mm": b"$c a $[ a.mm $] $.\n", "a.mm": b"\n"}, "may not occur here"),
    ("include in a comment is ignored", b"$( $[ nope.mm $] $)\n", None),
    (
        "included file with open comment",
        {"main.mm": b"$[ a.mm $]\n$)\n", "a.mm": b"$( open\n"},
        "without a matching $)",
    ),
    (
        "included file with open include",
        {"main.mm": b"$[ a.mm $]\nb.mm $]\n", "a.mm": b"$[ \n", "b.mm": b"\n"},
        "ends inside a statement",
    ),
    (
        "included file with open statement",
        {"main.mm": b"$[ a.mm $]\nb $.\n", "a.mm": b"$c a\n"},
        "ends inside a statement",
    ),
    (
        "included file with a label only",
        {"main.mm": b"$c wff $.\n$[ a.mm $]\n$a wff $.\n", "a.mm": b"x\n"},
        "must be followed by",
    ),
    (
        "included file with open block",
        {"main.mm": b"$[ a.mm $]\n$}\n", "a.mm": b"${\n"},
        "matching $}",
    ),
    (
        "included file closing an outer block",
        {"main.mm": b"${\n$[ a.mm $]\n", "a.mm": b"$}\n"},
        "outermost block",
    ),
    (
        "included file breaks a byte rule",
        {"main.mm": b"$[ a.mm $]\n", "a.mm": b"$( \xff $)\n"},
        "byte 0xff",
    ),
    (
        "included file ends in bare close",
        {"main.mm": b"$[ a.mm $]\n", "a.mm": b"$( x $)"},
        "followed by white space",
    ),
    (
        "ignored second reference to a file is not reread",
        {"main.mm": b"$[ a.mm $] $[ a.mm $]\n$c b $.\n", "a.mm": b"$c a $.\n"},
        None,
    ),
    ("include close at bare eof", {"main.mm": b"$[ a.mm $]", "a.mm": b"\n"}, "followed by white space"),
    (
        "comment inside an include command",
        {"main.mm": b"$[ $( c $) a.mm $]\n", "a.mm": b"\n"},
        "inside a file inclusion",
    ),
    (
        "declarations carry through an inclusion",
        {
            "main.mm": b"$[ a.mm $]\nb $a wff p $.\n",
            "a.mm": b"$c wff $.\n$v p $.\nwp $f wff p $.\n",
        },
        None,
    ),
    (
        "duplicate label across files",
        {"main.mm": b"$c wff $.\nx $a wff $.\n$[ a.mm $]\n", "a.mm": b"x $a wff $.\n"},
        "not unique",
    ),
]


def large_list_case(number_of_labels, letters):
    """A compressed proof whose result pins one integer to one list position."""
    constants = " ".join(f"c{i}" for i in range(1, number_of_labels + 1))
    axioms = "\n".join(f"a{i} $a |- c{i} $." for i in range(1, number_of_labels + 1))
    labels = " ".join(f"a{i}" for i in range(1, number_of_labels + 1))
    text = (
        f"$c |- {constants} $.\n{axioms}\n"
        f"th $p |- c{number_of_labels} $= ( {labels} ) {letters} $.\n"
    )
    return text.encode("ascii")


# The documented boundaries of the integer encoding. A decoder that is off by
# one lands on a different axiom, so the proof no longer proves the statement.
for number, letters in [
    (1, "A"),
    (20, "T"),
    (21, "UA"),
    (22, "UB"),
    (40, "UT"),
    (41, "VA"),
    (120, "YT"),
    (121, "UUA"),
    (620, "YYT"),
    (621, "UUUA"),
]:
    CASES.append((f"integer {number} is {letters}", large_list_case(number, letters), None))
CASES.append(("integer 21 is not UB", large_list_case(21, "UB"), "not yet tagged"))
CASES.append(("integer 20 is not UA", large_list_case(21, "T"), "does not prove"))


# Each of these failed to notice when one check was removed from mmcheck.
PREFIX_AXIOM = b"${ ax.1 $e |- p -> $. ax $a |- p $. $}\n"
CASES += [
    ("dollar in a variable", b"$v a$b $.\n", ""),
    ("$d on a hypothesis label", p(b"$d wp x $.\n"), ""),
    ("$f on a hypothesis label", p(b"bad $f wff wq $.\n"), ""),
    ("$f closed by the end of a block", p(b"$v t $.\n${ a $f wff t $} $}\n"), "may not occur here"),
    (
        "stack entry is a proper prefix of the hypothesis",
        p(PREFIX_AXIOM + b"${ th.1 $e |- q $. th $p |- q $= wq th.1 ax $. $}\n"),
        "",
    ),
    (
        "hypothesis is a proper prefix of the stack entry",
        p(
            b"${ ax.1 $e |- p $. ax $a |- p $. $}\n"
            b"${ th.1 $e |- q -> $. th $p |- q $= wq th.1 ax $. $}\n"
        ),
        "",
    ),
    ("proof step that names nothing", p(b"th $p wff p $= wp nosuch $.\n"), ""),
    ("proof step that names the theorem", p(b"th $p wff p $= wp th $.\n"), ""),
    ("proof step that names a constant", p(b"th $p wff p $= wp wff $.\n"), ""),
    (
        "tag left over from the previous proof",
        p(b"a $p wff p $= ( ) AZ $.\nb $p wff p $= ( ) B $.\n"),
        "",
    ),
    ("theorem is a proper prefix of what was proved", p(b"th $p wff ( p $= wp wq wi $.\n"), ""),
    ("dollar in an included name", {"main.mm": b"$[ a$b.mm $]\n", "a$b.mm": b""}, ""),
    ("$[ closed by something else", {"main.mm": b"$[ a.mm nope\n", "a.mm": b""}, ""),
]


def run_case(verifier, root, files):
    if not isinstance(files, dict):
        files = {"main.mm": files}
    with tempfile.TemporaryDirectory(dir=root) as directory:
        for name, content in files.items():
            pathlib.Path(directory, name).write_bytes(content)
        return subprocess.run(
            [sys.executable, "-I", verifier, "main.mm"],
            cwd=directory,
            capture_output=True,
            text=True,
            timeout=60,
        )


def check(name, files, expected, verifier, root):
    result = run_case(verifier, root, files)
    message = result.stderr.strip()
    if expected is None:
        return None if result.returncode == 0 else f"exit {result.returncode}: {message}"
    if result.returncode != 1:
        return f"exit {result.returncode}, expected refusal: {message}"
    if "\n" in message:
        return f"more than one line on stderr: {message}"
    if expected not in message:
        return f"refused for another reason: {message}"
    return None


def main():
    # Each case runs from its own directory, so a relative path is made absolute.
    verifier = pathlib.Path(sys.argv[1]).resolve()
    root = verifier.parent
    failures = 0
    for name, files, expected in CASES:
        problem = check(name, files, expected, verifier, root)
        if problem is not None:
            failures += 1
            print(f"FAIL {name}: {problem}")
    accepted = sum(1 for case in CASES if case[2] is None)
    print(f"{len(CASES)} cases ({accepted} accept, {len(CASES) - accepted} refuse), {failures} failed")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
