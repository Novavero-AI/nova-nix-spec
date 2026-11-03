# nova-nix-spec

Lean models of the Nix store layer, the proofs about them, and a proof checker
that can be built from a seed.

- `NixLayer.lean`: ATerm strings, the store path fingerprint, the hash quotient.
- `Trust.lean`: diverse double-compiling, and a trust list over a build tree,
  including checked edges and what shared ancestry does to them.
- `Metamath.lean`: Metamath's proof rule, a pure checker, and the proof that the
  checker only accepts what the rule derives. Parsing, block scoping and the
  decoding of compressed proofs are outside it, and it is not a proof of `mmcheck`.
- `Hex0.lean`: hex0 as a pure function, and proofs about it. It is the rule the
  Windows PE32 seed follows. The upstream Linux x86 seed also takes `G` and `g`
  as a digit worth 16.
- `Seed.lean`: each hex0 seed, Linux x86 and Windows PE32, is exactly what its
  annotated source decodes to.
- `checker/`: `mmcheck`, a Metamath proof checker.
- `experiments/`: small standalone files.

`Seed.lean` is about the upstream seed files, which it reads from
`Seed/Bytes.lean`. That file is not tracked. Write it from checkouts of
[bootstrap-seeds](https://github.com/oriansj/bootstrap-seeds) and
[stage0-pe32](https://github.com/Novavero-AI/stage0-pe32) at the commits
`BOOTSTRAP_SEEDS_REF` and `STAGE0_PE32_REF` in
[ci.yml](.github/workflows/ci.yml), then build:

```sh
python3 scripts/seed_bytes.py BOOTSTRAP_SEEDS_DIR STAGE0_PE32_DIR
lake build
lake env lean scripts/AxiomAudit.lean
```

`scripts/AxiomAudit.lean` fails unless every declaration in the five libraries
rests on no axiom beyond `propext`, `Classical.choice` and `Quot.sound`, so a
`sorry`, a `native_decide` or a declared `axiom` fails it.

## mmcheck

`mmcheck database.mm` exits 0 when every `$p` proof in the database checks, and
otherwise refuses with a reason. It holds no logic of its own: the axioms are the
database's `$a` statements. A proof containing `?` is refused.

It is written in the C subset M2-Planet compiles, so the stage0 ladder can build
it with no other compiler.

- `checker/run-suite.sh CHECKER SUITE_DIR` runs a build over a checkout of
  [metamath-test](https://github.com/david-a-wheeler/metamath-test).
- `checker/tests/compare_rules.py CHECKER` runs one small database per rule.
- `checker/tests/compare_mutants.py SEED CHECKER SUITE_DIR DIVISOR` corrupts real
  databases and requires the verdict of `verify.py`, a second verifier written
  from the specification alone.
- `checker/tests/kill_checks.py SUITE_DIR WORK_DIR` removes each check from
  `mmcheck.c` in turn and requires a test to notice.
- `checker/build-linux.sh` builds it with M2-Planet for 32-bit Linux.
- `checker/build-windows.cmd` builds it with the tools a
  [stage0-pe32](https://github.com/Novavero-AI/stage0-pe32) checkout built from
  its seed.

## License

Apache-2.0. See [LICENSE](LICENSE) and [NOTICE](NOTICE).
