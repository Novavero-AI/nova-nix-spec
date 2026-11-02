# nova-nix-spec

Lean models of the Nix store layer, the proofs about them, and a proof checker
that can be built from a seed.

- `NixLayer.lean`: ATerm strings, the store path fingerprint, the hash quotient.
- `Trust.lean`: diverse double-compiling, and a trust list over a build tree,
  including checked edges and what shared ancestry does to them.
- `checker/`: `mmcheck`, a Metamath proof checker.
- `experiments/`: small standalone files.

Build with `lake build`. `#print axioms` in each file lists what its theorems
rest on.

## mmcheck

`mmcheck database.mm` exits 0 when every `$p` proof in the database checks, and
otherwise refuses with a reason. It holds no logic of its own: the axioms are the
database's `$a` statements. A proof containing `?` is refused.

It is written in the C subset M2-Planet compiles, so the stage0 ladder can build
it with no other compiler.

- `checker/run-suite.sh CHECKER SUITE_DIR` runs a build over a checkout of
  [metamath-test](https://github.com/david-a-wheeler/metamath-test).
- `checker/build-linux.sh` builds it with M2-Planet for 32-bit Linux.
- `checker/build-windows.cmd` builds it with the tools a
  [stage0-pe32](https://github.com/Novavero-AI/stage0-pe32) checkout built from
  its seed.
