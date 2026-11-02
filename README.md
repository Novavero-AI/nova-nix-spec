# nova-nix-spec

Lean models of the Nix store layer, and the proofs about them.

- `NixLayer.lean`: ATerm strings, the store path fingerprint, the hash quotient.
- `Trust.lean`: diverse double-compiling, and a trust list over a build tree.
- `experiments/`: small standalone files.

Build with `lake build`. `#print axioms` in each file lists what its theorems rest on.
