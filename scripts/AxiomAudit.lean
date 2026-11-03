import Lean
import NixLayer
import Trust
import Metamath
import Hex0
import Seed

/-! Fails unless every constant the libraries declare rests on no axiom beyond
`propext`, `Classical.choice` and `Quot.sound`. A `sorry` is the axiom
`sorryAx`, and `native_decide` declares an axiom that its compiled evaluation
came out true, so both fail it, as does any `axiom` a library declares, used or
not.

Run it after `lake build`: `lake env lean scripts/AxiomAudit.lean`. -/

open Lean

/-- The `lean_lib` roots in lakefile.toml. A module belongs to a library when
the root is a prefix of its name, as `Seed` is of `Seed.Bytes`. -/
def libraries : Array Name := #[`NixLayer, `Trust, `Metamath, `Hex0, `Seed]

def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let env <- getEnv
  for library in libraries do
    if (env.getModuleIdx? library).isNone then
      logError m!"{library} is not imported"
  let mut checked : Nat := 0
  for module in env.header.moduleNames, data in env.header.moduleData do
    if libraries.any (·.isPrefixOf module) then
      for name in data.constNames do
        let others := (<- collectAxioms name).filter (!standardAxioms.contains ·)
        unless others.isEmpty do
          logError m!"{name} in {module} rests on {others}"
        checked := checked + 1
  logInfo m!"{checked} constants checked"
