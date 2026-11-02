import Hex0
import Seed.Bytes

/-! Each hex0 seed is exactly what its annotated source says: `Hex0.decode`
applied to the source gives the seed, byte for byte. The kernel checks this by
evaluating the decoder, so no binary had to run to establish it, and the
annotated source can be read in place of the seed. -/

-- The kernel evaluates the decoder over a whole source, past the default limit.
set_option maxRecDepth 1000000

namespace Seed

theorem linux_seed_is_its_source : Hex0.decode linuxSource.toList = linuxSeed.toList := by
  decide +kernel

theorem pe32_seed_is_its_source : Hex0.decode pe32Source.toList = pe32Seed.toList := by
  decide +kernel

#print axioms linux_seed_is_its_source
#print axioms pe32_seed_is_its_source

end Seed
