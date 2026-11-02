/-- Proved from nothing but definitions. -/
theorem two_plus_two : 2 + 2 = 4 := rfl

/-- Uses a standard axiom of classical logic. -/
theorem either_way (p : Prop) : p ∨ ¬p := Classical.em p

/-- Something accepted without proof, like a seed you audited by reading it. -/
axiom seedIsHonest : Prop
axiom seedAudited : seedIsHonest

/-- Built on top of that assumption. -/
theorem chainIsHonest : seedIsHonest ∧ 2 + 2 = 4 := ⟨seedAudited, two_plus_two⟩

/-- Unfinished: `sorry` skips the proof. -/
theorem notFinished : 1 = 2 := sorry

#print axioms two_plus_two
#print axioms either_way
#print axioms chainIsHonest
#print axioms notFinished
