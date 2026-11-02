/-! Does an injective hash axiom, polymorphic in the input type, stay consistent?
The two axiom statements are copied from the claim under test; nothing else is. -/

opaque Hash : Type
axiom hash_of {α : Type} [Inhabited α] : α → Hash
axiom hash_injectivity {α : Type} [Inhabited α] (a b : α) :
  hash_of a = hash_of b → a = b

/-- Cantor's diagonal argument, instantiated at `α := Hash → Prop`. -/
theorem everything_is_provable : False := by
  let f : (Hash → Prop) → Hash := hash_of
  let S : Hash → Prop := fun h => ∃ g : Hash → Prop, f g = h ∧ ¬ g h
  have not_S : ¬ S (f S) := by
    intro hs
    obtain ⟨g, hg, hn⟩ := hs
    have : g = S := hash_injectivity g S hg
    subst this
    exact hn ⟨_, rfl, hn⟩
  exact not_S ⟨S, rfl, not_S⟩

#print axioms everything_is_provable
