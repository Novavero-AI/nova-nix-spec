/-! Real statements about the Nix store layer, with no hash axiom. -/
namespace NixLayer

/-! ### ATerm strings, mirroring `escapeATermBytes` and `pStringContent` -/

def esc (c : UInt8) : List UInt8 :=
  if c = 92 then [92, 92] else if c = 34 then [92, 34]
  else if c = 10 then [92, 110] else if c = 13 then [92, 114]
  else if c = 9 then [92, 116] else [c]

def escape (s : List UInt8) : List UInt8 := s.flatMap esc

def unesc (e : UInt8) : UInt8 :=
  if e = 110 then 10 else if e = 114 then 13 else if e = 116 then 9 else e

def scan : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => none
  | c :: r =>
    if c = 34 then some ([], r)
    else if c = 92 then
      match r with
      | [] => none
      | e :: rest => (scan rest).map fun p => (unesc e :: p.1, p.2)
    else (scan r).map fun p => (c :: p.1, p.2)

theorem scan_quote (r : List UInt8) : scan (34 :: r) = some ([], r) := by
  cases r <;> simp [scan]

theorem scan_bs (e : UInt8) (r : List UInt8) :
    scan (92 :: e :: r) = (scan r).map fun p => (unesc e :: p.1, p.2) := by
  simp [scan]

theorem scan_plain (c : UInt8) (r : List UInt8) (h1 : c ≠ 34) (h2 : c ≠ 92) :
    scan (c :: r) = (scan r).map fun p => (c :: p.1, p.2) := by
  cases r <;> simp [scan, h1, h2]

/-- Parsing an escaped string returns exactly the string and the remainder. -/
theorem scan_escape (s rest : List UInt8) :
    scan (escape s ++ 34 :: rest) = some (s, rest) := by
  induction s with
  | nil => exact scan_quote rest
  | cons c cs ih =>
    have tail : escape (c :: cs) = esc c ++ escape cs := rfl
    rw [tail, List.append_assoc]
    by_cases h1 : c = 92
    · subst h1
      show scan (92 :: 92 :: (escape cs ++ 34 :: rest)) = _
      rw [scan_bs, ih]; rfl
    by_cases h2 : c = 34
    · subst h2
      show scan (92 :: 34 :: (escape cs ++ 34 :: rest)) = _
      rw [scan_bs, ih]; rfl
    by_cases h3 : c = 10
    · subst h3
      show scan (92 :: 110 :: (escape cs ++ 34 :: rest)) = _
      rw [scan_bs, ih]; rfl
    by_cases h4 : c = 13
    · subst h4
      show scan (92 :: 114 :: (escape cs ++ 34 :: rest)) = _
      rw [scan_bs, ih]; rfl
    by_cases h5 : c = 9
    · subst h5
      show scan (92 :: 116 :: (escape cs ++ 34 :: rest)) = _
      rw [scan_bs, ih]; rfl
    · have e : esc c = [c] := by simp [esc, h1, h2, h3, h4, h5]
      rw [e]
      show scan (c :: (escape cs ++ 34 :: rest)) = _
      rw [scan_plain c _ h2 h1, ih]; rfl

/-- Escaped strings are self-delimiting: no field can bleed into the next. -/
theorem quoted_prefix_free (a b r₁ r₂ : List UInt8)
    (h : escape a ++ 34 :: r₁ = escape b ++ 34 :: r₂) : a = b ∧ r₁ = r₂ := by
  have ha := scan_escape a r₁
  have hb := scan_escape b r₂
  rw [h, hb] at ha
  have := Option.some.inj ha
  simp only [Prod.mk.injEq] at this
  exact ⟨this.1.symm, this.2.symm⟩

theorem escape_injective (a b : List UInt8) (h : escape a = escape b) : a = b :=
  (quoted_prefix_free a b [] [] (by rw [h])).1

/-! ### The store path fingerprint, mirroring `makeStorePath` -/

def colon : UInt8 := 58
/-- The bytes of `:sha256`. -/
def sha : List UInt8 := [58, 115, 104, 97, 50, 53, 54]

def fp (typ hex dir name : List UInt8) : List UInt8 :=
  typ ++ sha ++ colon :: hex ++ colon :: dir ++ colon :: name

theorem split_last (a b x y : List UInt8) (hx : colon ∉ x) (hy : colon ∉ y)
    (h : a ++ colon :: x = b ++ colon :: y) : a = b ∧ x = y := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simpa using h
    | cons b0 b' =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.2 ▸ List.mem_append_right b' List.mem_cons_self) hx
  | cons a0 a' ih =>
    cases b with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.2.symm ▸ List.mem_append_right a' List.mem_cons_self) hy
    | cons b0 b' =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨h0, ht⟩ := ih b' h.2
      exact ⟨by rw [h.1, h0], ht⟩

/-- Same directory, and neither hex nor name contains a colon: the preimage
determines type, digest and name. -/
theorem fp_injective (t₁ t₂ x₁ x₂ d n₁ n₂ : List UInt8)
    (hx₁ : colon ∉ x₁) (hx₂ : colon ∉ x₂) (hn₁ : colon ∉ n₁) (hn₂ : colon ∉ n₂)
    (h : fp t₁ x₁ d n₁ = fp t₂ x₂ d n₂) : t₁ = t₂ ∧ x₁ = x₂ ∧ n₁ = n₂ := by
  have h1 : (t₁ ++ sha ++ colon :: x₁ ++ colon :: d) ++ colon :: n₁
      = (t₂ ++ sha ++ colon :: x₂ ++ colon :: d) ++ colon :: n₂ := by
    simpa [fp, List.append_assoc] using h
  obtain ⟨p, hn⟩ := split_last _ _ _ _ hn₁ hn₂ h1
  have p2 : (t₁ ++ sha ++ colon :: x₁) ++ colon :: d
      = (t₂ ++ sha ++ colon :: x₂) ++ colon :: d := by
    simpa [List.append_assoc] using p
  have p3 := List.append_cancel_right p2
  have p4 : (t₁ ++ sha) ++ colon :: x₁ = (t₂ ++ sha) ++ colon :: x₂ := by
    simpa [List.append_assoc] using p3
  obtain ⟨q, hx⟩ := split_last _ _ _ _ hx₁ hx₂ p4
  exact ⟨List.append_cancel_right q, hx, hn⟩

/-- The name rule is load-bearing: allow a colon in a name and two different
triples share a preimage, so a store path collides with no hash collision. -/
theorem name_rule_is_needed :
    ∃ t₁ x₁ n₁ t₂ x₂ n₂ d : List UInt8,
      fp t₁ x₁ d n₁ = fp t₂ x₂ d n₂ ∧ t₁ ≠ t₂ :=
  ⟨[], [], [65] ++ sha ++ [58, 58, 58, 66],
   sha ++ [58, 58, 58, 65], [], [66], [], by decide, by decide⟩

variable {D : Type}

def Collision {P : Type} (H : P → D) : Prop := ∃ u v : P, u ≠ v ∧ H u = H v

/-- Two different store path inputs with one output hand you a real collision. -/
theorem path_binding (H : List UInt8 → D) (t₁ t₂ x₁ x₂ d n₁ n₂ : List UInt8)
    (hx₁ : colon ∉ x₁) (hx₂ : colon ∉ x₂) (hn₁ : colon ∉ n₁) (hn₂ : colon ∉ n₂)
    (h : H (fp t₁ x₁ d n₁) = H (fp t₂ x₂ d n₂)) :
    (t₁ = t₂ ∧ x₁ = x₂ ∧ n₁ = n₂) ∨ Collision H := by
  by_cases e : fp t₁ x₁ d n₁ = fp t₂ x₂ d n₂
  · exact Or.inl (fp_injective _ _ _ _ _ _ _ hx₁ hx₂ hn₁ hn₂ e)
  · exact Or.inr ⟨_, _, e, h⟩

/-! ### The hash quotient, after `hashOutputsOrInputMaskedDerivation`

A fixed-output derivation contributes only its content address. `how` stands
for what masking discards: URL, mirrors, builder. -/

mutual
  inductive Drv where
    | fixed (ca how : Nat)
    | input (body : Nat) (deps : Deps)
  inductive Deps where
    | nil
    | cons (d : Drv) (rest : Deps)
end

inductive Pre (D : Type) where
  | fixed (ca : Nat)
  | input (body : Nat) (deps : List D)

mutual
  def quot (H : Pre D → D) : Drv → D
    | .fixed ca _ => H (.fixed ca)
    | .input b ds => H (.input b (quots H ds))
  def quots (H : Pre D → D) : Deps → List D
    | .nil => []
    | .cons d r => quot H d :: quots H r
end

/-! The relation upstream's manual writes as `~IADrv`, on lists for now. -/

mutual
  def Equiv : Drv → Drv → Prop
    | .fixed c₁ _, .fixed c₂ _ => c₁ = c₂
    | .input b₁ r, .input b₂ s => b₁ = b₂ ∧ EquivD r s
    | _, _ => False
  def EquivD : Deps → Deps → Prop
    | .nil, .nil => True
    | .cons a r, .cons b s => Equiv a b ∧ EquivD r s
    | _, _ => False
end

/-! Equivalent derivations hash the same. This is why changing a mirror does
not rebuild the world. -/

mutual
  theorem masked (H : Pre D → D) : ∀ a b, Equiv a b → quot H a = quot H b
    | .fixed c₁ _, .fixed c₂ _, h => by
        have e : c₁ = c₂ := h
        simp only [quot, e]
    | .input b₁ r, .input b₂ s, h => by
        have e : b₁ = b₂ ∧ EquivD r s := h
        simp only [quot, e.1, maskedD H r s e.2]
  theorem maskedD (H : Pre D → D) : ∀ r s, EquivD r s → quots H r = quots H s
    | .nil, .nil, _ => rfl
    | .cons a r, .cons b s, h => by
        have e : Equiv a b ∧ EquivD r s := h
        simp only [quots, masked H a b e.1, maskedD H r s e.2]
end

/-! Equal hash means equivalent, or an explicit collision in `H`. Nothing is
assumed about `H`. -/

mutual
  theorem binding (H : Pre D → D) : ∀ a b, quot H a = quot H b → Equiv a b ∨ Collision H
    | .fixed c₁ h₁, .fixed c₂ h₂, h => by
        by_cases e : c₁ = c₂
        · exact Or.inl e
        · exact Or.inr ⟨.fixed c₁, .fixed c₂, by simpa using e, h⟩
    | .fixed c _, .input b ds, h => Or.inr ⟨.fixed c, .input b (quots H ds), by simp, h⟩
    | .input b ds, .fixed c _, h => Or.inr ⟨.input b (quots H ds), .fixed c, by simp, h⟩
    | .input b₁ r, .input b₂ s, h => by
        by_cases e : Pre.input b₁ (quots H r) = Pre.input b₂ (quots H s)
        · have p : b₁ = b₂ ∧ quots H r = quots H s := by simpa using e
          cases bindingD H r s p.2 with
          | inl q => exact Or.inl ⟨p.1, q⟩
          | inr c => exact Or.inr c
        · exact Or.inr ⟨_, _, e, h⟩
  theorem bindingD (H : Pre D → D) : ∀ r s, quots H r = quots H s → EquivD r s ∨ Collision H
    | .nil, .nil, _ => Or.inl trivial
    | .nil, .cons _ _, h => by simp [quots] at h
    | .cons _ _, .nil, h => by simp [quots] at h
    | .cons a r, .cons b s, h => by
        have p : quot H a = quot H b ∧ quots H r = quots H s := by simpa [quots] using h
        cases binding H a b p.1 with
        | inr c => exact Or.inr c
        | inl ea =>
          cases bindingD H r s p.2 with
          | inr c => exact Or.inr c
          | inl er => exact Or.inl ⟨ea, er⟩
end

/-! ### Upstream's "symmetric closure" sentence

`d₃` and `d₄` use different fetches of one content-addressed file, and both
resolve to `r`. They are input-content equivalent. -/

inductive Toy where | d₃ | d₄ | r
  deriving DecidableEq

inductive Step : Toy → Toy → Prop
  | a : Step .d₃ .r
  | b : Step .d₄ .r

inductive Star : Toy → Toy → Prop
  | refl (x) : Star x x
  | tail {x y z} : Star x y → Step y z → Star x z

theorem star_from_d₃ {x y} (h : Star x y) : x = .d₃ → y = .d₃ ∨ y = .r := by
  induction h with
  | refl => exact Or.inl
  | tail _ s _ => intro _; cases s <;> exact Or.inr rfl

theorem star_from_d₄ {x y} (h : Star x y) : x = .d₄ → y = .d₄ ∨ y = .r := by
  induction h with
  | refl => exact Or.inl
  | tail _ s _ => intro _; cases s <;> exact Or.inr rfl

/-- Both reach the same normal form, yet neither reaches the other, so the
symmetric closure of the reduction misses a pair the equivalence must contain. -/
theorem symmetric_closure_too_small :
    Star .d₃ .r ∧ Star .d₄ .r ∧ ¬ (Star .d₃ .d₄ ∨ Star .d₄ .d₃) := by
  refine ⟨.tail (.refl _) .a, .tail (.refl _) .b, ?_⟩
  rintro (h | h)
  · rcases star_from_d₃ h rfl with e | e <;> cases e
  · rcases star_from_d₄ h rfl with e | e <;> cases e

#print axioms scan_escape
#print axioms quoted_prefix_free
#print axioms fp_injective
#print axioms name_rule_is_needed
#print axioms path_binding
#print axioms masked
#print axioms binding
#print axioms symmetric_closure_too_small

end NixLayer
