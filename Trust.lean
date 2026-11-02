/-! Wheeler's DDC and the trust list, over a pure build model. -/
namespace Trust

/-- `run` being a function is the purity assumption. `sem` is what source means. -/
structure World (B : Type) where
  run : B → B → B
  sem : B → B → B

variable {B : Type}

/-- The executable behaves as the source means, on every input. -/
def Implements (w : World B) (exe src : B) : Prop := ∀ i, w.run exe i = w.sem src i

/-- Compiler `c` turns `src` into a binary that implements it. -/
def Accurate (w : World B) (c src : B) : Prop := Implements w (w.run c src) src

/-- Wheeler's `source_corresponds_to_executable`, environments elided. -/
theorem ddc (w : World B) (cT sP sA cA : B)
    (cT_compiles_sP : Accurate w cT sP)
    (sP_compiles_sA : ∀ c, Implements w c sP → Accurate w c sA)
    (compare : w.run (w.run cT sP) sA = cA) :
    Implements w cA sA := by
  rw [← compare]
  exact sP_compiles_sA _ cT_compiles_sP

/-- Why something is believed: a monotone formula over assumptions. -/
inductive Why (A : Type) where
  | atom (a : A)
  | all (x y : Why A)
  | any (x y : Why A)
  deriving Repr

namespace Why
variable {A : Type}

def holds (σ : A → Prop) : Why A → Prop
  | atom a => σ a
  | all x y => holds σ x ∧ holds σ y
  | any x y => holds σ x ∨ holds σ y

/-- Each list is one complete way to break the claim. -/
def cuts : Why A → List (List A)
  | atom a => [[a]]
  | all x y => cuts x ++ cuts y
  | any x y => (cuts x).flatMap fun c => (cuts y).map fun d => c ++ d

/-- The claim fails exactly when every atom of some cut has failed. -/
theorem cuts_exact (σ : A → Prop) (f : Why A) :
    ¬ holds σ f ↔ ∃ c ∈ cuts f, ∀ a ∈ c, ¬ σ a := by
  induction f with
  | atom a => simp [holds, cuts]
  | all x y ihx ihy =>
    simp only [holds, cuts, List.mem_append]
    constructor
    · intro h
      by_cases hx : holds σ x
      · have hy : ¬ holds σ y := fun hy => h ⟨hx, hy⟩
        obtain ⟨c, hc, hb⟩ := ihy.mp hy
        exact ⟨c, Or.inr hc, hb⟩
      · obtain ⟨c, hc, hb⟩ := ihx.mp hx
        exact ⟨c, Or.inl hc, hb⟩
    · rintro ⟨c, hc | hc, hb⟩ ⟨hx, hy⟩
      · exact ihx.mpr ⟨c, hc, hb⟩ hx
      · exact ihy.mpr ⟨c, hc, hb⟩ hy
  | any x y ihx ihy =>
    simp only [holds, cuts, List.mem_flatMap, List.mem_map]
    constructor
    · intro h
      obtain ⟨c, hc, hb⟩ := ihx.mp (fun hx => h (Or.inl hx))
      obtain ⟨d, hd, hb2⟩ := ihy.mp (fun hy => h (Or.inr hy))
      refine ⟨c ++ d, ⟨c, hc, d, hd, rfl⟩, ?_⟩
      intro a ha
      rcases List.mem_append.mp ha with h1 | h1
      · exact hb a h1
      · exact hb2 a h1
    · rintro ⟨_, ⟨c, hc, d, hd, rfl⟩, hb⟩ (hx | hy)
      · exact ihx.mpr ⟨c, hc, fun a ha => hb a (List.mem_append.mpr (Or.inl ha))⟩ hx
      · exact ihy.mpr ⟨d, hd, fun a ha => hb a (List.mem_append.mpr (Or.inr ha))⟩ hy

end Why

inductive Assumption (B : Type) where
  | seed (exe src : B)
  | honestSource (compilerSrc src : B)

def Assumption.holds (w : World B) : Assumption B → Prop
  | .seed exe src => Implements w exe src
  | .honestSource cs s => ∀ c, Implements w c cs → Accurate w c s

/-- A build tree: a seed, a compile step, or two routes compared byte for byte. -/
inductive Build (B : Type) where
  | seed (exe src : B)
  | compile (c : Build B) (src : B)
  | agree (a b : Build B)

namespace Build

def src : Build B → B
  | seed _ s => s
  | compile _ s => s
  | agree a _ => src a

def bin (w : World B) : Build B → B
  | seed e _ => e
  | compile c s => w.run (bin w c) s
  | agree a _ => bin w a

/-- Every comparison in the tree really matched. -/
def Checked (w : World B) : Build B → Prop
  | seed .. => True
  | compile c _ => Checked w c
  | agree a b => Checked w a ∧ Checked w b ∧ bin w a = bin w b ∧ src a = src b

/-- The trust list of a build. -/
def why : Build B → Why (Assumption B)
  | seed e s => .atom (.seed e s)
  | compile c s => .all (why c) (.atom (.honestSource (src c) s))
  | agree a b => .any (why a) (why b)

/-- If everything the list names holds, the binary implements its source. -/
theorem sound (w : World B) (t : Build B) (hc : Checked w t)
    (h : (why t).holds (Assumption.holds w)) : Implements w (bin w t) (src t) := by
  induction t with
  | seed e s => exact h
  | compile c s ih => exact h.2 _ (ih hc h.1)
  | agree a b iha ihb =>
    obtain ⟨hca, hcb, hbin, hsrc⟩ := hc
    rcases h with ha | hb
    · exact iha hca ha
    · have := ihb hcb hb
      simp only [bin, src]
      rw [hbin, hsrc]
      exact this

end Build

/-! ### Thompson's attack as a concrete world, so the theorems cannot be vacuous -/

inductive T where
  | ccSrc | loginSrc
  | ccGood | ccEvil | rootCc | rootStage1
  | loginGood | loginEvil
  | other
  deriving DecidableEq, Repr

def thompson : World T where
  run
    | .ccGood, .ccSrc => .ccGood
    | .ccGood, .loginSrc => .loginGood
    | .ccEvil, .ccSrc => .ccEvil
    | .ccEvil, .loginSrc => .loginEvil
    | .rootCc, .ccSrc => .rootStage1
    | .rootStage1, .ccSrc => .ccGood
    | .rootStage1, .loginSrc => .loginGood
    | _, _ => .other
  sem
    | .ccSrc, .ccSrc => .ccGood
    | .ccSrc, .loginSrc => .loginGood
    | _, _ => .other

/-- The trojan rebuilds itself byte for byte: reproducibility passes. -/
theorem evil_is_reproducible : thompson.run .ccEvil .ccSrc = .ccEvil := rfl

/-- And yet it does not implement its source. -/
theorem evil_is_not_faithful : ¬ Implements thompson .ccEvil .ccSrc := fun h => by
  have := h .ccSrc
  simp [thompson] at this

theorem good_faithful : Implements thompson .ccGood .ccSrc := by
  intro i; cases i <;> rfl

theorem stage1_faithful : Implements thompson .rootStage1 .ccSrc := by
  intro i; cases i <;> rfl

/-- Self-compilation is honest in this world, at source level. -/
theorem source_honest (c : T) (h : Implements thompson c .ccSrc) :
    Accurate thompson c .ccSrc := by
  have e : thompson.run c .ccSrc = .ccGood := h .ccSrc
  unfold Accurate
  rw [e]
  exact good_faithful

/-- DDC through an unrelated root reaches the honest bytes. -/
theorem ddc_accepts_honest : Implements thompson .ccGood .ccSrc :=
  ddc thompson .rootCc .ccSrc .ccSrc .ccGood stage1_faithful source_honest rfl

/-- DDC refuses the trojan: the comparison cannot pass. -/
theorem ddc_catches_trojan : thompson.run (thompson.run .rootCc .ccSrc) .ccSrc ≠ .ccEvil := by
  decide

/-! ### What a flat set gets wrong -/

/-- With two agreeing routes, one failed assumption does not break the claim,
so a flat list of assumptions overstates what is needed. -/
theorem flat_overstates :
    ∃ (f : Why Bool) (σ : Bool → Prop), f.holds σ ∧ ¬ σ false :=
  ⟨.any (.atom true) (.atom false), fun b => b = true, Or.inl rfl, by simp⟩

/-- Print minimal cuts: dedupe each, then drop any that contains a smaller one. -/
def minimalCuts (f : Why String) : List (List String) :=
  let norm (c : List String) := c.foldr (fun a acc => if acc.contains a then acc else a :: acc) []
  let cs := (f.cuts.map norm)
  let sub (a b : List String) := a.all (b.contains ·)
  let keep := cs.filter fun c => !cs.any fun d => sub d c && !(sub c d)
  keep.foldr (fun c acc => if acc.any (fun d => sub d c && sub c d) then acc else c :: acc) []

open Why in
def route (seed kernel cpu : String) : Why String :=
  .all (.atom seed) (.all (.atom kernel) (.all (.atom cpu) (.atom "ladder source")))

open Why in
#eval minimalCuts (.any (route "pe32 seed" "NT kernel" "CPU A") (route "hex0 seed" "Linux kernel" "CPU A"))
#eval minimalCuts (.any (route "pe32 seed" "NT kernel" "CPU A") (route "hex0 seed" "Linux kernel" "CPU B"))
#eval minimalCuts (.any (route "same seed" "NT kernel" "CPU A") (route "same seed" "NT kernel" "CPU A"))

#print axioms ddc
#print axioms Why.cuts_exact
#print axioms Build.sound
#print axioms ddc_catches_trojan
#print axioms evil_is_not_faithful

end Trust
