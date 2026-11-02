/-! Wheeler's DDC and the trust list, over a pure build model. -/
namespace Trust

/-- What a checker is asked to confirm about a binary: that it implements a
source, or that it meets a spec. -/
inductive Claim (B : Type) where
  | source (s : B)
  | spec (p : B)

/-- `run` being a function is the purity assumption. `sem` is what source means,
`admits` is the behaviours a spec allows, `want` is what the user actually wants,
`ask` is the question put to a checker, and `accept` is its yes. -/
structure World (B : Type) where
  run : B → B → B
  sem : B → B → B
  admits : B → (B → B) → Prop
  want : (B → B) → Prop
  ask : B → Claim B → B → B
  accept : B

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

/-- Everything a formula mentions. -/
def atoms : Why A → List A
  | atom a => [a]
  | all x y => atoms x ++ atoms y
  | any x y => atoms x ++ atoms y

/-- The claim fails when exactly the assumptions in `S` fail. -/
def Breaks (f : Why A) (S : List A) : Prop := ¬ holds (fun a => a ∉ S) f

/-- `S` breaks a claim exactly when it contains one of its cuts. -/
theorem breaks_iff (f : Why A) (S : List A) :
    Breaks f S ↔ ∃ c ∈ cuts f, ∀ a ∈ c, a ∈ S := by
  simpa [Breaks] using cuts_exact (fun a => a ∉ S) f

/-- A formula holds when everything it mentions holds. -/
theorem holds_of_atoms (σ : A → Prop) (f : Why A) (h : ∀ a ∈ atoms f, σ a) : holds σ f := by
  induction f with
  | atom a => exact h a (by simp [atoms])
  | all x y ihx ihy =>
    exact ⟨ihx fun a ha => h a (List.mem_append.mpr (Or.inl ha)),
      ihy fun a ha => h a (List.mem_append.mpr (Or.inr ha))⟩
  | any x y ihx _ =>
    exact Or.inl (ihx fun a ha => h a (List.mem_append.mpr (Or.inl ha)))

/-- Breaking two alternative routes means breaking both of them. -/
theorem breaks_any (x y : Why A) (S : List A) :
    Breaks (any x y) S ↔ Breaks x S ∧ Breaks y S := by
  simp [Breaks, holds, not_or]

/-- Failures a route never mentions cannot break it. -/
theorem not_breaks_of_unmentioned (f : Why A) (S : List A)
    (h : ∀ a ∈ atoms f, a ∉ S) : ¬ Breaks f S :=
  fun hb => hb (holds_of_atoms _ f h)

end Why

inductive Assumption (B : Type) where
  | seed (exe src : B)
  | honestSource (compilerSrc src : B)
  /-- Whatever implements this source only accepts claims that are true. -/
  | checker (checkerSrc : B)
  /-- This source does what the user wants. -/
  | wanted (src : B)
  /-- Everything this spec allows is what the user wants. -/
  | adequate (spec : B)

/-- The claim is true of this binary. -/
def Claim.Met (w : World B) : Claim B → B → Prop
  | .source s, exe => Implements w exe s
  | .spec p, exe => w.admits p (w.run exe)

/-- The binary `ck` says yes to this claim about `exe`. -/
def Accepts (w : World B) (ck exe : B) (c : Claim B) (cert : B) : Prop :=
  w.run ck (w.ask exe c cert) = w.accept

/-- The binary `ck` never says yes to something false. -/
def Sound (w : World B) (ck : B) : Prop :=
  ∀ exe c cert, Accepts w ck exe c cert → c.Met w exe

def Assumption.holds (w : World B) : Assumption B → Prop
  | .seed exe src => Implements w exe src
  | .honestSource cs s => ∀ c, Implements w c cs → Accurate w c s
  | .checker cs => ∀ c, Implements w c cs → Sound w c
  | .wanted s => w.want (w.sem s)
  | .adequate p => ∀ f, w.admits p f → w.want f

/-- A build tree: a seed, a compile step, two routes compared byte for byte, or
a result that a checker, itself built by `ck`, confirmed against its source. -/
inductive Build (B : Type) where
  | seed (exe src : B)
  | compile (c : Build B) (src : B)
  | agree (a b : Build B)
  | checked (t ck : Build B) (cert : B)

namespace Build

def src : Build B → B
  | seed _ s => s
  | compile _ s => s
  | agree a _ => src a
  | checked t _ _ => src t

def bin (w : World B) : Build B → B
  | seed e _ => e
  | compile c s => w.run (bin w c) s
  | agree a _ => bin w a
  | checked t _ _ => bin w t

/-- Every comparison in the tree really matched, and every checker said yes. -/
def Checked (w : World B) : Build B → Prop
  | seed .. => True
  | compile c _ => Checked w c
  | agree a b => Checked w a ∧ Checked w b ∧ bin w a = bin w b ∧ src a = src b
  | checked t ck cert =>
    Checked w t ∧ Checked w ck ∧ Accepts w (bin w ck) (bin w t) (.source (src t)) cert

/-- The trust list of a build. -/
def why : Build B → Why (Assumption B)
  | seed e s => .atom (.seed e s)
  | compile c s => .all (why c) (.atom (.honestSource (src c) s))
  | agree a b => .any (why a) (why b)
  | checked t ck _ => .any (why t) (.all (why ck) (.atom (.checker (src ck))))

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
  | checked t ck cert iht ihk =>
    obtain ⟨hct, hck, ha⟩ := hc
    rcases h with ht | ⟨hk, hs⟩
    · exact iht hct ht
    · exact hs _ (ihk hck hk) _ _ _ ha

/-- A check needs no history: `exe` is arbitrary, so nothing about how it was
built can appear here. Only the checker's own build does. -/
theorem check_ignores_ancestry (w : World B) (ck : Build B) (exe s cert : B)
    (hc : Checked w ck) (hk : (why ck).holds (Assumption.holds w))
    (hs : (Assumption.checker (src ck)).holds w)
    (ha : Accepts w (bin w ck) exe (.source s) cert) : Implements w exe s :=
  hs _ (sound w ck hc hk) _ _ _ ha

/-- One failure breaks a checked result only if the checker's side names it too. -/
theorem check_removes_failure (t ck : Build B) (cert : B) (a : Assumption B)
    (hk : a ∉ (why ck).atoms) (hc : a ≠ .checker (src ck)) :
    ¬ Why.Breaks (why (checked t ck cert)) [a] := by
  intro hb
  refine Why.not_breaks_of_unmentioned (.all (why ck) (.atom (.checker (src ck)))) [a] ?_
    ((Why.breaks_any _ _ _).mp hb).2
  intro b hbm
  simp only [Why.atoms, List.mem_append, List.mem_singleton] at hbm
  rcases hbm with hbm | rfl
  · simp only [List.mem_singleton]
    exact fun e => hk (e ▸ hbm)
  · simp only [List.mem_singleton]
    exact fun e => hc e.symm

/-- A failure that breaks both the build and the checker's build breaks the
result: shared ancestry undoes the check. -/
theorem shared_failure_returns (t ck : Build B) (cert : B) (a : Assumption B)
    (ht : Why.Breaks (why t) [a]) (hk : Why.Breaks (why ck) [a]) :
    Why.Breaks (why (checked t ck cert)) [a] :=
  (Why.breaks_any _ _ _).mpr ⟨ht, fun h => hk h.1⟩

/-- A build tree never mentions what the user wants. -/
theorem wanted_not_in_why (t : Build B) (s : B) : Assumption.wanted s ∉ (why t).atoms := by
  induction t with
  | seed => simp [why, Why.atoms]
  | compile _ _ ih => simp [why, Why.atoms, ih]
  | agree _ _ iha ihb => simp [why, Why.atoms, iha, ihb]
  | checked _ _ _ iht ihk => simp [why, Why.atoms, iht, ihk]

/-- The user wants what this binary does. -/
def Wanted (w : World B) (exe : B) : Prop := w.want (w.run exe)

/-- Faithful to a source the user wants. -/
def viaSource (t : Build B) : Why (Assumption B) :=
  .all (why t) (.atom (.wanted (src t)))

/-- Accepted by a checker against a spec the user wants. -/
def viaSpec (ck : Build B) (p : B) : Why (Assumption B) :=
  .all (why ck) (.all (.atom (.checker (src ck))) (.atom (.adequate p)))

theorem viaSource_sound (w : World B) (t : Build B) (hc : Checked w t)
    (h : (viaSource t).holds (Assumption.holds w)) : Wanted w (bin w t) := by
  obtain ⟨hw, hs⟩ := h
  have e : w.run (bin w t) = w.sem (src t) := funext (sound w t hc hw)
  unfold Wanted
  rw [e]
  exact hs

theorem viaSpec_sound (w : World B) (ck : Build B) (exe p cert : B)
    (hc : Checked w ck) (ha : Accepts w (bin w ck) exe (.spec p) cert)
    (h : (viaSpec ck p).holds (Assumption.holds w)) : Wanted w exe := by
  obtain ⟨hk, hs, hp⟩ := h
  exact hp _ (hs _ (sound w ck hc hk) _ _ _ ha)

/-- Every kind of build evidence leaves the source as one point of failure:
`t` here is any tree of rebuilds, comparisons and source-level checks. -/
theorem source_failure_survives (t : Build B) :
    Why.Breaks (viaSource t) [.wanted (src t)] :=
  fun h => h.2 (List.mem_singleton.mpr rfl)

/-- A proof against a spec is a second route that never mentions the source. -/
theorem spec_removes_source_failure (t ck : Build B) (p : B) :
    ¬ Why.Breaks (.any (viaSource t) (viaSpec ck p)) [.wanted (src t)] := by
  intro hb
  refine Why.not_breaks_of_unmentioned (viaSpec ck p) _ ?_ ((Why.breaks_any _ _ _).mp hb).2
  intro b hbm
  simp only [viaSpec, Why.atoms, List.mem_append, List.mem_singleton] at hbm
  simp only [List.mem_singleton]
  rcases hbm with hbm | rfl | rfl
  · exact fun e => wanted_not_in_why ck _ (e ▸ hbm)
  · exact fun e => nomatch e
  · exact fun e => nomatch e

end Build

/-! ### Thompson's attack as a concrete world, so the theorems cannot be vacuous -/

inductive T where
  | ccSrc | loginSrc | xzSrc | checkerSrc
  | ccGood | ccEvil | rootCc | rootStage1
  | loginGood | loginEvil | xzBin
  | checkerGood | checkerEvil
  | key | grant | deny
  | noBackdoor | cert | accept | reject
  | askSource (exe s cert : T)
  | askSpec (exe p cert : T)
  | other
  deriving DecidableEq, Repr

/-- What the honest checker answers about a binary against a source. -/
def verdictSource (e s k : T) : T :=
  if k = .cert ∧ ((s = .ccSrc ∧ (e = .ccGood ∨ e = .rootStage1)) ∨ (s = .loginSrc ∧ e = .loginGood))
  then .accept else .reject

/-- What the honest checker answers about a binary against a spec. -/
def verdictSpec (e p k : T) : T :=
  if k = .cert ∧ p = .noBackdoor ∧ e = .loginGood then .accept else .reject

def thompson : World T where
  run
    | .ccGood, .ccSrc => .ccGood
    | .ccGood, .loginSrc => .loginGood
    | .ccGood, .xzSrc => .xzBin
    | .ccGood, .checkerSrc => .checkerGood
    | .ccEvil, .ccSrc => .ccEvil
    | .ccEvil, .loginSrc => .loginEvil
    | .ccEvil, .xzSrc => .xzBin
    -- The trojan aims at the checker too: it accepts whatever it is shown.
    | .ccEvil, .checkerSrc => .checkerEvil
    | .rootCc, .ccSrc => .rootStage1
    | .rootStage1, .ccSrc => .ccGood
    | .rootStage1, .loginSrc => .loginGood
    | .rootStage1, .xzSrc => .xzBin
    | .rootStage1, .checkerSrc => .checkerGood
    | .checkerGood, .askSource e s k => verdictSource e s k
    | .checkerGood, .askSpec e p k => verdictSpec e p k
    | .checkerEvil, .askSource .. => .accept
    | .checkerEvil, .askSpec .. => .accept
    | .loginGood, .key => .deny
    | .loginEvil, .key => .grant
    | .xzBin, .key => .grant
    | _, _ => .other
  sem
    | .ccSrc, .ccSrc => .ccGood
    | .ccSrc, .loginSrc => .loginGood
    | .ccSrc, .xzSrc => .xzBin
    | .ccSrc, .checkerSrc => .checkerGood
    | .loginSrc, .key => .deny
    | .xzSrc, .key => .grant
    | .checkerSrc, .askSource e s k => verdictSource e s k
    | .checkerSrc, .askSpec e p k => verdictSpec e p k
    | _, _ => .other
  admits
    | .noBackdoor, f => f .key = .deny
    | _, _ => False
  want f := f .key = .deny
  ask
    | e, .source s, k => .askSource e s k
    | e, .spec p, k => .askSpec e p k
  accept := .accept

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

/-! ### Checks, in the same world -/

theorem login_faithful : Implements thompson .loginGood .loginSrc := by
  intro i; cases i <;> rfl

theorem xz_faithful : Implements thompson .xzBin .xzSrc := by
  intro i; cases i <;> rfl

theorem checker_faithful : Implements thompson .checkerGood .checkerSrc := by
  intro i; cases i <;> rfl

theorem verdictSource_sound (e s k : T) (h : verdictSource e s k = .accept) :
    Implements thompson e s := by
  unfold verdictSource at h
  split at h
  · rename_i hc
    obtain ⟨-, ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩⟩ := hc
    · exact good_faithful
    · exact stage1_faithful
    · exact login_faithful
  · cases h

theorem verdictSpec_sound (e p k : T) (h : verdictSpec e p k = .accept) :
    thompson.admits p (thompson.run e) := by
  unfold verdictSpec at h
  split at h
  · rename_i hc
    obtain ⟨-, rfl, rfl⟩ := hc
    rfl
  · cases h

/-- The honest checker's source really does only accept true claims. -/
theorem checker_source_sound : (Assumption.checker T.checkerSrc).holds thompson := by
  intro c hc exe claim k ha
  have e := hc (thompson.ask exe claim k)
  unfold Accepts at ha
  rw [e] at ha
  cases claim with
  | source s => exact verdictSource_sound exe s k ha
  | spec p => exact verdictSpec_sound exe p k ha

theorem compiles_checker : (Assumption.honestSource T.ccSrc T.checkerSrc).holds thompson := by
  intro c hc
  have e : thompson.run c .checkerSrc = .checkerGood := hc .checkerSrc
  unfold Accurate
  rw [e]
  exact checker_faithful

/-- A checker whose ancestry has nothing to do with the build it inspects. -/
def cleanChecker : Build T := .compile (.seed .ccGood .ccSrc) .checkerSrc

/-- A compiler built from a root that does not implement `ccSrc`. -/
def shakyBuild : Build T := .compile (.seed .rootCc .ccSrc) .ccSrc

/-- The route through the build really is false here. -/
theorem shaky_route_fails : ¬ (Build.why shakyBuild).holds (Assumption.holds thompson) := by
  intro h
  have e : thompson.run .rootCc .loginSrc = thompson.sem .ccSrc .loginSrc := h.1 .loginSrc
  cases e

theorem clean_checker_holds :
    (Build.why cleanChecker).holds (Assumption.holds thompson) :=
  ⟨good_faithful, compiles_checker⟩

/-- The check carries the claim on its own: a false ancestor does not matter. -/
theorem check_cuts_bad_ancestor :
    Implements thompson (Build.bin thompson (.checked shakyBuild cleanChecker .cert)) .ccSrc := by
  refine Build.sound thompson (.checked shakyBuild cleanChecker .cert) ?_
    (Or.inr ⟨clean_checker_holds, checker_source_sound⟩)
  exact ⟨trivial, trivial, by unfold Accepts; decide⟩

/-- A clean checker refuses the trojan. -/
theorem clean_checker_rejects_trojan :
    ¬ Accepts thompson (Build.bin thompson cleanChecker) .ccEvil (.source .ccSrc) .cert := by
  unfold Accepts; decide

def trojan : Build T := .seed .ccEvil .ccSrc

/-- The trojan inspected by a checker the trojan itself compiled. -/
def fooled : Build T := .checked trojan (.compile trojan .checkerSrc) .cert

/-- Every check in the tree passes. -/
theorem fooled_passes : Build.Checked thompson fooled :=
  ⟨trivial, trivial, by unfold Accepts; decide⟩

/-- And the result is still the trojan. -/
theorem fooled_is_false :
    ¬ Implements thompson (Build.bin thompson fooled) (Build.src fooled) :=
  evil_is_not_faithful

/-- The trojan is one failure that takes out both sides of the check. -/
theorem fooled_shares_its_failure :
    Why.Breaks (Build.why fooled) [.seed .ccEvil .ccSrc] :=
  Build.shared_failure_returns _ _ _ _ (fun h => h (List.mem_singleton.mpr rfl))
    (fun h => h.1 (List.mem_singleton.mpr rfl))

/-- The same trojan with a clean checker has no single failure left. -/
theorem clean_check_has_no_single_failure :
    ¬ Why.Breaks (Build.why (.checked trojan cleanChecker .cert)) [.seed .ccEvil .ccSrc] := by
  apply Build.check_removes_failure
  · simp [Build.why, cleanChecker, Why.atoms]
  · exact fun e => nomatch e

/-- A backdoored source, rebuilt two ways that agree byte for byte. -/
def xzBuild : Build T :=
  .agree (.compile (.seed .ccGood .ccSrc) .xzSrc) (.compile (.seed .rootStage1 .ccSrc) .xzSrc)

theorem compiles_xz : (Assumption.honestSource T.ccSrc T.xzSrc).holds thompson := by
  intro c hc
  have e : thompson.run c .xzSrc = .xzBin := hc .xzSrc
  unfold Accurate
  rw [e]
  exact xz_faithful

/-- Every comparison passes and everything the build's list names is true. -/
theorem xz_passes_every_build_check :
    Build.Checked thompson xzBuild ∧ (Build.why xzBuild).holds (Assumption.holds thompson) :=
  ⟨⟨trivial, trivial, rfl, rfl⟩, Or.inl ⟨good_faithful, compiles_xz⟩⟩

/-- The binary is faithful to its source, and it is still not what anyone wants. -/
theorem xz_is_not_wanted : ¬ Build.Wanted thompson (Build.bin thompson xzBuild) := by
  intro h
  cases (h : thompson.run .xzBin .key = .deny)

/-- Checking the source would pass it. Checking the spec refuses it. -/
theorem spec_refuses_xz :
    ¬ Accepts thompson .checkerGood .xzBin (.spec .noBackdoor) .cert := by
  unfold Accepts; decide

theorem spec_accepts_login :
    Accepts thompson .checkerGood .loginGood (.spec .noBackdoor) .cert := by
  unfold Accepts; decide

theorem login_passes_spec_route : Build.Wanted thompson .loginGood := by
  refine Build.viaSpec_sound thompson cleanChecker .loginGood .noBackdoor .cert ?_
    spec_accepts_login ⟨clean_checker_holds, checker_source_sound, ?_⟩
  · exact trivial
  · exact fun _ h => h

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

-- A check whose ancestry is separate, then one that shares the compiler.
#eval minimalCuts (.any (.all (.atom "gcc") (.atom "source")) (.all (.atom "checker seed") (.atom "spec")))
#eval minimalCuts (.any (.all (.atom "gcc") (.atom "source")) (.all (.atom "gcc") (.atom "spec")))

#print axioms ddc
#print axioms Why.cuts_exact
#print axioms Build.sound
#print axioms ddc_catches_trojan
#print axioms evil_is_not_faithful
#print axioms Build.check_ignores_ancestry
#print axioms Build.check_removes_failure
#print axioms Build.shared_failure_returns
#print axioms Build.source_failure_survives
#print axioms Build.spec_removes_source_failure
#print axioms check_cuts_bad_ancestor
#print axioms fooled_passes
#print axioms fooled_is_false
#print axioms xz_passes_every_build_check
#print axioms xz_is_not_wanted
#print axioms spec_refuses_xz
#print axioms login_passes_spec_route

end Trust
