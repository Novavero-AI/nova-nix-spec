/-! Metamath's proof rule as an inductive definition, a checker as a function, and
the proof that the checker only accepts what the rule derives.

`Provable` is section 4.1 of the Metamath book, on a database already parsed into
frames. Parsing, block scoping and the decoding of compressed proofs are outside
this file. -/
namespace Metamath

abbrev Sym := Nat
abbrev Expr := List Sym

/-- A mandatory hypothesis of an assertion. -/
inductive Hyp where
  | float (type var : Sym)
  | essential (e : Expr)
  deriving DecidableEq

def Hyp.expr : Hyp → Expr
  | .float t v => [t, v]
  | .essential e => e

/-- What citing an assertion requires and gives. -/
structure Frame where
  hyps : List Hyp
  disjoint : List (Sym × Sym)
  concl : Expr
  deriving DecidableEq

/-- What a proof may use: every active hypothesis, and every active `$d`. -/
structure Context where
  hyps : List Expr
  disjoint : List (Sym × Sym)
  deriving DecidableEq

section Rules

variable (isVar : Sym → Bool)

/-- Simultaneous replacement of the variables of `e`. -/
def subst (σ : Sym → Expr) (e : Expr) : Expr :=
  e.flatMap fun s => if isVar s then σ s else [s]

def varsIn (e : Expr) : List Sym := e.filter isVar

def declared (ctx : Context) (a b : Sym) : Bool :=
  ctx.disjoint.contains (a, b) || ctx.disjoint.contains (b, a)

/-- Each `$d` of `A` holds of the substitution: the two expressions share no
variable, and each pair of their variables has a `$d` in the proof's context. -/
def dvOk (ctx : Context) (A : Frame) (σ : Sym → Expr) : Bool :=
  A.disjoint.all fun p =>
    (varsIn isVar (σ p.1)).all fun a =>
      (varsIn isVar (σ p.2)).all fun b => a != b && declared ctx a b

/-- The rule itself: a proof may use a hypothesis, or cite an earlier assertion
under a substitution that meets its hypotheses and its `$d` conditions. -/
inductive Provable (db : List Frame) (ctx : Context) : Expr → Prop
  | hyp {e : Expr} : e ∈ ctx.hyps → Provable db ctx e
  | cite {A : Frame} {σ : Sym → Expr} : A ∈ db →
      (∀ h ∈ A.hyps, Provable db ctx (subst isVar σ h.expr)) →
      dvOk isVar ctx A σ = true →
      Provable db ctx (subst isVar σ A.concl)

def floatVars : List Hyp → List Sym
  | [] => []
  | .float _ v :: hs => v :: floatVars hs
  | .essential _ :: hs => floatVars hs

/-- Each variable has one `$f`, and none appears in a `$e` ahead of its `$f`.
Scoping gives every frame this shape, which is what lets a one-pass match work. -/
def ordered : List Hyp → Bool
  | [] => true
  | .float _ v :: hs => !(floatVars hs).contains v && ordered hs
  | .essential h :: hs =>
    h.all (fun s => !isVar s || !(floatVars hs).contains s) && ordered hs

def update (σ : Sym → Expr) (v : Sym) (e : Expr) : Sym → Expr :=
  fun s => if s = v then e else σ s

/-- Matches hypotheses against stack entries, oldest first, as `mmcheck` does. -/
def unify (σ : Sym → Expr) : List Hyp → List Expr → Option (Sym → Expr)
  | [], [] => some σ
  | .float t v :: hs, (s :: rest) :: es =>
    if s = t ∧ isVar t = false ∧ isVar v = true then unify (update σ v rest) hs es else none
  | .essential h :: hs, e :: es =>
    if subst isVar σ h = e then unify σ hs es else none
  | _, _ => none

/-- A compressed proof reuses a subproof by saving and loading its result. -/
inductive Step where
  | hyp (i : Nat)
  | cite (i : Nat)
  | save
  | load (i : Nat)
  deriving DecidableEq

structure State where
  stack : List Expr
  saved : List Expr

def step (db : List Frame) (ctx : Context) (S : State) : Step → Option State
  | .hyp i => (ctx.hyps[i]?).map fun e => { S with stack := e :: S.stack }
  | .load i => (S.saved[i]?).map fun e => { S with stack := e :: S.stack }
  | .save =>
    match S.stack with
    | [] => none
    | e :: _ => some { S with saved := S.saved ++ [e] }
  | .cite i =>
    match db[i]? with
    | none => none
    | some A =>
      if S.stack.length < A.hyps.length ∨ ordered isVar A.hyps = false then none
      else
        match unify isVar (fun _ => []) A.hyps (S.stack.take A.hyps.length).reverse with
        | none => none
        | some τ =>
          if dvOk isVar ctx A τ = true then
            some { S with stack := subst isVar τ A.concl :: S.stack.drop A.hyps.length }
          else none

def run (db : List Frame) (ctx : Context) (S : State) : List Step → Option State
  | [] => some S
  | s :: rest =>
    match step isVar db ctx S s with
    | none => none
    | some T => run db ctx T rest

/-- A proof checks when it leaves exactly the claimed expression on the stack. -/
def verify (db : List Frame) (ctx : Context) (proof : List Step) (concl : Expr) : Bool :=
  match run isVar db ctx ⟨[], []⟩ proof with
  | some ⟨[e], _⟩ => e == concl
  | _ => false

/-! ### Soundness of one citation -/

theorem subst_congr {σ τ : Sym → Expr} {e : Expr}
    (h : ∀ s ∈ e, isVar s = true → τ s = σ s) : subst isVar τ e = subst isVar σ e := by
  induction e with
  | nil => rfl
  | cons s rest ih =>
    have hr := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [subst, List.flatMap_cons] at hr ⊢
    rw [hr]
    by_cases hv : isVar s = true
    · simp [hv, h s (List.mem_cons_self) hv]
    · simp [hv]

/-- `unify` only touches the variables of the `$f` hypotheses it passes. -/
theorem unify_other {σ τ : Sym → Expr} {hs : List Hyp} {es : List Expr} {s : Sym}
    (h : unify isVar σ hs es = some τ) (hs_not : s ∉ floatVars hs) : τ s = σ s := by
  induction hs generalizing σ es with
  | nil =>
    cases es with
    | nil => simp only [unify, Option.some.injEq] at h; rw [h]
    | cons _ _ => simp [unify] at h
  | cons hd tl ih =>
    cases hd with
    | float t v =>
      cases es with
      | nil => simp [unify] at h
      | cons e es =>
        cases e with
        | nil => simp [unify] at h
        | cons x rest =>
          simp only [unify] at h
          split at h
          · simp only [floatVars, List.mem_cons, not_or] at hs_not
            have := ih h hs_not.2
            rw [this]
            simp [update, hs_not.1]
          · simp at h
    | essential e0 =>
      cases es with
      | nil => simp [unify] at h
      | cons e es =>
        simp only [unify] at h
        split at h
        · exact ih h hs_not
        · simp at h

/-- A match on ordered hypotheses is a substitution meeting every one of them. -/
theorem unify_sound {P : Expr → Prop} {σ τ : Sym → Expr} {hs : List Hyp} {es : List Expr}
    (ho : ordered isVar hs = true) (h : unify isVar σ hs es = some τ)
    (hes : ∀ e ∈ es, P e) : ∀ x ∈ hs, P (subst isVar τ x.expr) := by
  induction hs generalizing σ es with
  | nil => simp
  | cons hd tl ih =>
    cases hd with
    | float t v =>
      cases es with
      | nil => simp [unify] at h
      | cons e es =>
        cases e with
        | nil => simp [unify] at h
        | cons x rest =>
          simp only [unify] at h
          split at h
          · rename_i hc
            obtain ⟨rfl, ht, hv⟩ := hc
            simp only [ordered, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
              decide_eq_false_iff_not] at ho
            have tail := ih ho.2 h fun e he => hes e (List.mem_cons_of_mem _ he)
            intro y hy
            rcases List.mem_cons.mp hy with rfl | hy
            · have hτ : τ v = rest := by
                have := unify_other isVar h ho.1
                rw [this]
                simp [update]
              have : subst isVar τ (Hyp.float x v).expr = x :: rest := by
                simp [subst, Hyp.expr, ht, hv, hτ]
              rw [this]
              exact hes _ List.mem_cons_self
            · exact tail y hy
          · simp at h
    | essential e0 =>
      cases es with
      | nil => simp [unify] at h
      | cons e es =>
        simp only [unify] at h
        split at h
        · rename_i hc
          simp only [ordered, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
            Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at ho
          have tail := ih ho.2 h fun e he => hes e (List.mem_cons_of_mem _ he)
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · have same : subst isVar τ e0 = subst isVar σ e0 := by
              apply subst_congr
              intro s hs hv
              apply unify_other isVar h
              rcases ho.1 s hs with hf | hn
              · simp [hf] at hv
              · exact hn
            have : subst isVar τ (Hyp.essential e0).expr = e := by
              simp only [Hyp.expr]
              rw [same]
              exact hc
            rw [this]
            exact hes _ List.mem_cons_self
          · exact tail y hy
        · simp at h

/-! ### Soundness of a whole proof -/

/-- Everything on the stack, and everything saved, is provable. -/
def Good (db : List Frame) (ctx : Context) (S : State) : Prop :=
  (∀ e ∈ S.stack, Provable isVar db ctx e) ∧ (∀ e ∈ S.saved, Provable isVar db ctx e)

theorem step_good {db : List Frame} {ctx : Context} {S T : State} {s : Step}
    (hg : Good isVar db ctx S) (h : step isVar db ctx S s = some T) :
    Good isVar db ctx T := by
  cases s with
  | hyp i =>
    simp only [step, Option.map_eq_some_iff] at h
    obtain ⟨e, he, rfl⟩ := h
    refine ⟨?_, hg.2⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact .hyp (List.mem_of_getElem? he)
    · exact hg.1 x hx
  | load i =>
    simp only [step, Option.map_eq_some_iff] at h
    obtain ⟨e, he, rfl⟩ := h
    refine ⟨?_, hg.2⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hg.2 _ (List.mem_of_getElem? he)
    · exact hg.1 x hx
  | save =>
    simp only [step] at h
    split at h
    · simp at h
    · rename_i e rest hs
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨hg.1, ?_⟩
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hg.2 x hx
      · have hx : x = e := by simpa using hx
        subst hx
        exact hg.1 _ (by simp [hs])
  | cite i =>
    simp only [step] at h
    split at h
    · simp at h
    · rename_i A hA
      split at h
      · simp at h
      · rename_i hn
        have ho : ordered isVar A.hyps = true := by
          by_cases hc : ordered isVar A.hyps = true
          · exact hc
          · exact absurd (Or.inr (by simpa using hc)) hn
        split at h
        · simp at h
        · rename_i τ hu
          split at h
          · rename_i hd
            simp only [Option.some.injEq] at h
            subst h
            have hargs : ∀ e ∈ (S.stack.take A.hyps.length).reverse,
                Provable isVar db ctx e := fun e he =>
              hg.1 e (List.mem_of_mem_take (List.mem_reverse.mp he))
            have hyps := unify_sound isVar ho hu hargs
            refine ⟨?_, hg.2⟩
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact .cite (List.mem_of_getElem? hA) hyps hd
            · exact hg.1 x (List.mem_of_mem_drop hx)
          · simp at h

theorem run_good {db : List Frame} {ctx : Context} {S T : State} {proof : List Step}
    (hg : Good isVar db ctx S) (h : run isVar db ctx S proof = some T) :
    Good isVar db ctx T := by
  induction proof generalizing S with
  | nil =>
    simp only [run, Option.some.injEq] at h
    exact h ▸ hg
  | cons s rest ih =>
    simp only [run] at h
    split at h
    · simp at h
    · rename_i U hu
      exact ih (step_good isVar hg hu) h

/-- The checker only accepts what the rule derives. -/
theorem verify_sound {db : List Frame} {ctx : Context} {proof : List Step} {concl : Expr}
    (h : verify isVar db ctx proof concl = true) : Provable isVar db ctx concl := by
  unfold verify at h
  split at h
  · rename_i e saved hr
    have hg := run_good isVar (S := ⟨[], []⟩) ⟨by simp, by simp⟩ hr
    have he : e = concl := by simpa using h
    exact he ▸ hg.1 e (by simp)
  · simp at h

/-! ### Soundness of a whole database -/

def mandatoryVars (F : Frame) : List Sym :=
  floatVars F.hyps

/-- A proof's context adds to its theorem's frame only type hypotheses for
variables the theorem does not mention. So a theorem cannot be proved from a `$e`
its frame does not list, and every `$d` among its variables is in its frame. -/
def conforms (F : Frame) (ctx : Context) : Bool :=
  (ctx.hyps.all fun e =>
    (F.hyps.map Hyp.expr).contains e ||
      match e with
      | [t, v] => !isVar t && isVar v && !(mandatoryVars F).contains v
      | _ => false) &&
  (ctx.disjoint.all fun p =>
    !((mandatoryVars F).contains p.1 && (mandatoryVars F).contains p.2) ||
      F.disjoint.contains p)

/-- A database is valid when each `$p` has a proof from the statements before it. -/
inductive Valid : List Frame → Prop
  | nil : Valid []
  | ax {db : List Frame} (F : Frame) : Valid db → Valid (db ++ [F])
  | thm {db : List Frame} (F : Frame) (ctx : Context) : Valid db →
      conforms isVar F ctx = true → Provable isVar db ctx F.concl → Valid (db ++ [F])

inductive Entry where
  | ax (F : Frame)
  | thm (F : Frame) (ctx : Context) (proof : List Step)

def Entry.frame : Entry → Frame
  | .ax F => F
  | .thm F _ _ => F

def check (db : List Frame) : List Entry → Bool
  | [] => true
  | .ax F :: rest => check (db ++ [F]) rest
  | .thm F ctx proof :: rest =>
    conforms isVar F ctx && verify isVar db ctx proof F.concl && check (db ++ [F]) rest

/-- An accepted database is a valid one. -/
theorem check_sound {db : List Frame} {entries : List Entry}
    (hv : Valid isVar db) (h : check isVar db entries = true) :
    Valid isVar (db ++ entries.map Entry.frame) := by
  induction entries generalizing db with
  | nil => simpa using hv
  | cons e rest ih =>
    cases e with
    | ax F =>
      simp only [check] at h
      have := ih (.ax F hv) h
      simpa [Entry.frame] using this
    | thm F ctx proof =>
      simp only [check, Bool.and_eq_true] at h
      have := ih (.thm F ctx hv h.1.1 (verify_sound isVar h.1.2)) h.2
      simpa [Entry.frame] using this

end Rules

/-! ### The checker refuses things, so the theorems cannot be vacuous -/

/-- Symbols from 100 up are variables. -/
def var (s : Sym) : Bool := decide (100 ≤ s)

def wff : Sym := 0
def turnstile : Sym := 1
def arrow : Sym := 2
def P : Sym := 100
def Q : Sym := 101

/-- `wff ( P -> Q )`, flattened to `wff P -> Q`. -/
def wi : Frame := ⟨[.float wff P, .float wff Q], [], [wff, P, arrow, Q]⟩

def mp : Frame :=
  ⟨[.float wff P, .float wff Q, .essential [turnstile, P], .essential [turnstile, P, arrow, Q]],
    [], [turnstile, Q]⟩

def demoDb : List Frame := [wi, mp]

/-- What the proof may use: `|- P` and `|- P -> Q`. -/
def demoCtx : Context :=
  ⟨[[wff, P], [wff, Q], [turnstile, P], [turnstile, P, arrow, Q]], []⟩

def goodProof : List Step := [.hyp 0, .hyp 1, .hyp 2, .hyp 3, .cite 1]

theorem good_accepted : verify var demoDb demoCtx goodProof [turnstile, Q] = true := by
  decide

theorem good_is_provable : Provable var demoDb demoCtx [turnstile, Q] :=
  verify_sound var good_accepted

/-- Hypotheses in the wrong order. -/
theorem swapped_refused :
    verify var demoDb demoCtx [.hyp 0, .hyp 1, .hyp 3, .hyp 2, .cite 1] [turnstile, Q] = false := by
  decide

/-- The right proof of the wrong claim. -/
theorem wrong_claim_refused :
    verify var demoDb demoCtx goodProof [turnstile, P] = false := by
  decide

/-- A claim that is only a prefix of what was proved. -/
theorem prefix_refused :
    verify var demoDb demoCtx [.hyp 3] [turnstile, P] = false := by
  decide

/-- A step left on the stack. -/
theorem leftover_refused :
    verify var demoDb demoCtx (.hyp 0 :: goodProof) [turnstile, Q] = false := by
  decide

/-- A citation out of range is refused, and a saved result can be reused. -/
theorem save_and_range :
    verify var demoDb demoCtx [.hyp 2, .cite 7] [turnstile, P] = false ∧
    verify var demoDb demoCtx [.hyp 2, .save] [turnstile, P] = true := by
  decide

#print axioms verify_sound
#print axioms check_sound
#print axioms good_is_provable

end Metamath
