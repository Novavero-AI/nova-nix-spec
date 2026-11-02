/-- Adds 1 + 2 + ... + n the slow way, one step at a time. -/
def sum : Nat → Nat
  | 0 => 0
  | n + 1 => sum n + (n + 1)

theorem gauss (n : Nat) : sum n * 2 = n * (n + 1) := by
  trace_state
  induction n with
  | zero =>
    trace_state
    rfl
  | succ n ih =>
    trace_state
    rw [sum, Nat.add_mul, ih]
    trace_state
    rw [Nat.mul_comm n, ← Nat.mul_add]

#print axioms gauss

/-- The same function with a hidden trigger at one secret input. -/
def sumEvil : Nat → Nat
  | 0 => 0
  | n + 1 => if n = 31337 then sumEvil n else sumEvil n + (n + 1)

#eval (List.range 10000).all fun n => sumEvil n * 2 == n * (n + 1)
#eval sumEvil 31338 * 2 == 31338 * (31338 + 1)

theorem gaussEvil (n : Nat) : sumEvil n * 2 = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumEvil]
    split
    · rw [ih]
      trace_state
      rw [Nat.mul_comm n, ← Nat.mul_add]
    · rw [Nat.add_mul, ih, Nat.mul_comm n, ← Nat.mul_add]
