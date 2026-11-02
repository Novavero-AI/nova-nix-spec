-- Attempt 1: prove False by calling yourself.
theorem loop : False := loop

-- Attempt 2: a type that contains a function out of itself.
inductive Bad where
  | mk : (Bad → False) → Bad

-- An honest proof by induction, written as plain recursion.
theorem zero_add' : (n : Nat) → 0 + n = n
  | 0 => rfl
  | n + 1 => congrArg Nat.succ (zero_add' n)

#print axioms zero_add'
#check @Nat.rec
