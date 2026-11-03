/-! hex0 as a pure function, written so that proofs can be about it. Two hex
digits make a byte, and `#` or `;` starts a comment that runs to the end of the
line. This is the rule the Windows PE32 seed follows. The upstream Linux x86
seed also takes `G` and `g` as a digit worth 16. -/
namespace Hex0

/-- A hex digit's value, if the byte is one. -/
def hexValue (c : UInt8) : Option UInt8 :=
  if c >= 48 && c <= 57 then some (c - 48)
  else if c >= 97 && c <= 102 then some (c - 87)
  else if c >= 65 && c <= 70 then some (c - 55)
  else none

/-- Decoder state: a pending high digit, whether we are in a comment, and the
output so far, newest byte first. -/
structure St where
  high : Option UInt8 := none
  comment : Bool := false
  out : List UInt8 := []

/-- Handles one input byte. -/
def step (s : St) (c : UInt8) : St :=
  if c == 10 then { s with comment := false }
  else if s.comment then s
  else if c == 35 || c == 59 then { s with comment := true }
  else match hexValue c with
    | none => s
    | some v =>
      match s.high with
      | none => { s with high := some v }
      | some h => { s with high := none, out := (h * 16 + v) :: s.out }

/-- hex0 as a pure function: text in, bytes out. -/
def decode (input : List UInt8) : List UInt8 :=
  (input.foldl step {}).out.reverse


/-- Empty input gives empty output. -/
theorem decode_nil : decode [] = [] := rfl

/-- Inside a comment, any byte except a newline changes nothing. -/
theorem comment_ignores (s : St) (c : UInt8)
    (hc : s.comment = true) (hn : (c == 10) = false) : step s c = s := by
  simp [step, hc, hn]

/-- The text "4D" decodes to the single byte 0x4D. -/
example : decode [52, 68] = [0x4D] := by decide

/-- Inside a comment, any run of non-newline bytes changes nothing. -/
theorem foldl_in_comment (s : St) (body : List UInt8)
    (hc : s.comment = true) (hb : ∀ c, c ∈ body -> (c == 10) = false) :
    body.foldl step s = s := by
  induction body with
  | nil => rfl
  | cons c rest ih =>
    rw [List.foldl_cons, comment_ignores s c hc (hb c List.mem_cons_self)]
    exact ih (fun x hx => hb x (List.mem_cons_of_mem c hx))

/-- A whole comment line leaves the decoder exactly where it started. -/
theorem comment_line (s : St) (body : List UInt8)
    (hc : s.comment = false) (hb : ∀ c, c ∈ body -> (c == 10) = false) :
    (35 :: body ++ [10]).foldl step s = s := by
  have open_comment : step s 35 = { s with comment := true } := by
    simp [step, hc]
  have inside := foldl_in_comment { s with comment := true } body rfl hb
  simp only [List.cons_append, List.foldl_cons, List.foldl_append, List.foldl_nil]
  rw [open_comment, inside]
  cases s
  simp_all [step]

/-- Inserting a comment line at any point outside a comment never changes the
output, for every possible input. -/
theorem decode_comment_line (pre post body : List UInt8)
    (hc : (pre.foldl step {}).comment = false)
    (hb : ∀ c, c ∈ body -> (c == 10) = false) :
    decode (pre ++ (35 :: body ++ [10]) ++ post) = decode (pre ++ post) := by
  have line := comment_line _ body hc hb
  rw [List.foldl_append] at line
  simp only [decode, List.foldl_append]
  rw [line]

end Hex0
