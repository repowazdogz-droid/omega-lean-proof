import OmegaJCS.Decode

open OmegaJCS

theorem parseStringCharsGoFuel_quote_rest (rest acc : List Char) :
    parseStringCharsGoFuel ((2 + rest.length) * 6) rest (acc ++ ['"']) =
    parseStringCharsGoFuel (rest.length * 6 + 1) rest (acc ++ ['"']) := by
  induction rest generalizing acc with
  | nil =>
    simp only [List.length_nil, parseStringCharsGoFuel]
  | cons c rest ih =>
    simp only [List.length_cons, parseStringCharsGoFuel]
    match c with
    | '"' => simp [parseStringCharsGoFuel]
    | '\\' =>
      simp only [parseStringCharsGoFuel]
      match rest with
      | [] => simp [parseStringCharsGoFuel]
      | '"' :: r => exact ih (acc ++ ['"'] ++ ['"'])  -- wrong acc
      | _ => sorry
    | c => exact ih (acc ++ ['"'] ++ [c])

example (acc rest : List Char) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  dsimp [escapeCharList, escapeChar, parseStringChars, parseStringCharsFuelBound, parseStringCharsGoFuel]
  have ht : ("\\\"").toList = ['\\', '"'] := rfl
  simp only [ht, List.cons_append, List.nil_append, parseStringCharsGoFuel]
  have hlen : ('\\' :: '"' :: rest).length * 6 = (2 + rest.length) * 6 := by simp; omega
  rw [hlen]
  exact parseStringCharsGoFuel_quote_rest rest acc
