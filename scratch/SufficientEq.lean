import OmegaJCS.Decode

namespace OmegaJCS

theorem parseStringCharsGoFuel_sufficient_eq (rest acc : List Char) :
    parseStringCharsGoFuel ((rest.length + 2) * 6) rest acc =
      parseStringCharsGoFuel (rest.length * 6 + 1) rest acc := by
  induction rest generalizing acc with
  | nil => simp [parseStringCharsGoFuel]
  | cons c rest ih =>
    simp only [parseStringCharsGoFuel, List.length_cons]
    rw [show (rest.length + 1 + 2) * 6 = (rest.length + 2) * 6 + 6 by ring]
    rw [show (rest.length + 1) * 6 + 1 + 6 = (rest.length + 2) * 6 + 1 by ring]
    exact ih (acc ++ [c])

example (acc rest) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  dsimp [escapeCharList, escapeChar, parseStringChars, parseStringCharsFuelBound,
    parseStringCharsGoFuel]
  have ht : ("\\\"").toList = ['\\', '"'] := rfl
  simp only [ht, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
  simp only [parseStringCharsGoFuel]
  exact parseStringCharsGoFuel_sufficient_eq rest (acc ++ ['"'])

end OmegaJCS
