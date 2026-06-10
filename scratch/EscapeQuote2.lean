import OmegaJCS.Decode

namespace OmegaJCS

example (acc rest) :
    parseStringCharsGo ('\\' :: '"' :: rest) acc = parseStringCharsGo rest (acc ++ ['"']) := by
  simp [parseStringCharsGo]

example (acc rest) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  dsimp [escapeCharList, escapeChar, parseStringChars, parseStringCharsFuelBound,
    parseStringCharsGoFuel]
  have ht : ("\\\"").toList = ['\\', '"'] := rfl
  simp only [ht, List.cons_append, List.nil_append, List.length_cons, List.length_nil,
    parseStringCharsGoFuel]
  simp [parseStringCharsGo]

end OmegaJCS
