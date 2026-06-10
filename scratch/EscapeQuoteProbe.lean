import OmegaJCS.Decode
import OmegaJCS.Encode

namespace OmegaJCS

example (acc rest : List Char) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  dsimp [escapeCharList, escapeChar, parseStringChars, parseStringCharsFuelBound,
    parseStringCharsGoFuel]
  have ht : ("\\\"").toList = ['\\', '"'] := rfl
  simp only [ht, List.cons_append, parseStringCharsGoFuel]
  simp only [List.nil_append, parseStringCharsGo]

end OmegaJCS
