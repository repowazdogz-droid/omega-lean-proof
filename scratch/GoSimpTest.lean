import OmegaJCS.Decode

namespace OmegaJCS

example (acc rest) :
    parseStringCharsGo ('\\' :: '"' :: rest) acc = parseStringCharsGo rest (acc ++ ['"']) := by
  simp [parseStringCharsGo]

example (acc rest) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  simp [parseStringChars, escapeCharList, escapeChar, parseStringCharsGo,
    List.cons_append, String.toList]

end OmegaJCS
