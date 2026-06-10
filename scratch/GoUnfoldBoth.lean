import OmegaJCS.Decode

namespace OmegaJCS

example (acc rest) :
    parseStringCharsGo ('\\' :: '"' :: rest) acc = parseStringCharsGo rest (acc ++ ['"']) := by
  unfold parseStringCharsGo
  rfl

end OmegaJCS
