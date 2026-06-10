import OmegaJCS.Decode

namespace OmegaJCS

#check parseStringCharsGo ('\\' :: '"' :: ([] : List Char)) []
example (acc rest : List Char) :
    parseStringCharsGo ('\\' :: '"' :: rest) acc = parseStringCharsGo rest (acc ++ ['"']) := by
  simp only [parseStringCharsGo]
  rfl

end OmegaJCS
