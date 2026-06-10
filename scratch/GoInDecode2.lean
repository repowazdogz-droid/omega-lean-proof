import OmegaJCS.Types
import OmegaJCS.Encode

namespace OmegaJCS.Test

def parseStringCharsGo (s : List Char) (acc : List Char) : Option (String × List Char) :=
  match s with
  | [] => none
  | '"' :: rest => some (String.ofList acc, rest)
  | '\\' :: rest =>
      match rest with
      | '"' :: r => parseStringCharsGo r (acc ++ ['"'])
      | _ => none
  | c :: rest => parseStringCharsGo rest (acc ++ [c])
termination_by s.length
decreasing_by all_goals simp only [List.length_cons]; omega

example (acc rest) :
    parseStringCharsGo ('\\' :: '"' :: rest) acc = parseStringCharsGo rest (acc ++ ['"']) := by
  unfold parseStringCharsGo
  unfold parseStringCharsGo
  rfl

end OmegaJCS.Test
