import OmegaJCS.Decode

-- prove in same file as def by copying snippet
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
decreasing_by simp only [List.length_cons]; cases rest <;> simp [Nat.succ_le_iff, Nat.zero_le]

example (acc rest) :
    parseStringCharsGo ('\\' :: '"' :: rest) acc = parseStringCharsGo rest (acc ++ ['"']) := by
  simp only [parseStringCharsGo]
  rfl

end OmegaJCS.Test
