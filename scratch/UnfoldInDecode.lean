import OmegaJCS.Decode

-- copy partial def locally
namespace T

partial def parseStringCharsGo (s : List Char) (acc : List Char) : Option (String × List Char) :=
  match s with
  | [] => none
  | '"' :: rest => some (String.ofList acc, rest)
  | '\\' :: rest =>
      match rest with
      | '"' :: r => parseStringCharsGo r (acc ++ ['"'])
      | _ => none
  | c :: rest => parseStringCharsGo rest (acc ++ [c])

example (acc rest) :
    parseStringCharsGo ('\\' :: '"' :: rest) acc = parseStringCharsGo rest (acc ++ ['"']) := by
  unfold parseStringCharsGo
  rfl

end T
