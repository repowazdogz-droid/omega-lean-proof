import OmegaJCS.Decode

open OmegaJCS

theorem parseStringCharsGoFuel_mono (m n : Nat) (s acc : List Char) (h : m ≤ n) :
    parseStringCharsGoFuel (m + 1) s acc = parseStringCharsGoFuel (n + 1) s acc := by
  induction h with
  | refl => rfl
  | step h ih =>
    conv =>
      lhs; unfold parseStringCharsGoFuel
      rhs; unfold parseStringCharsGoFuel
    match s with
    | [] => rfl
    | '"' :: rest => rfl
    | '\\' :: rest =>
      match rest with
      | '"' :: r => exact ih r (acc ++ ['"'])
      | '\\' :: r => exact ih r (acc ++ ['\\'])
      | 'b' :: r => exact ih r (acc ++ [Char.ofNat 0x08])
      | 'f' :: r => exact ih r (acc ++ [Char.ofNat 0x0C])
      | 'n' :: r => exact ih r (acc ++ [Char.ofNat 0x0A])
      | 'r' :: r => exact ih r (acc ++ [Char.ofNat 0x0D])
      | 't' :: r => exact ih r (acc ++ [Char.ofNat 0x09])
      | 'u' :: r =>
        cases parseHex4 r with
        | none => rfl
        | some p => exact ih p.2 (acc ++ [Char.ofNat p.1])
      | _ :: _ => rfl
    | c :: rest => exact ih rest (acc ++ [c])
