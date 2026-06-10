import OmegaJCS.Decode

open OmegaJCS

theorem parseStringCharsGoFuel_mono_ge (fuel extra : Nat) (s acc : List Char)
    (hle : extra ≤ fuel) (hpos : 0 < extra) :
    parseStringCharsGoFuel fuel s acc = parseStringCharsGoFuel extra s acc := by
  induction fuel generalizing extra s acc with
  | zero =>
    match extra with
    | 0 => exact (Nat.pos_iff_ne_zero.mp hpos rfl).elim
    | _ + 1 => omega
  | succ f ih =>
    match extra with
    | 0 => exact (Nat.pos_iff_ne_zero.mp hpos rfl).elim
    | succ e =>
      have he : e ≤ f := Nat.le_of_succ_le_succ hle
      rcases Nat.eq_or_lt_of_le he with rfl | hlt
      · rfl
      · unfold parseStringCharsGoFuel
        match s with
        | [] => rfl
        | '"' :: rest => rfl
        | '\\' :: rest =>
          match rest with
          | '"' :: r => exact ih e (by omega) r (acc ++ ['"'])
          | '\\' :: r => exact ih e (by omega) r (acc ++ ['\\'])
          | 'b' :: r => exact ih e (by omega) r (acc ++ [Char.ofNat 0x08])
          | 'f' :: r => exact ih e (by omega) r (acc ++ [Char.ofNat 0x0C])
          | 'n' :: r => exact ih e (by omega) r (acc ++ [Char.ofNat 0x0A])
          | 'r' :: r => exact ih e (by omega) r (acc ++ [Char.ofNat 0x0D])
          | 't' :: r => exact ih e (by omega) r (acc ++ [Char.ofNat 0x09])
          | 'u' :: r =>
            cases parseHex4 r with
            | none => rfl
            | some p => exact ih e (by omega) p.2 (acc ++ [Char.ofNat p.1])
          | _ :: _ => rfl
        | c :: rest =>
          match f with
          | 0 => rfl
          | _ + 1 => exact ih e (by omega) rest (acc ++ [c])

theorem parseStringCharsGoFuel_mono (m n : Nat) (s acc : List Char) (h : m ≤ n) :
    parseStringCharsGoFuel (m + 1) s acc = parseStringCharsGoFuel (n + 1) s acc := by
  have hpos : 0 < m + 1 := by omega
  have hle : m + 1 ≤ n + 1 := Nat.add_le_add_right h 1
  exact parseStringCharsGoFuel_mono_ge (n + 1) (m + 1) s acc hle hpos
