import OmegaJCS.Decode

open OmegaJCS

theorem parseStringCharsGoFuel_mono_ge (fuel extra : Nat) (s acc : List Char)
    (hle : extra ≤ fuel) (hpos : 0 < extra) (h8 : 8 ≤ extra) :
    parseStringCharsGoFuel fuel s acc = parseStringCharsGoFuel extra s acc := by
  induction fuel generalizing extra s acc with
  | zero =>
    have : extra = 0 := Nat.eq_zero_of_le_zero hle
    omega
  | succ f ih =>
    match extra with
    | 0 => omega
    | e + 1 =>
      have he : e ≤ f := Nat.le_of_succ_le_succ hle
      rcases Nat.eq_or_lt_of_le he with rfl | hlt
      · rfl
      · have hef : e + 1 ≤ f := by omega
        have h8' : 8 ≤ e + 1 := h8
        have hepos : 0 < e := by omega
        have h7e : 7 ≤ e := by omega
        match s with
        | [] => simp [parseStringCharsGoFuel]
        | '"' :: rest => simp [parseStringCharsGoFuel]
        | '\\' :: rest =>
          match rest with
          | [] => simp [parseStringCharsGoFuel]
          | '"' :: r =>
            simp [parseStringCharsGoFuel]
            exact ih e r (acc ++ ['"']) (Nat.le_of_succ_le_succ hle) hepos h7e
          | '\\' :: r =>
            simp [parseStringCharsGoFuel]
            exact ih e r (acc ++ ['\\']) (Nat.le_of_succ_le_succ hle) (by omega) (by omega)
          | 'b' :: r =>
            simp [parseStringCharsGoFuel]
            exact ih e r (acc ++ [Char.ofNat 0x08]) (Nat.le_of_succ_le_succ hle) (by omega) (by omega)
          | 'f' :: r =>
            simp [parseStringCharsGoFuel]
            exact ih e r (acc ++ [Char.ofNat 0x0C]) (Nat.le_of_succ_le_succ hle) (by omega) (by omega)
          | 'n' :: r =>
            simp [parseStringCharsGoFuel]
            exact ih e r (acc ++ [Char.ofNat 0x0A]) (Nat.le_of_succ_le_succ hle) (by omega) (by omega)
          | 'r' :: r =>
            simp [parseStringCharsGoFuel]
            exact ih e r (acc ++ [Char.ofNat 0x0D]) (Nat.le_of_succ_le_succ hle) (by omega) (by omega)
          | 't' :: r =>
            simp [parseStringCharsGoFuel]
            exact ih e r (acc ++ [Char.ofNat 0x09]) (Nat.le_of_succ_le_succ hle) (by omega) (by omega)
          | 'u' :: r =>
            simp [parseStringCharsGoFuel]
            cases parseHex4 r with
            | none => rfl
            | some p =>
              exact ih e p.2 (acc ++ [Char.ofNat p.1]) (Nat.le_of_succ_le_succ hle) hepos h7e
          | _ :: _ => simp [parseStringCharsGoFuel]
        | c :: rest =>
          simp [parseStringCharsGoFuel]
          exact ih e rest (acc ++ [c]) (Nat.le_of_succ_le_succ hle) hepos h7e
