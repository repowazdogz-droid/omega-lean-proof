import OmegaJCS.Decode

open OmegaJCS

theorem parseStringCharsGoFuel_mono_ge (fuel extra : Nat) (s acc : List Char)
    (hle : extra ≤ fuel) (hpos : 0 < extra) :
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
        match s with
        | [] => simp [parseStringCharsGoFuel]
        | '"' :: rest => simp [parseStringCharsGoFuel]
        | '\\' :: rest =>
          match rest with
          | [] => simp [parseStringCharsGoFuel]
          | '"' :: r => simp [parseStringCharsGoFuel]; exact ih (e + 1) r (acc ++ ['"']) hef (by omega)
          | '\\' :: r => simp [parseStringCharsGoFuel]; exact ih (e + 1) r (acc ++ ['\\']) hef (by omega)
          | 'b' :: r => simp [parseStringCharsGoFuel]; exact ih (e + 1) r (acc ++ [Char.ofNat 0x08]) hef (by omega)
          | 'f' :: r => simp [parseStringCharsGoFuel]; exact ih (e + 1) r (acc ++ [Char.ofNat 0x0C]) hef (by omega)
          | 'n' :: r => simp [parseStringCharsGoFuel]; exact ih (e + 1) r (acc ++ [Char.ofNat 0x0A]) hef (by omega)
          | 'r' :: r => simp [parseStringCharsGoFuel]; exact ih (e + 1) r (acc ++ [Char.ofNat 0x0D]) hef (by omega)
          | 't' :: r => simp [parseStringCharsGoFuel]; exact ih (e + 1) r (acc ++ [Char.ofNat 0x09]) hef (by omega)
          | 'u' :: r =>
            simp [parseStringCharsGoFuel]
            cases parseHex4 r with
            | none => rfl
            | some p => exact ih (e + 1) p.2 (acc ++ [Char.ofNat p.1]) hef (by omega)
          | _ :: _ => simp [parseStringCharsGoFuel]
        | c :: rest =>
          simp [parseStringCharsGoFuel]
          exact ih (e + 1) rest (acc ++ [c]) hef (by omega)

example (acc rest : List Char) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  dsimp [escapeCharList, escapeChar, parseStringChars, parseStringCharsFuelBound, parseStringCharsGoFuel]
  have ht : ("\\\"").toList = ['\\', '"'] := rfl
  simp only [ht, List.cons_append, List.nil_append, parseStringCharsGoFuel]
  have hlen : ('\\' :: '"' :: rest).length * 6 = (2 + rest.length) * 6 := by simp; omega
  rw [hlen]
  exact parseStringCharsGoFuel_mono_ge ((2 + rest.length) * 6) (rest.length * 6 + 1) rest
    (acc ++ ['"']) (by omega) (by omega)
