import OmegaJCS.Decode
import OmegaJCS.Encode

open OmegaJCS

theorem parseStringCharsGoFuel_mono_ge (fuel extra : Nat) (s acc : List Char)
    (hle : extra ≤ fuel) (hpos : 0 < extra) (h7 : 7 ≤ extra) :
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
        have h7' : 7 ≤ e + 1 := h7
        match s with
        | [] => simp [parseStringCharsGoFuel]
        | '"' :: rest => simp [parseStringCharsGoFuel]
        | '\\' :: rest =>
          match rest with
          | [] => simp [parseStringCharsGoFuel]
          | '"' :: r => simp [parseStringCharsGoFuel]; exact ih (e + 1) r (acc ++ ['"']) hef (Nat.succ_pos e) h7'
          | '\\' :: r => simp [parseStringCharsGoFuel]; exact ih (e + 1) r (acc ++ ['\\']) hef (Nat.succ_pos e) h7'
          | 'b' :: r => simp [parseStringCharsGoFuel]; exact ih (e + 1) r (acc ++ [Char.ofNat 0x08]) hef (Nat.succ_pos e) h7'
          | 'f' :: r => simp [parseStringCharsGoFuel]; exact ih (e + 1) r (acc ++ [Char.ofNat 0x0C]) hef (Nat.succ_pos e) h7'
          | 'n' :: r => simp [parseStringCharsGoFuel]; exact ih (e + 1) r (acc ++ [Char.ofNat 0x0A]) hef (Nat.succ_pos e) h7'
          | 'r' :: r => simp [parseStringCharsGoFuel]; exact ih (e + 1) r (acc ++ [Char.ofNat 0x0D]) hef (Nat.succ_pos e) h7'
          | 't' :: r => simp [parseStringCharsGoFuel]; exact ih (e + 1) r (acc ++ [Char.ofNat 0x09]) hef (Nat.succ_pos e) h7'
          | 'u' :: r =>
            simp [parseStringCharsGoFuel]
            cases parseHex4 r with
            | none => rfl
            | some p => exact ih (e + 1) p.2 (acc ++ [Char.ofNat p.1]) hef (Nat.succ_pos e) h7'
          | _ :: _ => simp [parseStringCharsGoFuel]
        | c :: rest =>
          simp [parseStringCharsGoFuel]
          exact ih (e + 1) rest (acc ++ [c]) hef (Nat.succ_pos e) h7'

private theorem parseStringChars_escapeCharList_quote_nonempty (acc rest : List Char) (h : rest ≠ []) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  dsimp [escapeCharList, escapeChar, parseStringChars, parseStringCharsFuelBound, parseStringCharsGoFuel]
  have ht : ("\\\"").toList = ['\\', '"'] := rfl
  simp only [ht, List.cons_append, List.nil_append, parseStringCharsGoFuel]
  have hlen : ('\\' :: '"' :: rest).length * 6 = (2 + rest.length) * 6 := by simp; omega
  rw [hlen]
  have h7 : 7 ≤ rest.length * 6 + 1 := by
    rcases rest with ⟨_ | ⟨c, rest'⟩⟩
    · exact absurd rfl h
    · simp [List.length_cons]; omega
  exact parseStringCharsGoFuel_mono_ge ((2 + rest.length) * 6) (rest.length * 6 + 1) rest
    (acc ++ ['"']) (by omega) (by omega) h7

private theorem parseStringChars_escapeCharList_quote_nil (acc : List Char) :
    parseStringChars (escapeCharList '"' ++ []) acc =
      parseStringChars [] (acc ++ ['"']) := by
  dsimp [escapeCharList, escapeChar, parseStringChars, parseStringCharsFuelBound, parseStringCharsGoFuel]
  have ht : ("\\\"").toList = ['\\', '"'] := rfl
  simp only [ht, List.cons_append, List.nil_append, List.length_nil, parseStringCharsGoFuel]

private theorem parseStringChars_escapeCharList_quote (acc rest : List Char) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  cases rest with
  | nil => exact parseStringChars_escapeCharList_quote_nil acc
  | cons c rest => exact parseStringChars_escapeCharList_quote_nonempty acc (c :: rest) (by intro h; cases h)
