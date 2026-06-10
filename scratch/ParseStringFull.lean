import Init.Data.Nat.Bitwise.Lemmas
import OmegaJCS.Types
import OmegaJCS.Encode
import OmegaJCS.Decode

namespace OmegaJCS

section Hex

private theorem land_f_lt16 (x : Nat) : x &&& 0xF < 16 :=
  Nat.lt_succ_iff.mpr (Nat.and_le_right (n := x) (m := 0xF))

private theorem hexDigit_spec (n : Nat) (hn : n < 16) :
    hexValue (hexDigit n) = some n := by
  revert n hn; decide +revert

private theorem hex4_recomb_small (n : Nat) (hn : n < 0x20) :
    (n >>> 12 &&& 0xF) * 4096 +
      (n >>> 8 &&& 0xF) * 256 +
      (n >>> 4 &&& 0xF) * 16 +
      (n &&& 0xF) = n := by
  revert n hn; decide +revert

private theorem hex4Lower_toList (n : Nat) :
    (hex4Lower n).toList =
      [hexDigit ((n >>> 12) &&& 0xF), hexDigit ((n >>> 8) &&& 0xF),
        hexDigit ((n >>> 4) &&& 0xF), hexDigit (n &&& 0xF)] := by
  unfold hex4Lower; simp [String.toList_ofList]

private theorem hex4Lower_parseHex4 (n : Nat) (hn : n < 0x20) (rest : List Char) :
    parseHex4 ((hex4Lower n).toList ++ rest) = some (n, rest) := by
  rw [hex4Lower_toList, List.cons_append]
  have hflat :
      hexDigit (n >>> 12 &&& 0xF) ::
        ([hexDigit (n >>> 8 &&& 0xF), hexDigit (n >>> 4 &&& 0xF), hexDigit (n &&& 0xF)] ++ rest) =
      hexDigit (n >>> 12 &&& 0xF) :: hexDigit (n >>> 8 &&& 0xF) :: hexDigit (n >>> 4 &&& 0xF) ::
        hexDigit (n &&& 0xF) :: rest := by simp [List.cons_append, List.nil_append]
  have h0 := hexDigit_spec ((n >>> 12) &&& 0xF) (land_f_lt16 _)
  have h1 := hexDigit_spec ((n >>> 8) &&& 0xF) (land_f_lt16 _)
  have h2 := hexDigit_spec ((n >>> 4) &&& 0xF) (land_f_lt16 _)
  have h3 := hexDigit_spec (n &&& 0xF) (land_f_lt16 _)
  rw [hflat]; unfold parseHex4; simp [h0, h1, h2, h3, hex4_recomb_small n hn]

end Hex

section ParseString

private theorem escapeCharList_quote : escapeCharList '"' = ['\\', '"'] := by native_decide
private theorem escapeCharList_backslash : escapeCharList '\\' = ['\\', '\\'] := by native_decide

private theorem parseStringGoFuel_nil (f : Nat) (acc : List Char) :
    parseStringCharsGoFuel f [] acc = none := by cases f <;> rfl

private theorem rest_extra_ge7 (rest : List Char) (h : rest ≠ []) : 7 ≤ rest.length * 6 + 1 := by
  cases rest with
  | nil => exact absurd rfl h
  | cons _ rest' => simp [List.length_cons]; omega

theorem parseStringCharsGoFuel_mono_ge (fuel extra : Nat) (s acc : List Char)
    (hle : extra ≤ fuel) (hpos : 0 < extra) (h7 : 7 ≤ extra) :
    parseStringCharsGoFuel fuel s acc = parseStringCharsGoFuel extra s acc := by
  induction fuel generalizing extra s acc with
  | zero =>
    have he : extra = 0 := Nat.eq_zero_of_le_zero hle
    subst he; exact absurd hpos (Nat.not_lt_zero _)
  | succ f ih =>
    cases extra with
    | zero => exact absurd hpos (Nat.not_lt_zero _)
    | succ e =>
      have hef : e ≤ f := Nat.le_of_succ_le_succ hle
      rcases Nat.eq_or_lt_of_le hef with rfl | hlt
      · rfl
      · have hele : e ≤ f := Nat.le_of_lt (Nat.lt_of_succ_lt_succ hlt)
        have h7' : 7 ≤ e + 1 := h7
        match s with
        | [] => simp [parseStringCharsGoFuel]
        | '"' :: rest => simp [parseStringCharsGoFuel]
        | '\\' :: rest =>
          match rest with
          | [] => simp [parseStringCharsGoFuel]
          | '"' :: r => simp [parseStringCharsGoFuel]; exact ih e r (acc ++ ['"']) hele (Nat.succ_pos e) h7'
          | '\\' :: r => simp [parseStringCharsGoFuel]; exact ih e r (acc ++ ['\\']) hele (Nat.succ_pos e) h7'
          | 'b' :: r => simp [parseStringCharsGoFuel]; exact ih e r (acc ++ [Char.ofNat 0x08]) hele (Nat.succ_pos e) h7'
          | 'f' :: r => simp [parseStringCharsGoFuel]; exact ih e r (acc ++ [Char.ofNat 0x0C]) hele (Nat.succ_pos e) h7'
          | 'n' :: r => simp [parseStringCharsGoFuel]; exact ih e r (acc ++ [Char.ofNat 0x0A]) hele (Nat.succ_pos e) h7'
          | 'r' :: r => simp [parseStringCharsGoFuel]; exact ih e r (acc ++ [Char.ofNat 0x0D]) hele (Nat.succ_pos e) h7'
          | 't' :: r => simp [parseStringCharsGoFuel]; exact ih e r (acc ++ [Char.ofNat 0x09]) hele (Nat.succ_pos e) h7'
          | 'u' :: r =>
            simp [parseStringCharsGoFuel]
            cases parseHex4 r with
            | none => rfl
            | some p => exact ih e p.2 (acc ++ [Char.ofNat p.1]) hele (Nat.succ_pos e) h7'
          | _ :: _ => simp [parseStringCharsGoFuel]
        | c :: rest =>
          simp [parseStringCharsGoFuel]
          exact ih e rest (acc ++ [c]) hele (Nat.succ_pos e) h7'

private theorem parseStringChars_tail_mono (rest acc : List Char) (h : rest ≠ [])
    (hfuel : Nat) (hle : rest.length * 6 + 1 ≤ hfuel) :
    parseStringCharsGoFuel hfuel rest acc =
      parseStringCharsGoFuel (rest.length * 6 + 1) rest acc :=
  parseStringCharsGoFuel_mono_ge hfuel (rest.length * 6 + 1) rest acc (by omega) (by omega)
    (rest_extra_ge7 rest h)

private theorem parseStringChars_escapeCharList_quote (acc rest : List Char) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  dsimp [parseStringChars, parseStringCharsGo, parseStringCharsFuelBound, escapeCharList, escapeChar]
  have ht : ("\\\"").toList = ['\\', '"'] := rfl
  cases rest with
  | nil =>
    simp only [ht, List.cons_append, List.nil_append, List.length_nil, parseStringCharsGoFuel,
      parseStringGoFuel_nil]
  | cons c rest' =>
    simp only [ht, List.cons_append, List.nil_append, parseStringCharsGoFuel]
    have hlen : (2 + (c :: rest').length) * 6 = ('\\' :: '"' :: c :: rest').length * 6 := by
      simp [List.length_cons]
    rw [hlen]
    exact parseStringChars_tail_mono (c :: rest') (acc ++ ['"']) (by intro h; cases h)
      _ (by simp [List.length_cons]; omega)

private theorem parseStringChars_escapeCharList_backslash (acc rest : List Char) :
    parseStringChars (escapeCharList '\\' ++ rest) acc =
      parseStringChars rest (acc ++ ['\\']) := by
  dsimp [parseStringChars, parseStringCharsGo, parseStringCharsFuelBound, escapeCharList, escapeChar]
  have ht : ("\\\\").toList = ['\\', '\\'] := rfl
  cases rest with
  | nil =>
    simp only [ht, List.cons_append, List.nil_append, List.length_nil, parseStringCharsGoFuel,
      parseStringGoFuel_nil]
  | cons c rest' =>
    simp only [ht, List.cons_append, List.nil_append, parseStringCharsGoFuel]
    have hlen : (2 + (c :: rest').length) * 6 = ('\\' :: '\\' :: c :: rest').length * 6 := by
      simp [List.length_cons]
    rw [hlen]
    exact parseStringChars_tail_mono (c :: rest') (acc ++ ['\\']) (by intro h; cases h)
      _ (by simp [List.length_cons]; omega)

private theorem parseStringChars_escapeCharList_ctrl (acc rest : List Char) (tag : Char)
    (h : tag = 'b' ∨ tag = 'f' ∨ tag = 'n' ∨ tag = 'r' ∨ tag = 't') :
    parseStringChars (['\\', tag] ++ rest) acc =
      parseStringChars rest (acc ++ [match tag with
        | 'b' => Char.ofNat 0x08 | 'f' => Char.ofNat 0x0C | 'n' => Char.ofNat 0x0A
        | 'r' => Char.ofNat 0x0D | 't' => Char.ofNat 0x09 | _ => tag]) := by
  rcases h with rfl | rfl | rfl | rfl | rfl
  all_goals
    cases rest with
    | nil =>
      dsimp [parseStringChars, parseStringCharsGo, parseStringCharsFuelBound]
      simp only [List.cons_append, List.nil_append, List.length_nil, parseStringCharsGoFuel,
        parseStringGoFuel_nil]
    | cons c rest' =>
      dsimp [parseStringChars, parseStringCharsGo, parseStringCharsFuelBound]
      simp only [List.cons_append, List.nil_append, parseStringCharsGoFuel]
      simp only [parseStringCharsGoFuel]
      have hlen : (2 + (c :: rest').length) * 6 = ('\\' :: tag :: c :: rest').length * 6 := by
        simp [List.length_cons]
      rw [hlen]
      exact parseStringChars_tail_mono (c :: rest') _ (by intro h; cases h)
        _ (by simp [List.length_cons]; omega)

private theorem parseStringChars_escapeCharList_unicode (c : Char) (acc rest : List Char)
    (hlt : c.toNat < 0x20) :
    parseStringChars (escapeCharList c ++ rest) acc =
      parseStringChars rest (acc ++ [c]) := by
  by_cases h1 : c = '"'; · subst h1; simp at hlt
  by_cases h2 : c = '\\'; · subst h2; simp at hlt
  by_cases h3 : c = Char.ofNat 0x08; · subst h3; exact parseStringChars_escapeCharList_ctrl acc rest 'b' (Or.inl rfl)
  by_cases h4 : c = Char.ofNat 0x0C; · subst h4; exact parseStringChars_escapeCharList_ctrl acc rest 'f' (Or.inr (Or.inl rfl))
  by_cases h5 : c = Char.ofNat 0x0A; · subst h5; exact parseStringChars_escapeCharList_ctrl acc rest 'n' (Or.inr (Or.inr (Or.inl rfl)))
  by_cases h6 : c = Char.ofNat 0x0D
  · subst h6; exact parseStringChars_escapeCharList_ctrl acc rest 'r' (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  by_cases h7c : c = Char.ofNat 0x09
  · subst h7c; exact parseStringChars_escapeCharList_ctrl acc rest 't' (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  dsimp [parseStringChars, parseStringCharsGo, parseStringCharsFuelBound, escapeCharList, escapeChar]
  simp only [beq_iff_eq, h1, h2, h3, h4, h5, h6, h7c, if_false, hlt, if_pos, String.append,
    String.toList, List.cons_append, List.nil_append, hex4Lower, hex4Lower_toList, parseStringCharsGoFuel]
  rw [hex4Lower_parseHex4 c.toNat (by omega) rest]
  simp only [parseStringCharsGoFuel]
  cases rest with
  | nil =>
    simp only [List.length_nil, parseStringGoFuel_nil]
  | cons d rest' =>
    have hlen : (6 + (d :: rest').length) * 6 = (escapeCharList c ++ d :: rest').length * 6 := by
      simp [escapeCharList, escapeChar, beq_iff_eq, h1, h2, h3, h4, h5, h6, h7c, if_false, hlt, if_pos,
        String.append, String.toList, List.length_cons, hex4Lower, hex4Lower_toList, List.length_append]
    rw [hlen]
    exact parseStringChars_tail_mono (d :: rest') (acc ++ [c]) (by intro h; cases h)
      _ (by simp [List.length_cons]; omega)

private theorem parseStringChars_escapeCharList_plain (c : Char) (acc rest : List Char)
    (h8 : ¬ c.toNat < 0x20) :
    parseStringChars (escapeCharList c ++ rest) acc =
      parseStringChars rest (acc ++ [c]) := by
  by_cases h1 : c = '"'; · subst h1; simp at h8
  by_cases h2 : c = '\\'; · subst h2; simp at h8
  by_cases h3 : c = Char.ofNat 0x08; · subst h3; exact parseStringChars_escapeCharList_ctrl acc rest 'b' (Or.inl rfl)
  by_cases h4 : c = Char.ofNat 0x0C; · subst h4; exact parseStringChars_escapeCharList_ctrl acc rest 'f' (Or.inr (Or.inl rfl))
  by_cases h5 : c = Char.ofNat 0x0A; · subst h5; exact parseStringChars_escapeCharList_ctrl acc rest 'n' (Or.inr (Or.inr (Or.inl rfl)))
  by_cases h6 : c = Char.ofNat 0x0D
  · subst h6; exact parseStringChars_escapeCharList_ctrl acc rest 'r' (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  by_cases h7c : c = Char.ofNat 0x09
  · subst h7c; exact parseStringChars_escapeCharList_ctrl acc rest 't' (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  dsimp [parseStringChars, parseStringCharsGo, parseStringCharsFuelBound, escapeCharList, escapeChar]
  simp only [beq_iff_eq, h1, h2, h3, h4, h5, h6, h7c, if_false, h8, if_neg, String.singleton,
    String.toList, List.cons_append, List.nil_append, parseStringCharsGoFuel]
  cases rest with
  | nil => simp only [List.length_nil, parseStringGoFuel_nil]
  | cons d rest' =>
    have hlen : (1 + (d :: rest').length) * 6 = (escapeCharList c ++ d :: rest').length * 6 := by
      simp [escapeCharList, escapeChar, beq_iff_eq, h1, h2, h3, h4, h5, h6, h7c, if_false, h8, if_neg,
        String.singleton, String.toList, List.length_cons, List.length_append]
    rw [hlen]
    exact parseStringChars_tail_mono (d :: rest') (acc ++ [c]) (by intro h; cases h)
      _ (by simp [List.length_cons]; omega)

theorem parseStringChars_escapeCharList (c : Char) (acc rest : List Char) :
    parseStringChars (escapeCharList c ++ rest) acc =
      parseStringChars rest (acc ++ [c]) := by
  match c with
  | '"' => exact parseStringChars_escapeCharList_quote acc rest
  | '\\' => exact parseStringChars_escapeCharList_backslash acc rest
  | c =>
    by_cases h8 : c = Char.ofNat 0x08
    · subst h8; exact parseStringChars_escapeCharList_ctrl acc rest 'b' (Or.inl rfl)
    by_cases h12 : c = Char.ofNat 0x0C
    · subst h12; exact parseStringChars_escapeCharList_ctrl acc rest 'f' (Or.inr (Or.inl rfl))
    by_cases h10 : c = Char.ofNat 0x0A
    · subst h10; exact parseStringChars_escapeCharList_ctrl acc rest 'n' (Or.inr (Or.inr (Or.inl rfl)))
    by_cases h13 : c = Char.ofNat 0x0D
    · subst h13; exact parseStringChars_escapeCharList_ctrl acc rest 'r' (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    by_cases h9 : c = Char.ofNat 0x09
    · subst h9; exact parseStringChars_escapeCharList_ctrl acc rest 't' (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    by_cases hlt : c.toNat < 0x20
    · exact parseStringChars_escapeCharList_unicode c acc rest hlt
    · exact parseStringChars_escapeCharList_plain c acc rest hlt

theorem parseStringChars_escapeStringChars (cs : List Char) (rest : List Char) :
    parseStringChars (escapeStringChars cs ++ rest) [] =
      parseStringChars rest (String.ofList cs).toList := by
  induction cs with
  | nil =>
    simp [escapeStringChars, parseStringChars, parseStringCharsGo, parseStringCharsFuelBound,
      parseStringGoFuel_nil, String.toList_ofList]
  | cons c cs ih =>
    simp only [escapeStringChars, List.flatMap_cons, List.append_assoc, List.cons_append]
    rw [← List.append_assoc, parseStringChars_escapeCharList c, ih, String.toList_ofList]

theorem parseStringChars_escapeString (s : String) (rest : List Char) :
    parseStringChars (escapeStringChars s.toList ++ '"' :: rest) [] = some (s, rest) := by
  have h := parseStringChars_escapeStringChars s.toList ('"' :: rest)
  rw [h]
  dsimp [parseStringChars, parseStringCharsGo, parseStringCharsFuelBound, parseStringCharsGoFuel]
  simp only [String.toList_ofList, parseStringCharsGoFuel, String.ofList_toList]

theorem parseString_jcsEscapeString (s : String) (rest : List Char) :
    parseString (jcsEscapeStringChars s ++ rest) = some (s, rest) := by
  unfold parseString jcsEscapeStringChars
  simpa [List.cons_append] using parseStringChars_escapeString s rest

end ParseString

end OmegaJCS
