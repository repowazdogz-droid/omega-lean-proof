section ParseString

private theorem escapeCharList_quote : escapeCharList '"' = ['\\', '"'] := by
  native_decide

private theorem escapeCharList_backslash : escapeCharList '\\' = ['\\', '\\'] := by
  native_decide

private theorem parseStringGoFuel_nil (f : Nat) (acc : List Char) :
    parseStringCharsGoFuel f [] acc = none := by
  cases f with
  | zero => rfl
  | succ _ => rfl

theorem parseStringCharsGoFuel_mono (m n : Nat) (s acc : List Char) (h : m ≤ n) :
    parseStringCharsGoFuel (m + 1) s acc = parseStringCharsGoFuel (n + 1) s acc := by
  induction n generalizing m s acc with
  | zero =>
    have hm : m = 0 := Nat.eq_zero_of_le_zero h
    subst hm
    rfl
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · rfl
    · have hle : m ≤ n := Nat.lt_succ_iff.mp hlt
      match s with
      | [] => simp [parseStringCharsGoFuel, parseStringGoFuel_nil]
      | '"' :: rest => rfl
      | '\\' :: rest =>
        simp only [parseStringCharsGoFuel]
        match rest with
        | [] => rfl
        | '"' :: r => exact ih m r (acc ++ ['"']) (Nat.le_of_lt hlt)
        | '\\' :: r => exact ih m r (acc ++ ['\\']) (Nat.le_of_lt hlt)
        | 'b' :: r => exact ih m r (acc ++ [Char.ofNat 0x08]) (Nat.le_of_lt hlt)
        | 'f' :: r => exact ih m r (acc ++ [Char.ofNat 0x0C]) (Nat.le_of_lt hlt)
        | 'n' :: r => exact ih m r (acc ++ [Char.ofNat 0x0A]) (Nat.le_of_lt hlt)
        | 'r' :: r => exact ih m r (acc ++ [Char.ofNat 0x0D]) (Nat.le_of_lt hlt)
        | 't' :: r => exact ih m r (acc ++ [Char.ofNat 0x09]) (Nat.le_of_lt hlt)
        | 'u' :: r =>
          cases parseHex4 r with
          | none => rfl
          | some p => exact ih m p.2 (acc ++ [Char.ofNat p.1]) (Nat.le_of_lt hlt)
        | _ :: _ => rfl
      | c :: rest =>
        exact ih m rest (acc ++ [c]) (Nat.le_of_lt hlt)

theorem parseStringCharsGoFuel_mono_ge (fuel extra : Nat) (s acc : List Char)
    (hle : extra ≤ fuel) (hpos : 0 < extra) :
    parseStringCharsGoFuel fuel s acc = parseStringCharsGoFuel extra s acc := by
  induction fuel generalizing extra s acc with
  | zero =>
    have he : extra = 0 := Nat.eq_zero_of_le_zero hle
    subst he
    exact absurd hpos (Nat.not_lt_zero _)
  | succ f ih =>
    cases extra with
    | zero => exact absurd hpos (Nat.not_lt_zero _)
    | succ e =>
      rcases Nat.eq_or_lt_of_le hle with heq | hlt
      · have hf : e = f := by injection heq
        subst hf; rfl
      · have hele : e ≤ f := Nat.le_of_lt (Nat.lt_of_succ_lt_succ hlt)
        unfold parseStringCharsGoFuel
        match s with
        | [] => rfl
        | '"' :: rest => rfl
        | '\\' :: rest =>
          match rest with
          | [] => rfl
          | '"' :: r => exact ih e r (acc ++ ['"']) hele (Nat.lt_succ_self e)
          | '\' :: r => exact ih e r (acc ++ ['\\']) hele (Nat.lt_succ_self e)
          | 'b' :: r => exact ih e r (acc ++ [Char.ofNat 0x08]) hele (Nat.lt_succ_self e)
          | 'f' :: r => exact ih e r (acc ++ [Char.ofNat 0x0C]) hele (Nat.lt_succ_self e)
          | 'n' :: r => exact ih e r (acc ++ [Char.ofNat 0x0A]) hele (Nat.lt_succ_self e)
          | 'r' :: r => exact ih e r (acc ++ [Char.ofNat 0x0D]) hele (Nat.lt_succ_self e)
          | 't' :: r => exact ih e r (acc ++ [Char.ofNat 0x09]) hele (Nat.lt_succ_self e)
          | 'u' :: r =>
            match parseHex4 r with
            | none => rfl
            | some (cp, r') => exact ih e r' (acc ++ [Char.ofNat cp]) hele (Nat.lt_succ_self e)
          | _ :: _ => rfl
        | c :: rest => exact ih e rest (acc ++ [c]) hele (Nat.lt_succ_self e)

private theorem parseStringChars_escapeCharList_quote_nil (acc : List Char) :
    parseStringChars (escapeCharList '"' ++ []) acc =
      parseStringChars [] (acc ++ ['"']) := by
  dsimp [parseStringChars, parseStringCharsFuelBoundFuel,
    escapeCharList, escapeChar]
  rw [escapeCharList_quote, List.cons_append, List.nil_append, List.length_nil]
  simp [parseStringCharsGoFuel]

private theorem parseStringChars_escapeCharList_quote_nonempty (acc rest : List Char) (h : rest ≠ []) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  dsimp [parseStringChars, parseStringCharsFuelBoundFuel,
    escapeCharList, escapeChar]
  rw [escapeCharList_quote, List.cons_append, List.nil_appendFuel]
  have hlen : ('\\' :: '"' :: rest).length * 6 = (2 + rest.length) * 6 := by simp; omega
  rw [hlen]
  exact parseStringCharsGoFuel_mono_ge ((2 + rest.length) * 6) (rest.length * 6 + 1) rest
    (acc ++ ['"']) (by omega) (by omega)

private theorem parseStringChars_escapeCharList_quote (acc rest : List Char) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  cases rest with
  | nil => exact parseStringChars_escapeCharList_quote_nil acc
  | cons c rest => exact parseStringChars_escapeCharList_quote_nonempty acc (c :: rest) rfl

private theorem parseStringChars_escapeCharList_backslash (acc rest : List Char) :
    parseStringChars (escapeCharList '\\' ++ rest) acc =
      parseStringChars rest (acc ++ ['\\']) := by
  dsimp [parseStringChars, parseStringCharsFuelBoundFuel,
    escapeCharList, escapeChar]
  rw [escapeCharList_backslash]
  simp only [beq_iff_eq, if_false, List.cons_append, List.nil_appendFuel]
  have hlen : ('\\' :: '\\' :: rest).length * 6 = (2 + rest.length) * 6 := by simp; omega
  rw [hlen]
  exact parseStringCharsGoFuel_mono_ge ((2 + rest.length) * 6) (rest.length * 6 + 1) rest
    (acc ++ ['\\']) (by omega) (by omega)

private theorem parseStringChars_escapeCharList_ctrl (acc rest : List Char) (tag : Char)
    (h : tag = 'b' ∨ tag = 'f' ∨ tag = 'n' ∨ tag = 'r' ∨ tag = 't') :
    parseStringChars (['\\', tag] ++ rest) acc =
      parseStringChars rest (acc ++ [match tag with
        | 'b' => Char.ofNat 0x08 | 'f' => Char.ofNat 0x0C | 'n' => Char.ofNat 0x0A
        | 'r' => Char.ofNat 0x0D | 't' => Char.ofNat 0x09 | _ => tag]) := by
  rcases h with rfl | rfl | rfl | rfl | rfl
  all_goals
    dsimp [parseStringChars, parseStringCharsFuelBoundFuel]
    simp only [List.cons_append, List.nil_appendFuel]
    exact parseStringCharsGoFuel_mono_ge ((2 + rest.length) * 6) (rest.length * 6 + 1) rest
      _ (by omega) (by omega)

private theorem parseStringChars_escapeCharList_unicode (c : Char) (acc rest : List Char)
    (h1 : c ≠ '"') (h2 : c ≠ '\\') (h3 : c.toNat ≠ 0x08) (h4 : c.toNat ≠ 0x0C)
    (h5 : c.toNat ≠ 0x0A) (h6 : c.toNat ≠ 0x0D) (h7 : c.toNat ≠ 0x09) (hlt : c.toNat < 0x20) :
    parseStringChars (escapeCharList c ++ rest) acc =
      parseStringChars rest (acc ++ [c]) := by
  dsimp [parseStringChars, parseStringCharsFuelBoundFuel,
    escapeCharList, escapeChar]
  simp only [beq_iff_eq, h1, h2, h3, h4, h5, h6, h7, if_false, hlt, if_pos, String.append,
    String.toList, List.cons_append, List.nil_append, hex4Lower, hex4Lower_toList]
  have h0 := hexDigit_spec ((c.toNat >>> 12) &&& 0xF) (land_f_lt16 _)
  have h1d := hexDigit_spec ((c.toNat >>> 8) &&& 0xF) (land_f_lt16 _)
  have h2d := hexDigit_spec ((c.toNat >>> 4) &&& 0xF) (land_f_lt16 _)
  have h3d := hexDigit_spec (c.toNat &&& 0xF) (land_f_lt16 _)
  simp only [h0, h1d, h2d, h3d, hex4_recomb_small c.toNat (by omega), parseHex4, hexValue,
    parseStringCharsGoFuel]
  have hstep :
      parseStringCharsGoFuel ((6 + rest.length) * 6) rest (acc ++ [c]) =
        parseStringCharsGoFuel (rest.length * 6 + 1) rest (acc ++ [c]) := by
    exact parseStringCharsGoFuel_mono_ge ((6 + rest.length) * 6) (rest.length * 6 + 1) rest
      (acc ++ [c]) (by omega) (by omega)
  rw [hstep]

private theorem parseStringChars_escapeCharList_plain (c : Char) (acc rest : List Char)
    (h1 : c ≠ '"') (h2 : c ≠ '\\') (h3 : c.toNat ≠ 0x08) (h4 : c.toNat ≠ 0x0C)
    (h5 : c.toNat ≠ 0x0A) (h6 : c.toNat ≠ 0x0D) (h7 : c.toNat ≠ 0x09) (h8 : ¬ c.toNat < 0x20) :
    parseStringChars (escapeCharList c ++ rest) acc =
      parseStringChars rest (acc ++ [c]) := by
  dsimp [parseStringChars, parseStringCharsFuelBoundFuel,
    escapeCharList, escapeChar]
  simp only [beq_iff_eq, h1, h2, h3, h4, h5, h6, h7, if_false, h8, if_neg, String.singleton,
    String.toList, List.cons_append, List.nil_appendFuel]
  have hstep :
      parseStringCharsGoFuel ((1 + rest.length) * 6) rest (acc ++ [c]) =
        parseStringCharsGoFuel (rest.length * 6 + 1) rest (acc ++ [c]) := by
    exact parseStringCharsGoFuel_mono_ge ((1 + rest.length) * 6) (rest.length * 6 + 1) rest
      (acc ++ [c]) (by omega) (by omega)
  simp only [parseStringCharsGoFuel, hstep]

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
    · subst h13
      exact parseStringChars_escapeCharList_ctrl acc rest 'r'
        (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    by_cases h9 : c = Char.ofNat 0x09
    · subst h9
      exact parseStringChars_escapeCharList_ctrl acc rest 't'
        (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    by_cases hlt : c.toNat < 0x20
    · exact parseStringChars_escapeCharList_unicode c acc rest
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) hlt
    · exact parseStringChars_escapeCharList_plain c acc rest
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) h8

theorem parseStringChars_escapeStringChars (cs : List Char) (rest : List Char) :
    parseStringChars (escapeStringChars cs ++ rest) [] =
      parseStringChars rest (String.ofList cs).toList := by
  induction cs with
  | nil =>
    simp [escapeStringChars, parseStringChars, parseStringCharsFuelBound,
      parseStringGoFuel_nil]
  | cons c cs ih =>
    simp only [escapeStringChars, List.flatMap_cons, List.append_assoc]
    rw [← List.append_assoc, parseStringChars_escapeCharList, ih]

theorem parseStringChars_escapeString (s : String) (rest : List Char) :
    parseStringChars (escapeStringChars s.toList ++ '"' :: rest) [] = some (s, rest) := by
  have h := parseStringChars_escapeStringChars s.toList ('"' :: rest)
  rw [h]
  dsimp [parseStringChars, parseStringCharsFuelBoundFuel]
  simp only [String.toList_ofListFuel]

theorem parseString_jcsEscapeString (s : String) (rest : List Char) :
    parseString (jcsEscapeStringChars s ++ rest) = some (s, rest) := by
  unfold parseString jcsEscapeStringChars
  simpa [List.cons_append] using parseStringChars_escapeString s rest

end ParseString