section ParseString

private theorem escapeCharList_quote : escapeCharList '"' = ['\\', '"'] := by native_decide
private theorem escapeCharList_backslash : escapeCharList '\\' = ['\\', '\\'] := by native_decide

private theorem parseStringChars_escapeCharList_quote (acc rest : List Char) :
    parseStringChars (escapeCharList '"' ++ rest) acc = parseStringChars rest (acc ++ ['"']) := by
  rw [escapeCharList_quote]; simp [parseStringChars, List.cons_append, List.nil_append]

private theorem parseStringChars_escapeCharList_backslash (acc rest : List Char) :
    parseStringChars (escapeCharList '\\' ++ rest) acc = parseStringChars rest (acc ++ ['\\']) := by
  rw [escapeCharList_backslash]; simp [parseStringChars, List.cons_append, List.nil_append]

private theorem parseStringChars_escapeCharList_ctrl (acc rest : List Char) (tag : Char)
    (h : tag = 'b' ∨ tag = 'f' ∨ tag = 'n' ∨ tag = 'r' ∨ tag = 't') :
    parseStringChars (['\\', tag] ++ rest) acc =
      parseStringChars rest (acc ++ [match tag with
        | 'b' => Char.ofNat 0x08 | 'f' => Char.ofNat 0x0C | 'n' => Char.ofNat 0x0A
        | 'r' => Char.ofNat 0x0D | 't' => Char.ofNat 0x09 | _ => tag]) := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [parseStringChars, List.cons_append]

private theorem parseStringChars_escapeCharList_unicode (c : Char) (acc rest : List Char)
    (h1 : c ≠ '"') (h2 : c ≠ '\\') (h3 : c.toNat ≠ 0x08) (h4 : c.toNat ≠ 0x0C)
    (h5 : c.toNat ≠ 0x0A) (h6 : c.toNat ≠ 0x0D) (h7 : c.toNat ≠ 0x09) (hlt : c.toNat < 0x20) :
    parseStringChars (escapeCharList c ++ rest) acc = parseStringChars rest (acc ++ [c]) := by
  simp [escapeCharList, escapeChar, beq_iff_eq, h1, h2, h3, h4, h5, h6, h7, if_false, hlt, if_pos,
    String.append, String.toList, List.cons_append, List.nil_append, hex4Lower, hex4Lower_toList]
  have h0 := hexDigit_spec ((c.toNat >>> 12) &&& 0xF) (land_f_lt16 _)
  have h1d := hexDigit_spec ((c.toNat >>> 8) &&& 0xF) (land_f_lt16 _)
  have h2d := hexDigit_spec ((c.toNat >>> 4) &&& 0xF) (land_f_lt16 _)
  have h3d := hexDigit_spec (c.toNat &&& 0xF) (land_f_lt16 _)
  simp [parseStringChars, List.cons_append, List.nil_append, h0, h1d, h2d, h3d, hex4_recomb_small c.toNat (by omega)]

private theorem parseStringChars_escapeCharList_plain (c : Char) (acc rest : List Char)
    (h1 : c ≠ '"') (h2 : c ≠ '\\') (h3 : c.toNat ≠ 0x08) (h4 : c.toNat ≠ 0x0C)
    (h5 : c.toNat ≠ 0x0A) (h6 : c.toNat ≠ 0x0D) (h7 : c.toNat ≠ 0x09) (h8 : ¬ c.toNat < 0x20) :
    parseStringChars (escapeCharList c ++ rest) acc = parseStringChars rest (acc ++ [c]) := by
  simp [escapeCharList, escapeChar, beq_iff_eq, h1, h2, h3, h4, h5, h6, h7, if_false, h8, if_neg,
    String.singleton, String.toList, List.cons_append, List.nil_append, parseStringChars]

theorem parseStringChars_escapeCharList (c : Char) (acc rest : List Char) :
    parseStringChars (escapeCharList c ++ rest) acc = parseStringChars rest (acc ++ [c]) := by
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
    · have h1 : c ≠ '"' := by intro h; subst h; omega
      have h2 : c ≠ '\\' := by intro h; subst h; omega
      have h3 : c.toNat ≠ 0x08 := fun hn => h8 (Char.ofNat_eq_iff.mpr (by simpa using hn))
      have h4 : c.toNat ≠ 0x0C := fun hn => h12 (Char.ofNat_eq_iff.mpr (by simpa using hn))
      have h5 : c.toNat ≠ 0x0A := fun hn => h10 (Char.ofNat_eq_iff.mpr (by simpa using hn))
      have h6 : c.toNat ≠ 0x0D := fun hn => h13 (Char.ofNat_eq_iff.mpr (by simpa using hn))
      have h7 : c.toNat ≠ 0x09 := fun hn => h9 (Char.ofNat_eq_iff.mpr (by simpa using hn))
      exact parseStringChars_escapeCharList_unicode c acc rest h1 h2 h3 h4 h5 h6 h7 hlt
    · have h1 : c ≠ '"' := by intro h; subst h; omega
      have h2 : c ≠ '\\' := by intro h; subst h; omega
      have h3 : c.toNat ≠ 0x08 := fun hn => h8 (Char.ofNat_eq_iff.mpr (by simpa using hn))
      have h4 : c.toNat ≠ 0x0C := fun hn => h12 (Char.ofNat_eq_iff.mpr (by simpa using hn))
      have h5 : c.toNat ≠ 0x0A := fun hn => h10 (Char.ofNat_eq_iff.mpr (by simpa using hn))
      have h6 : c.toNat ≠ 0x0D := fun hn => h13 (Char.ofNat_eq_iff.mpr (by simpa using hn))
      have h7 : c.toNat ≠ 0x09 := fun hn => h9 (Char.ofNat_eq_iff.mpr (by simpa using hn))
      exact parseStringChars_escapeCharList_plain c acc rest h1 h2 h3 h4 h5 h6 h7 hlt

theorem parseStringChars_escapeStringChars (cs : List Char) (rest : List Char) (acc : List Char) :
    parseStringChars (escapeStringChars cs ++ rest) acc = parseStringChars rest (acc ++ cs) := by
  induction cs generalizing acc rest with
  | nil => simp [escapeStringChars, parseStringChars, List.nil_append]
  | cons c cs ih =>
    simp [escapeStringChars, List.flatMap_cons, List.append_assoc]
    rw [← List.append_assoc, parseStringChars_escapeCharList, ih]

theorem parseStringChars_escapeString (s : String) (rest : List Char) :
    parseStringChars (escapeStringChars s.toList ++ '"' :: rest) [] = some (s, rest) := by
  have h := parseStringChars_escapeStringChars s.toList ('"' :: rest) []
  rw [h]; simp [parseStringChars]

theorem parseString_jcsEscapeString (s : String) (rest : List Char) :
    parseString (jcsEscapeStringChars s ++ rest) = some (s, rest) := by
  unfold parseString jcsEscapeStringChars
  simpa [List.cons_append] using parseStringChars_escapeString s rest

end ParseString
