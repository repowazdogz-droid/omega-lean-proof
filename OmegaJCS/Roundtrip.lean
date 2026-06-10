import Init.Data.Nat.Bitwise.Lemmas
import OmegaJCS.Types
import OmegaJCS.Encode
import OmegaJCS.Decode

namespace OmegaJCS

/-! Roundtrip on encoder output (decoder is not a general JSON parser). -/

section Prefix

theorem takePrefix_append (pre : String) (rest : List Char) :
    takePrefix (pre.toList ++ rest) pre = some rest := by
  unfold takePrefix startsWith
  have hlen : pre.toList.length = pre.length := by rw [String.length_toList]
  have htake : (pre.toList ++ rest).take pre.length = pre.toList := by
    rw [List.take_append, ← hlen, Nat.sub_self, List.take_zero, List.append_nil, List.take_length]
  have hdrop : (pre.toList ++ rest).drop pre.length = rest := by
    rw [List.drop_append, hlen, Nat.sub_self, List.drop_zero, ← hlen, List.drop_length, List.nil_append]
  simp [htake, hdrop]

theorem takePrefix_true_not_null (rest : List Char) :
    takePrefix ("true".toList ++ rest) "null" = none := by
  unfold takePrefix startsWith; cases rest <;> rfl

theorem takePrefix_false_not_null (rest : List Char) :
    takePrefix ("false".toList ++ rest) "null" = none := by
  unfold takePrefix startsWith; cases rest <;> rfl

theorem takePrefix_false_not_true (rest : List Char) :
    takePrefix ("false".toList ++ rest) "true" = none := by
  unfold takePrefix startsWith; cases rest <;> rfl

end Prefix

section StringJoin

theorem foldl_append_start (pfx start : String) (ss : List String) :
    List.foldl (fun r s => r ++ s) (pfx ++ start) ss =
      pfx ++ List.foldl (fun r s => r ++ s) start ss := by
  induction ss generalizing start with
  | nil => simp [List.foldl_nil, String.append_assoc]
  | cons t ts ih =>
    simp only [List.foldl_cons]
    rw [String.append_assoc]
    exact ih (start ++ t)

theorem String_join_cons (s : String) (ss : List String) :
    String.join (s :: ss) = s ++ String.join ss := by
  unfold String.join
  simpa [String.empty_append] using foldl_append_start s "" ss

theorem stringJoin_map_escapeChar (cs : List Char) :
    (String.join (cs.map escapeChar)).toList = escapeStringChars cs := by
  induction cs with
  | nil => simp [escapeStringChars, String.join]
  | cons c cs ih =>
    simp only [escapeStringChars, escapeCharList, List.flatMap_cons, List.map_cons,
      String_join_cons, String.toList_append, ih]

@[simp] theorem jcsEscapeStringChars_spec (s : String) :
    jcsEscapeStringChars s = '"' :: escapeStringChars s.toList ++ ['"'] := rfl

end StringJoin

section Hex

private theorem land_f_lt16 (x : Nat) : x &&& 0xF < 16 :=
  Nat.lt_succ_iff.mpr (Nat.and_le_right (n := x) (m := 0xF))

private theorem hexDigit_spec (n : Nat) (hn : n < 16) :
    hexValue (hexDigit n) = some n := by
  revert n hn
  decide +revert

private theorem hex4_recomb_small (n : Nat) (hn : n < 0x20) :
    (n >>> 12 &&& 0xF) * 4096 +
      (n >>> 8 &&& 0xF) * 256 +
      (n >>> 4 &&& 0xF) * 16 +
      (n &&& 0xF) = n := by
  revert n hn
  decide +revert

private theorem hex4Lower_toList (n : Nat) :
    (hex4Lower n).toList =
      [hexDigit ((n >>> 12) &&& 0xF), hexDigit ((n >>> 8) &&& 0xF),
        hexDigit ((n >>> 4) &&& 0xF), hexDigit (n &&& 0xF)] := by
  unfold hex4Lower
  simp [String.toList_ofList]

private theorem hex4Lower_parseHex4 (n : Nat) (hn : n < 0x20) (rest : List Char) :
    parseHex4 ((hex4Lower n).toList ++ rest) = some (n, rest) := by
  rw [hex4Lower_toList, List.cons_append]
  have hflat :
      hexDigit (n >>> 12 &&& 0xF) ::
        ([hexDigit (n >>> 8 &&& 0xF), hexDigit (n >>> 4 &&& 0xF), hexDigit (n &&& 0xF)] ++ rest) =
      hexDigit (n >>> 12 &&& 0xF) :: hexDigit (n >>> 8 &&& 0xF) :: hexDigit (n >>> 4 &&& 0xF) ::
        hexDigit (n &&& 0xF) :: rest := by
    simp [List.cons_append, List.nil_append]
  have h0 := hexDigit_spec ((n >>> 12) &&& 0xF) (land_f_lt16 _)
  have h1 := hexDigit_spec ((n >>> 8) &&& 0xF) (land_f_lt16 _)
  have h2 := hexDigit_spec ((n >>> 4) &&& 0xF) (land_f_lt16 _)
  have h3 := hexDigit_spec (n &&& 0xF) (land_f_lt16 _)
  rw [hflat]
  unfold parseHex4
  simp [h0, h1, h2, h3, hex4_recomb_small n hn]

end Hex

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

private theorem escapeCharList_ctrl (c : Char)
    (h3 : c.toNat ≠ 0x08) (h4 : c.toNat ≠ 0x0C) (h5 : c.toNat ≠ 0x0A)
    (h6 : c.toNat ≠ 0x0D) (h7 : c.toNat ≠ 0x09) (hlt : c.toNat < 0x20) :
    escapeCharList c = '\\' :: 'u' :: (hex4Lower c.toNat).toList := by
  have h1 : c ≠ '"' := by intro h; subst h; exact absurd hlt (by decide)
  have h2 : c ≠ '\\' := by intro h; subst h; exact absurd hlt (by decide)
  unfold escapeCharList escapeChar
  simp only [beq_iff_eq, h1, h2, h3, h4, h5, h6, h7, hlt, if_false, if_true]
  rw [String.toList_append]; rfl

private theorem escapeCharList_plain (c : Char)
    (h1 : c ≠ '"') (h2 : c ≠ '\\') (h3 : c.toNat ≠ 0x08) (h4 : c.toNat ≠ 0x0C)
    (h5 : c.toNat ≠ 0x0A) (h6 : c.toNat ≠ 0x0D) (h7 : c.toNat ≠ 0x09) (hge : ¬ c.toNat < 0x20) :
    escapeCharList c = [c] := by
  unfold escapeCharList escapeChar
  simp only [beq_iff_eq, h1, h2, h3, h4, h5, h6, h7, hge, if_false]
  exact String.toList_singleton c

theorem parseStringChars_escapeCharList (c : Char) (acc rest : List Char) :
    parseStringChars (escapeCharList c ++ rest) acc = parseStringChars rest (acc ++ [c]) := by
  by_cases hq : c = '"'
  · subst hq; exact parseStringChars_escapeCharList_quote acc rest
  by_cases hbs : c = '\\'
  · subst hbs; exact parseStringChars_escapeCharList_backslash acc rest
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
  have h3 : c.toNat ≠ 0x08 := fun hn => h8 (by rw [← hn]; exact (Char.ofNat_toNat c).symm)
  have h4 : c.toNat ≠ 0x0C := fun hn => h12 (by rw [← hn]; exact (Char.ofNat_toNat c).symm)
  have h5 : c.toNat ≠ 0x0A := fun hn => h10 (by rw [← hn]; exact (Char.ofNat_toNat c).symm)
  have h6 : c.toNat ≠ 0x0D := fun hn => h13 (by rw [← hn]; exact (Char.ofNat_toNat c).symm)
  have h7 : c.toNat ≠ 0x09 := fun hn => h9 (by rw [← hn]; exact (Char.ofNat_toNat c).symm)
  by_cases hlt : c.toNat < 0x20
  · rw [escapeCharList_ctrl c h3 h4 h5 h6 h7 hlt, hex4Lower_toList]
    have d0 := hexDigit_spec ((c.toNat >>> 12) &&& 0xF) (land_f_lt16 _)
    have d1 := hexDigit_spec ((c.toNat >>> 8) &&& 0xF) (land_f_lt16 _)
    have d2 := hexDigit_spec ((c.toNat >>> 4) &&& 0xF) (land_f_lt16 _)
    have d3 := hexDigit_spec (c.toNat &&& 0xF) (land_f_lt16 _)
    simp [parseStringChars, List.cons_append, List.nil_append, d0, d1, d2, d3,
      hex4_recomb_small c.toNat hlt, Char.ofNat_toNat]
  · rw [escapeCharList_plain c hq hbs h3 h4 h5 h6 h7 hlt]
    simp [parseStringChars, hq, hbs]

theorem parseStringChars_escapeStringChars (cs : List Char) (rest : List Char) (acc : List Char) :
    parseStringChars (escapeStringChars cs ++ rest) acc = parseStringChars rest (acc ++ cs) := by
  induction cs generalizing acc rest with
  | nil => simp [escapeStringChars, parseStringChars, List.nil_append]
  | cons c cs ih =>
    rw [show escapeStringChars (c :: cs) = escapeCharList c ++ escapeStringChars cs from
          by simp [escapeStringChars, List.flatMap_cons]]
    rw [List.append_assoc, parseStringChars_escapeCharList, ih]
    simp [List.append_assoc]

theorem parseStringChars_escapeString (s : String) (rest : List Char) :
    parseStringChars (escapeStringChars s.toList ++ '"' :: rest) [] = some (s, rest) := by
  have h := parseStringChars_escapeStringChars s.toList ('"' :: rest) []
  rw [h]; simp [parseStringChars]

theorem parseString_jcsEscapeString (s : String) (rest : List Char) :
    parseString (jcsEscapeStringChars s ++ rest) = some (s, rest) := by
  unfold parseString jcsEscapeStringChars
  simpa [List.cons_append] using parseStringChars_escapeString s rest

end ParseString


section NumberParse

/-- `rest` does not begin with a decimal digit. This is the precondition under which
    the greedy digit parser halts exactly at the encoded number's boundary; at every
    call site `rest` is either empty or starts with a structural byte (`,` `]` `}` `:`). -/
def NoLeadDigit (rest : List Char) : Prop := ∀ c t, rest = c :: t → isDigit c = false

theorem noLeadDigit_nil : NoLeadDigit [] := by intro c t h; cases h

theorem noLeadDigit_cons (c : Char) (t : List Char) (hc : isDigit c = false) :
    NoLeadDigit (c :: t) := by intro c' t' h; cases h; exact hc

private theorem isDigit_ofNat_digit (d : Nat) (hd : d < 10) :
    isDigit (Char.ofNat (d + '0'.toNat)) = true := by
  revert d hd
  decide +revert

private theorem parseNatDigits_nil (rest : List Char) (acc : Nat) (h : NoLeadDigit rest) :
    parseNatDigits rest acc = some (acc, rest) := by
  cases rest with
  | nil => simp [parseNatDigits]
  | cons c t => simp [parseNatDigits, h c t rfl]

private theorem parseNatDigits_cons (c : Char) (s rest : List Char) (acc : Nat) :
    parseNatDigits (c :: s ++ rest) acc =
      if isDigit c then
        parseNatDigits (s ++ rest) (acc * 10 + (c.toNat - '0'.toNat))
      else
        some (acc, c :: s ++ rest) := by
  simp [parseNatDigits, List.append_assoc]

private theorem parseNatDigits_all_digits (digits : List Char) (rest : List Char) (acc : Nat)
    (hd : ∀ c ∈ digits, isDigit c = true) (hrest : NoLeadDigit rest) :
    parseNatDigits (digits ++ rest) acc =
      some (digits.foldl (fun a c => a * 10 + (c.toNat - '0'.toNat)) acc, rest) := by
  induction digits generalizing acc with
  | nil => simpa using parseNatDigits_nil rest acc hrest
  | cons c digits ih =>
    have hdc := hd c (by simp)
    have hd' : ∀ c' ∈ digits, isDigit c' = true := fun c' hc' =>
      hd c' (by simp [List.mem_cons]; exact Or.inr hc')
    rw [parseNatDigits_cons, if_pos hdc, ih _ hd', List.foldl_cons]

private theorem digit_toNat_sub (d : Nat) (hd : d < 10) :
    (Char.ofNat (d + '0'.toNat)).toNat - '0'.toNat = d := by revert d hd; decide +revert

private theorem natToDecimalAux_zero (acc : List Char) : natToDecimalAux 0 acc = acc := by
  unfold natToDecimalAux; rfl

private theorem natToDecimalAux_step (n : Nat) (hn : n ≠ 0) (acc : List Char) :
    natToDecimalAux n acc = natToDecimalAux (n / 10) (Char.ofNat (n % 10 + '0'.toNat) :: acc) := by
  rw [natToDecimalAux, dif_neg hn]

/-- Accumulator factoring: the loop only prepends its running accumulator, so the
    accumulator can be split off as a suffix. This is what lets the strong-induction
    hypothesis (stated for the empty accumulator) apply to the recursive call. -/
private theorem natToDecimalAux_acc (n : Nat) (acc : List Char) :
    natToDecimalAux n acc = natToDecimalAux n [] ++ acc := by
  induction n using Nat.strongRecOn generalizing acc with
  | _ n ih =>
    by_cases hn : n = 0
    · subst hn; rw [natToDecimalAux_zero, natToDecimalAux_zero, List.nil_append]
    · have hlt : n / 10 < n := Nat.div_lt_self (Nat.zero_lt_of_ne_zero hn) (by decide)
      rw [natToDecimalAux_step n hn acc, ih (n/10) hlt (Char.ofNat (n % 10 + '0'.toNat) :: acc),
          natToDecimalAux_step n hn [], ih (n/10) hlt [Char.ofNat (n % 10 + '0'.toNat)]]
      simp

private theorem natToDecimalAux_eq (n : Nat) (hn : n ≠ 0) :
    (natToDecimalAux n []).foldl (fun a c => a * 10 + (c.toNat - '0'.toNat)) 0 = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    have hd10 : n % 10 < 10 := Nat.mod_lt n (by decide)
    rw [natToDecimalAux_step n hn [], natToDecimalAux_acc (n/10) [Char.ofNat (n % 10 + '0'.toNat)],
        List.foldl_append, List.foldl_cons, List.foldl_nil, digit_toNat_sub _ hd10]
    by_cases h10 : n < 10
    · have hn10 : n / 10 = 0 := Nat.div_eq_of_lt h10
      rw [hn10, natToDecimalAux_zero, List.foldl_nil]
      have := Nat.div_add_mod n 10; omega
    · have hn' : n / 10 ≠ 0 := by omega
      have ih' := ih (n / 10) (Nat.div_lt_self (by omega) (by decide)) hn'
      rw [ih']
      have := Nat.div_add_mod n 10; omega

private theorem natToDecimalAux_all_digits (n : Nat) (hn : n ≠ 0) :
    ∀ c ∈ natToDecimalAux n [], isDigit c = true := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro c hc
    have hd10 : n % 10 < 10 := Nat.mod_lt n (by decide)
    rw [natToDecimalAux_step n hn [], natToDecimalAux_acc (n/10) [Char.ofNat (n % 10 + '0'.toNat)],
        List.mem_append] at hc
    rcases hc with hc | hc
    · by_cases hn' : n / 10 = 0
      · rw [hn', natToDecimalAux_zero] at hc; exact absurd hc (List.not_mem_nil)
      · exact ih (n / 10) (Nat.div_lt_self (by omega) (by decide)) hn' c hc
    · simp only [List.mem_singleton] at hc
      subst hc
      exact isDigit_ofNat_digit (n % 10) hd10

private theorem natToDecimalAux_spec (n : Nat) (rest : List Char) (hn : n ≠ 0)
    (hrest : NoLeadDigit rest) :
    parseNatDigits (natToDecimalAux n [] ++ rest) 0 = some (n, rest) := by
  have hd := natToDecimalAux_all_digits n hn
  have e := parseNatDigits_all_digits (natToDecimalAux n []) rest 0 hd hrest
  rw [natToDecimalAux_eq n hn] at e
  exact e

theorem parseNatDigits_natToDecimal (n : Nat) (rest : List Char) (hrest : NoLeadDigit rest) :
    parseNatDigits (natToDecimal n ++ rest) 0 = some (n, rest) := by
  cases n with
  | zero =>
    simp [natToDecimal, parseNatDigits, isDigit]
    exact parseNatDigits_nil rest 0 hrest
  | succ n =>
    unfold natToDecimal
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    exact natToDecimalAux_spec (n + 1) rest (Nat.succ_ne_zero n) hrest

/-- parseInt on a digit-led list reduces to the nat-digit parser (the `'-'` arm is
    skipped because a digit is not `'-'`). -/
private theorem parseInt_digit_led (e : Char) (es rest : List Char) (k : Nat)
    (hdig : isDigit e = true) (hpd : parseNatDigits (e :: es) 0 = some (k, rest)) :
    parseInt (e :: es) = some (Int.ofNat k, rest) := by
  have hdash : e ≠ '-' := by intro h; subst h; revert hdig; decide
  unfold parseInt
  split
  · rename_i rest' heq; injection heq with h1 _; exact absurd h1 hdash
  · rename_i c s heq; injection heq with h1 h2; subst h1; rw [if_pos hdig, hpd]
  · rename_i heq; exact absurd heq (by simp)

private theorem parseInt_natToDecimal (k : Nat) (rest : List Char) (hrest : NoLeadDigit rest) :
    parseInt (natToDecimal k ++ rest) = some (Int.ofNat k, rest) := by
  have hne : natToDecimal k ≠ [] := by
    cases k with
    | zero => simp [natToDecimal]
    | succ k =>
      rw [natToDecimal, if_neg (Nat.succ_ne_zero k), natToDecimalAux_step _ (Nat.succ_ne_zero k) [],
          natToDecimalAux_acc ((k+1)/10) [Char.ofNat ((k+1) % 10 + '0'.toNat)]]
      simp
  obtain ⟨e, es, he⟩ := List.exists_cons_of_ne_nil hne
  have hmem : e ∈ natToDecimal k := he ▸ List.mem_cons_self
  have hdig : isDigit e = true := by
    cases k with
    | zero => rw [natToDecimal] at hmem; simp at hmem; subst hmem; decide
    | succ k =>
      rw [natToDecimal, if_neg (Nat.succ_ne_zero k)] at hmem
      exact natToDecimalAux_all_digits _ (Nat.succ_ne_zero k) e hmem
  have hpd : parseNatDigits (e :: (es ++ rest)) 0 = some (k, rest) := by
    have := parseNatDigits_natToDecimal k rest hrest; rwa [he, List.cons_append] at this
  rw [he, List.cons_append]
  exact parseInt_digit_led e (es ++ rest) rest k hdig hpd

theorem parseInt_intToStringChars (n : Int) (rest : List Char) (hrest : NoLeadDigit rest) :
    parseInt (intToStringChars n ++ rest) = some (n, rest) := by
  cases n with
  | ofNat n =>
    have h : intToStringChars (Int.ofNat n) = natToDecimal n := by
      unfold intToStringChars; simp
    rw [h]; exact parseInt_natToDecimal n rest hrest
  | negSucc n =>
    have h : intToStringChars (Int.negSucc n) = '-' :: natToDecimal (n + 1) := by
      unfold intToStringChars; rw [if_pos (Int.negSucc_lt_zero n)]; rfl
    rw [h, List.cons_append]
    unfold parseInt
    simp only [parseNatDigits_natToDecimal (n + 1) rest hrest]
    congr 1

end NumberParse


section EncodeList

private def encSep (xs : List OmegaJson) : List Char :=
  match xs with
  | [] => []
  | [v] => jcsEncodeChars v
  | v :: w :: ws => jcsEncodeChars v ++ ',' :: encSep (w :: ws)

private def encObjSep (kvs : List (String × OmegaJson)) : List Char :=
  match kvs with
  | [] => []
  | [kv] => encObjPairChars kv
  | kv :: kv' :: kvs' => encObjPairChars kv ++ ',' :: encObjSep (kv' :: kvs')

theorem encSep_nil : encSep [] = [] := rfl

theorem encSep_cons (v : OmegaJson) (vs : List OmegaJson) :
    encSep (v :: vs) =
      jcsEncodeChars v ++ (match vs with | [] => [] | w :: ws => ',' :: encSep (w :: ws)) := by
  cases vs <;> simp [encSep]

theorem encObjSep_nil : encObjSep [] = [] := rfl

theorem encObjSep_cons (kv : String × OmegaJson) (kvs : List (String × OmegaJson)) :
    encObjSep (kv :: kvs) =
      encObjPairChars kv ++
        (match kvs with | [] => [] | kv' :: kvs' => ',' :: encObjSep (kv' :: kvs')) := by
  cases kvs <;> simp [encObjSep]

-- (Removed dead `String.intercalate`-based characterisation of `encObjSep`; the
-- live roundtrip uses the suffix form `encObjBody_eq_encObjSep` below instead.)

theorem encArrSuffix_cons (v : OmegaJson) (vs : List OmegaJson) :
    encArrSuffix (v :: vs) = ',' :: jcsEncodeChars v ++ encArrSuffix vs := by
  cases vs <;> dsimp [encArrSuffix] <;> rfl


theorem encObjSuffix_cons (kv : String × OmegaJson) (kvs : List (String × OmegaJson)) :
    encObjSuffix (kv :: kvs) = ',' :: encObjPairChars kv ++ encObjSuffix kvs := by
  cases kvs <;> dsimp [encObjSuffix, encObjPairChars] <;> rfl

theorem encArrBody_cons (v : OmegaJson) (vs : List OmegaJson) :
    encArrBody (v :: vs) = jcsEncodeChars v ++ encArrSuffix vs := rfl

theorem encObjBody_cons (kv : String × OmegaJson) (kvs : List (String × OmegaJson)) :
    encObjBody (kv :: kvs) = encObjPairChars kv ++ encObjSuffix kvs := rfl


theorem encArrBody_eq_encSep (xs : List OmegaJson) :
    encArrBody xs = encSep xs ++ [']'] := by
  induction xs with
  | nil => rfl
  | cons v xs ih =>
    rw [encArrBody_cons]
    cases xs with
    | nil => simp [encArrSuffix, encSep]
    | cons w ws =>
      have ih' : jcsEncodeChars w ++ encArrSuffix ws = encSep (w :: ws) ++ [']'] := by
        rw [← encArrBody_cons]; exact ih
      rw [encArrSuffix_cons, encSep_cons]
      simp only [List.cons_append, List.append_assoc, ih']

theorem encObjBody_eq_encObjSep (kvs : List (String × OmegaJson)) :
    encObjBody kvs = encObjSep kvs ++ ['}'] := by
  induction kvs with
  | nil => rfl
  | cons kv kvs ih =>
    rw [encObjBody_cons]
    cases kvs with
    | nil => simp [encObjSuffix, encObjSep]
    | cons kv' kvs' =>
      have ih' : encObjPairChars kv' ++ encObjSuffix kvs' = encObjSep (kv' :: kvs') ++ ['}'] := by
        rw [← encObjBody_cons]; exact ih
      rw [encObjSuffix_cons, encObjSep_cons]
      simp only [List.cons_append, List.append_assoc, ih']

theorem jcsEncodeChars_arr (xs : List OmegaJson) :
    jcsEncodeChars (OmegaJson.arr xs) = '[' :: encArrBody xs := rfl


theorem jcsEncodeChars_obj (kvs : List (String × OmegaJson)) :
    jcsEncodeChars (OmegaJson.obj kvs) = '{' :: encObjBody kvs := rfl


-- Fuel bound: `nodeCount v` is strictly below the encoded length (+1), with the
-- suffix/body length helpers proved in the same mutual block since the encoder and
-- `nodeCount` recurse together through `OmegaJson`.
mutual
theorem nodeCount_lt_encode_len (v : OmegaJson) :
    nodeCount v < (jcsEncodeChars v).length + 1 := by
  cases v with
  | null => simp [nodeCount, jcsEncodeChars]; decide
  | bool b => cases b <;> (simp [nodeCount, jcsEncodeChars]; decide)
  | int n =>
    simp only [nodeCount, jcsEncodeChars]
    cases n with
    | ofNat m =>
      by_cases hm : m = 0
      · subst hm; simp [intToStringChars, natToDecimal]
      · have hid : intToStringChars (Int.ofNat m) = natToDecimal m := by
          unfold intToStringChars; simp
        rw [hid]
        have hlen : 0 < (natToDecimal m).length := by
          rw [natToDecimal, if_neg hm, natToDecimalAux_step m hm [],
              natToDecimalAux_acc (m / 10) [Char.ofNat (m % 10 + '0'.toNat)]]
          simp
        omega
    | negSucc _ =>
      simp [intToStringChars, List.length_cons, Nat.zero_lt_succ]
  | str _ =>
    simp [nodeCount, jcsEncodeChars, jcsEscapeStringChars, List.length_cons, Nat.zero_lt_succ]
  | arr xs =>
    rw [jcsEncodeChars_arr]
    simp only [nodeCount, List.length_cons]
    have := nodeCountList_lt_arrBody xs
    omega
  | obj kvs =>
    rw [jcsEncodeChars_obj]
    simp only [nodeCount, List.length_cons]
    have := nodeCountObj_lt_objBody kvs
    omega

theorem nodeCountList_lt_arrBody (xs : List OmegaJson) :
    nodeCountList xs < (encArrBody xs).length + 1 := by
  match xs with
  | [] => simp [encArrBody, nodeCountList]
  | v :: vs =>
    rw [encArrBody_cons, List.length_append]
    have hv := nodeCount_lt_encode_len v
    have ht := nodeCountList_lt_arrSuffix vs
    simp only [nodeCountList]
    omega

theorem nodeCountList_lt_arrSuffix (xs : List OmegaJson) :
    nodeCountList xs < (encArrSuffix xs).length + 1 := by
  match xs with
  | [] => simp [encArrSuffix, nodeCountList]
  | v :: vs =>
    rw [encArrSuffix_cons, List.length_append, List.length_cons]
    have hv := nodeCount_lt_encode_len v
    have ht := nodeCountList_lt_arrSuffix vs
    simp only [nodeCountList]
    omega

theorem nodeCountObj_lt_objBody (kvs : List (String × OmegaJson)) :
    nodeCountObj kvs < (encObjBody kvs).length + 1 := by
  match kvs with
  | [] => simp [encObjBody, nodeCountObj]
  | ⟨k, v⟩ :: kvs' =>
    rw [encObjBody_cons, List.length_append, encObjPairChars]
    have hv := nodeCount_lt_encode_len v
    have ht := nodeCountObj_lt_objSuffix kvs'
    simp only [nodeCountObj, List.length_append, List.length_cons]
    omega

theorem nodeCountObj_lt_objSuffix (kvs : List (String × OmegaJson)) :
    nodeCountObj kvs < (encObjSuffix kvs).length + 1 := by
  match kvs with
  | [] => simp [encObjSuffix, nodeCountObj]
  | ⟨k, v⟩ :: kvs' =>
    rw [encObjSuffix_cons, encObjPairChars]
    have hv := nodeCount_lt_encode_len v
    have ht := nodeCountObj_lt_objSuffix kvs'
    simp only [nodeCountObj, List.length_append, List.length_cons]
    omega
end

end EncodeList

section CompositeParse

-- Dispatch helpers: at each `parseValueFuel` branch we must show the earlier
-- keyword/number/string probes fail before the correct constructor fires.
theorem takePrefix_head_ne {pre : String} {p : Char} {ps : List Char} (hpre : pre.toList = p :: ps)
    {c : Char} {t : List Char} (hne : c ≠ p) : takePrefix (c :: t) pre = none := by
  unfold takePrefix startsWith
  have hlen : pre.length = ps.length + 1 := by
    rw [← String.length_toList, hpre, List.length_cons]
  have : ¬ ((c :: t).take pre.length = pre.toList) := by
    rw [hpre, hlen, List.take_succ_cons]; simp [hne]
  simp [this]

theorem parseInt_cons_eq_none (c : Char) (t : List Char) (hd : isDigit c = false) (hm : c ≠ '-') :
    parseInt (c :: t) = none := by
  unfold parseInt
  split
  · rename_i rest heq; injection heq with h1 _; exact absurd h1 hm
  · rename_i c' s heq; injection heq with h1 _; subst h1; rw [if_neg (by simp [hd])]
  · rename_i heq; exact absurd heq (by simp)

theorem parseString_cons_eq_none (c : Char) (t : List Char) (h : c ≠ '"') :
    parseString (c :: t) = none := by
  unfold parseString
  split
  · rename_i rest heq; injection heq with h1 _; exact absurd h1 h
  · rfl

theorem isDigit_ne_keyword {c : Char} (h : isDigit c = true) :
    c ≠ 'n' ∧ c ≠ 't' ∧ c ≠ 'f' := by
  refine ⟨?_, ?_, ?_⟩ <;> (rintro rfl; exact absurd h (by decide))

theorem natToDecimal_head (k : Nat) : ∃ c t, natToDecimal k = c :: t ∧ isDigit c = true := by
  have hne : natToDecimal k ≠ [] := by
    cases k with
    | zero => simp [natToDecimal]
    | succ k =>
      rw [natToDecimal, if_neg (Nat.succ_ne_zero k), natToDecimalAux_step _ (Nat.succ_ne_zero k) [],
          natToDecimalAux_acc ((k + 1) / 10) [Char.ofNat ((k + 1) % 10 + '0'.toNat)]]
      simp
  obtain ⟨c, t, hc⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨c, t, hc, ?_⟩
  have hmem : c ∈ natToDecimal k := hc ▸ List.mem_cons_self
  cases k with
  | zero => rw [natToDecimal] at hmem; simp at hmem; subst hmem; decide
  | succ k =>
    rw [natToDecimal, if_neg (Nat.succ_ne_zero k)] at hmem
    exact natToDecimalAux_all_digits _ (Nat.succ_ne_zero k) c hmem

theorem intToStringChars_head (n : Int) :
    ∃ c t, intToStringChars n = c :: t ∧ c ≠ 'n' ∧ c ≠ 't' ∧ c ≠ 'f' := by
  cases n with
  | ofNat m =>
    obtain ⟨c, t, hc, hdig⟩ := natToDecimal_head m
    obtain ⟨h1, h2, h3⟩ := isDigit_ne_keyword hdig
    refine ⟨c, t, ?_, h1, h2, h3⟩
    rw [show intToStringChars (Int.ofNat m) = natToDecimal m from by unfold intToStringChars; simp, hc]
  | negSucc m =>
    refine ⟨'-', natToDecimal (m + 1), ?_, by decide, by decide, by decide⟩
    unfold intToStringChars; rw [if_pos (Int.negSucc_lt_zero m)]; rfl

theorem isDigit_ne_bracket {c : Char} (h : isDigit c = true) : c ≠ ']' ∧ c ≠ '}' := by
  refine ⟨?_, ?_⟩ <;> (rintro rfl; exact absurd h (by decide))

/-- The first byte of any value encoding is never `]` or `}` (so the array/object
    parsers take their value branch rather than closing early). -/
theorem jcsEncodeChars_head (v : OmegaJson) :
    ∃ c t, jcsEncodeChars v = c :: t ∧ c ≠ ']' ∧ c ≠ '}' := by
  cases v with
  | null => exact ⟨'n', _, rfl, by decide, by decide⟩
  | bool b => cases b <;> exact ⟨_, _, rfl, by decide, by decide⟩
  | int n =>
    cases n with
    | ofNat m =>
      obtain ⟨d, t', hd, hdig⟩ := natToDecimal_head m
      refine ⟨d, t', ?_, (isDigit_ne_bracket hdig).1, (isDigit_ne_bracket hdig).2⟩
      rw [show jcsEncodeChars (OmegaJson.int (Int.ofNat m)) = intToStringChars (Int.ofNat m) from rfl]
      unfold intToStringChars; simp [hd]
    | negSucc m =>
      refine ⟨'-', natToDecimal (m + 1), ?_, by decide, by decide⟩
      rw [show jcsEncodeChars (OmegaJson.int (Int.negSucc m)) = intToStringChars (Int.negSucc m) from rfl]
      unfold intToStringChars; rw [if_pos (Int.negSucc_lt_zero m)]; rfl
  | str s => exact ⟨'"', _, by rw [show jcsEncodeChars (OmegaJson.str s) = jcsEscapeStringChars s from rfl,
      jcsEscapeStringChars_spec, List.cons_append], by decide, by decide⟩
  | arr xs => exact ⟨'[', _, by rw [jcsEncodeChars_arr], by decide, by decide⟩
  | obj kvs => exact ⟨'{', _, by rw [jcsEncodeChars_obj], by decide, by decide⟩

theorem jcsEscapeStringChars_head (s : String) :
    ∃ t, jcsEscapeStringChars s = '"' :: t ∧ 1 ≤ t.length := by
  refine ⟨escapeStringChars s.toList ++ ['"'], ?_, ?_⟩
  · rw [jcsEscapeStringChars_spec, List.cons_append]
  · simp

theorem paf_val (f : Nat) (c : Char) (s : List Char) (acc : List OmegaJson) (hc : c ≠ ']') :
    parseArrayFuel (f + 1) (c :: s) acc =
      (match parseValueFuel f (c :: s) with
       | some (v, rest') => (match rest' with
           | ',' :: rest'' => parseArrayFuel f rest'' (v :: acc)
           | ']' :: rest'' => some (OmegaJson.arr (v :: acc).reverse, rest'')
           | _ => none)
       | none => none) := by
  rw [parseArrayFuel]
  · rfl
  · intro rest heq; injection heq with h1 _; exact hc h1

theorem pof_val (f : Nat) (c : Char) (s : List Char) (acc : List (String × OmegaJson)) (hc : c ≠ '}') :
    parseObjectFuel (f + 1) (c :: s) acc =
      (match parseObjectPairFuel f (c :: s) with
       | some (k, v, rest') => (match rest' with
           | ',' :: rest'' => parseObjectFuel f rest'' ((k, v) :: acc)
           | '}' :: rest'' => some (OmegaJson.obj ((k, v) :: acc).reverse, rest'')
           | _ => none)
       | none => none) := by
  rw [parseObjectFuel]
  · rfl
  · intro rest heq; injection heq with h1 _; exact hc h1

mutual
  theorem parse_encode (v : OmegaJson) (h : v.WF) :
      ∀ (fuel : Nat) (rest : List Char),
        NoLeadDigit rest →
        (jcsEncodeChars v).length < fuel →
        parseValueFuel fuel (jcsEncodeChars v ++ rest) = some (v, rest) := by
    intro fuel rest hrest hfuel
    have h1 : 1 ≤ (jcsEncodeChars v).length := by
      obtain ⟨c, t, hc, _, _⟩ := jcsEncodeChars_head v; rw [hc]; simp
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    cases v with
    | null =>
      simp only [jcsEncodeChars, parseValueFuel, takePrefix_append]
    | bool b =>
      cases b with
      | true =>
        simp only [jcsEncodeChars, parseValueFuel, takePrefix_append, takePrefix_true_not_null]
      | false =>
        simp only [jcsEncodeChars, parseValueFuel, takePrefix_append, takePrefix_false_not_null,
          takePrefix_false_not_true]
    | int n =>
      obtain ⟨c, t, hc, hcn, hct, hcf⟩ := intToStringChars_head n
      have hc' : intToStringChars n ++ rest = c :: (t ++ rest) := by rw [hc, List.cons_append]
      rw [show jcsEncodeChars (OmegaJson.int n) = intToStringChars n from rfl]
      simp only [parseValueFuel,
        show takePrefix (intToStringChars n ++ rest) "null" = none from by
          rw [hc']; exact takePrefix_head_ne (show ("null").toList = 'n' :: ['u','l','l'] from rfl) hcn,
        show takePrefix (intToStringChars n ++ rest) "true" = none from by
          rw [hc']; exact takePrefix_head_ne (show ("true").toList = 't' :: ['r','u','e'] from rfl) hct,
        show takePrefix (intToStringChars n ++ rest) "false" = none from by
          rw [hc']; exact takePrefix_head_ne (show ("false").toList = 'f' :: ['a','l','s','e'] from rfl) hcf,
        parseInt_intToStringChars n rest hrest]
    | str s =>
      have hc' : jcsEscapeStringChars s ++ rest = '"' :: (escapeStringChars s.toList ++ ['"'] ++ rest) := by
        rw [jcsEscapeStringChars_spec]; simp [List.cons_append, List.append_assoc]
      rw [show jcsEncodeChars (OmegaJson.str s) = jcsEscapeStringChars s from rfl]
      simp only [parseValueFuel,
        show takePrefix (jcsEscapeStringChars s ++ rest) "null" = none from by
          rw [hc']; exact takePrefix_head_ne (show ("null").toList = 'n' :: ['u','l','l'] from rfl) (by decide),
        show takePrefix (jcsEscapeStringChars s ++ rest) "true" = none from by
          rw [hc']; exact takePrefix_head_ne (show ("true").toList = 't' :: ['r','u','e'] from rfl) (by decide),
        show takePrefix (jcsEscapeStringChars s ++ rest) "false" = none from by
          rw [hc']; exact takePrefix_head_ne (show ("false").toList = 'f' :: ['a','l','s','e'] from rfl) (by decide),
        show parseInt (jcsEscapeStringChars s ++ rest) = none from by
          rw [hc']; exact parseInt_cons_eq_none '"' _ (by decide) (by decide),
        parseString_jcsEscapeString s rest]
    | arr xs =>
      cases h with
      | arr xs hxs =>
        rw [jcsEncodeChars_arr, List.cons_append]
        simp only [parseValueFuel,
          takePrefix_head_ne (show ("null").toList = 'n' :: ['u','l','l'] from rfl) (show ('[' : Char) ≠ 'n' by decide),
          takePrefix_head_ne (show ("true").toList = 't' :: ['r','u','e'] from rfl) (show ('[' : Char) ≠ 't' by decide),
          takePrefix_head_ne (show ("false").toList = 'f' :: ['a','l','s','e'] from rfl) (show ('[' : Char) ≠ 'f' by decide),
          parseInt_cons_eq_none '[' _ (by decide) (by decide),
          parseString_cons_eq_none '[' _ (by decide),
          show takePrefix ('[' :: (encArrBody xs ++ rest)) "[" = some (encArrBody xs ++ rest) from rfl]
        have hb : (encArrBody xs).length < f := by
          have := hfuel; rw [jcsEncodeChars_arr, List.length_cons] at this; omega
        simpa using arrBody xs f [] rest hxs hb
    | obj kvs =>
      cases h with
      | obj kvs hvs _ =>
        rw [jcsEncodeChars_obj, List.cons_append]
        simp only [parseValueFuel,
          takePrefix_head_ne (show ("null").toList = 'n' :: ['u','l','l'] from rfl) (show ('{' : Char) ≠ 'n' by decide),
          takePrefix_head_ne (show ("true").toList = 't' :: ['r','u','e'] from rfl) (show ('{' : Char) ≠ 't' by decide),
          takePrefix_head_ne (show ("false").toList = 'f' :: ['a','l','s','e'] from rfl) (show ('{' : Char) ≠ 'f' by decide),
          parseInt_cons_eq_none '{' _ (by decide) (by decide),
          parseString_cons_eq_none '{' _ (by decide),
          takePrefix_head_ne (show ("[").toList = '[' :: [] from rfl) (show ('{' : Char) ≠ '[' by decide),
          show takePrefix ('{' :: (encObjBody kvs ++ rest)) "{" = some (encObjBody kvs ++ rest) from rfl]
        have hb : (encObjBody kvs).length < f := by
          have := hfuel; rw [jcsEncodeChars_obj, List.length_cons] at this; omega
        simpa using objBody kvs f [] rest hvs hb
  termination_by sizeOf v

  theorem arrBody (xs : List OmegaJson) (fuel : Nat) (acc : List OmegaJson) (rest : List Char)
      (hx : ∀ x ∈ xs, x.WF) (hfuel : (encArrBody xs).length < fuel) :
      parseArrayFuel fuel (encArrBody xs ++ rest) acc
        = some (OmegaJson.arr (acc.reverse ++ xs), rest) := by
    match xs, hx, hfuel with
    | [], _, hfuel =>
      rw [show encArrBody ([] : List OmegaJson) = [']'] from rfl] at hfuel ⊢
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
      simp only [List.cons_append, List.nil_append, parseArrayFuel, List.append_nil]
    | v :: vs, hx, hfuel =>
      obtain ⟨c, t, hc, hcne, _⟩ := jcsEncodeChars_head v
      have hvpos : 1 ≤ (jcsEncodeChars v).length := by rw [hc]; simp
      rw [encArrBody_cons, List.length_append] at hfuel
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hes_pos : 1 ≤ (encArrSuffix vs).length := by
        cases vs with
        | nil => rw [show encArrSuffix ([] : List OmegaJson) = [']'] from rfl]; simp
        | cons w ws => rw [encArrSuffix_cons]; simp
      have hncv : (jcsEncodeChars v).length < f := by omega
      have hnld : NoLeadDigit (encArrSuffix vs ++ rest) := by
        cases vs with
        | nil => rw [show encArrSuffix ([] : List OmegaJson) = [']'] from rfl]
                 exact noLeadDigit_cons _ _ (by decide)
        | cons w ws => rw [encArrSuffix_cons]; exact noLeadDigit_cons _ _ (by decide)
      have hpv := parse_encode v (hx v (by simp)) f (encArrSuffix vs ++ rest) hnld hncv
      rw [encArrBody_cons, List.append_assoc]
      rw [hc, List.cons_append] at hpv ⊢
      rw [paf_val f c (t ++ (encArrSuffix vs ++ rest)) acc hcne, hpv]
      cases vs with
      | nil =>
        rw [show encArrSuffix ([] : List OmegaJson) = [']'] from rfl]
        simp [List.reverse_cons, List.append_assoc]
      | cons w ws =>
        have hwf : ∀ x ∈ (w :: ws), x.WF := fun x hx' => hx x (List.mem_cons_of_mem v hx')
        have hlen : (encArrBody (w :: ws)).length < f := by
          have hf2 := hfuel
          simp only [encArrSuffix_cons, List.length_append, List.length_cons] at hf2
          simp only [encArrBody_cons, List.length_append]
          omega
        simp only [encArrSuffix_cons, List.cons_append]
        rw [← encArrBody_cons, arrBody (w :: ws) f (v :: acc) rest hwf hlen]
        simp [List.reverse_cons, List.append_assoc]
  termination_by sizeOf xs
  decreasing_by
    all_goals simp_wf
    all_goals try simp only [Prod.mk.sizeOf_spec, List.cons.sizeOf_spec]
    all_goals omega

  theorem objBody (kvs : List (String × OmegaJson)) (fuel : Nat)
      (acc : List (String × OmegaJson)) (rest : List Char)
      (hx : ∀ kv ∈ kvs, kv.2.WF) (hfuel : (encObjBody kvs).length < fuel) :
      parseObjectFuel fuel (encObjBody kvs ++ rest) acc
        = some (OmegaJson.obj (acc.reverse ++ kvs), rest) := by
    match kvs, hx, hfuel with
    | [], _, hfuel =>
      rw [show encObjBody ([] : List (String × OmegaJson)) = ['}'] from rfl] at hfuel ⊢
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
      simp only [List.cons_append, List.nil_append, parseObjectFuel, List.append_nil]
    | (k, v) :: kvs1, hx, hfuel =>
      obtain ⟨tq, hq, htq⟩ := jcsEscapeStringChars_head k
      have hpair_head : encObjPairChars (k, v) = '"' :: (tq ++ ':' :: jcsEncodeChars v) := by
        rw [encObjPairChars, hq, List.cons_append]
      have hppos : (jcsEncodeChars v).length + 3 ≤ (encObjPairChars (k, v)).length := by
        rw [encObjPairChars, hq]; simp; omega
      have hbody3 : 3 ≤ (encObjBody ((k, v) :: kvs1)).length := by
        rw [encObjBody_cons, List.length_append]; omega
      obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 2 := ⟨fuel - 2, by omega⟩
      rw [encObjBody_cons, List.length_append] at hfuel
      have heos_pos : 1 ≤ (encObjSuffix kvs1).length := by
        cases kvs1 with
        | nil => rw [show encObjSuffix ([] : List (String × OmegaJson)) = ['}'] from rfl]; simp
        | cons kw kws => rw [encObjSuffix_cons]; simp
      have hncv : (jcsEncodeChars v).length < g := by omega
      have hnld : NoLeadDigit (encObjSuffix kvs1 ++ rest) := by
        cases kvs1 with
        | nil => rw [show encObjSuffix ([] : List (String × OmegaJson)) = ['}'] from rfl]
                 exact noLeadDigit_cons _ _ (by decide)
        | cons kw kws => rw [encObjSuffix_cons]; exact noLeadDigit_cons _ _ (by decide)
      have hpvv := parse_encode v (hx (k, v) (by simp)) g (encObjSuffix kvs1 ++ rest) hnld hncv
      have hkey : '"' :: ((tq ++ ':' :: jcsEncodeChars v) ++ (encObjSuffix kvs1 ++ rest))
          = jcsEscapeStringChars k ++ (':' :: jcsEncodeChars v ++ (encObjSuffix kvs1 ++ rest)) := by
        rw [hq]; simp [List.cons_append, List.append_assoc]
      rw [encObjBody_cons, List.append_assoc, hpair_head, List.cons_append,
          show g + 2 = (g + 1) + 1 from rfl, pof_val (g + 1) '"' _ acc (by decide),
          hkey, parseObjectPairFuel, parseString_jcsEscapeString]
      simp only [List.cons_append, hpvv]
      cases kvs1 with
      | nil =>
        rw [show encObjSuffix ([] : List (String × OmegaJson)) = ['}'] from rfl]
        simp [List.reverse_cons, List.append_assoc]
      | cons kw kws =>
        have hwf : ∀ x ∈ (kw :: kws), x.2.WF := fun x hx' => hx x (List.mem_cons_of_mem (k, v) hx')
        have hlen : (encObjBody (kw :: kws)).length < g + 1 := by
          have hf2 := hfuel
          simp only [encObjSuffix_cons, List.length_append, List.length_cons] at hf2
          simp only [encObjBody_cons, List.length_append]
          omega
        simp only [encObjSuffix_cons, List.cons_append]
        rw [← encObjBody_cons, objBody (kw :: kws) (g + 1) ((k, v) :: acc) rest hwf hlen]
        simp [List.reverse_cons, List.append_assoc]
  termination_by sizeOf kvs
  decreasing_by
    all_goals simp_wf
    all_goals try simp only [Prod.mk.sizeOf_spec, List.cons.sizeOf_spec]
    all_goals omega
end

end CompositeParse

section Main

theorem decode_encode (v : OmegaJson) (h : v.WF) :
    jcsDecode (jcsEncode v) = some v := by
  unfold jcsDecode parseValue parseFuel
  have hlen := nodeCount_lt_encode_len v
  have hparse := parse_encode v h ((jcsEncodeChars v).length + 1) [] hlen
  rw [← jcsEncode_toList] at hparse
  simpa [String.toList, List.append_nil] using hparse

theorem jcsEncode_injective (v w : OmegaJson) (hv : v.WF) (hw : w.WF)
    (h : jcsEncode v = jcsEncode w) : v = w := by
  have hdec : jcsDecode (jcsEncode v) = jcsDecode (jcsEncode w) := by rw [h]
  rw [decode_encode v hv, decode_encode w hw] at hdec
  exact Option.some_inj.mp hdec

theorem canonicalBytesJCS_injective (v w : OmegaJson) (hv : v.WF) (hw : w.WF)
    (h : canonicalBytesJCS v = canonicalBytesJCS w) : v = w := by
  apply jcsEncode_injective v w hv hw
  simp only [canonicalBytesJCS, String.toUTF8_eq_toByteArray] at h
  exact (String.toByteArray_inj.mp h)

#print axioms parse_encode
#print axioms decode_encode
#print axioms jcsEncode_injective
#print axioms canonicalBytesJCS_injective

end Main

end OmegaJCS
