import Init.Data.Nat.Bitwise.Lemmas
import OmegaJCS.Encode
import OmegaJCS.Decode
open OmegaJCS

private theorem land_f_lt16 (x : Nat) : x &&& 0xF < 16 :=
  Nat.lt_succ_iff.mpr (Nat.and_le_right (n := x) (m := 0xF))

private theorem hexDigit_spec (n : Nat) (hn : n < 16) :
    hexValue (hexDigit n) = some n := by revert n hn; decide +revert

private theorem hex4_recomb_small (n : Nat) (hn : n < 0x20) :
    (n >>> 12 &&& 0xF) * 4096 + (n >>> 8 &&& 0xF) * 256 + (n >>> 4 &&& 0xF) * 16 + (n &&& 0xF) = n := by
  revert n hn; decide +revert

private theorem hex4Lower_toList (n : Nat) :
    (hex4Lower n).toList =
      [hexDigit ((n >>> 12) &&& 0xF), hexDigit ((n >>> 8) &&& 0xF),
        hexDigit ((n >>> 4) &&& 0xF), hexDigit (n &&& 0xF)] := by
  unfold hex4Lower; simp [String.toList_ofList]

example (c : Char) (acc rest : List Char)
    (h1 : c ≠ '"') (h2 : c ≠ '\\') (h3 : c.toNat ≠ 0x08) (h4 : c.toNat ≠ 0x0C)
    (h5 : c.toNat ≠ 0x0A) (h6 : c.toNat ≠ 0x0D) (h7 : c.toNat ≠ 0x09) (hlt : c.toNat < 0x20) :
    parseStringChars (escapeCharList c ++ rest) acc =
      parseStringChars rest (acc ++ [c]) := by
  simp only [escapeCharList, escapeChar, beq_iff_eq, h1, h2, h3, h4, h5, h6, h7, if_false, hlt,
    if_pos, String.append, String.toList, List.cons_append, List.nil_append, hex4Lower, hex4Lower_toList]
  have h0 := hexDigit_spec ((c.toNat >>> 12) &&& 0xF) (land_f_lt16 _)
  have h1d := hexDigit_spec ((c.toNat >>> 8) &&& 0xF) (land_f_lt16 _)
  have h2d := hexDigit_spec ((c.toNat >>> 4) &&& 0xF) (land_f_lt16 _)
  have h3d := hexDigit_spec (c.toNat &&& 0xF) (land_f_lt16 _)
  simp only [parseStringChars, List.cons_append, List.nil_append, h0, h1d, h2d, h3d, hex4_recomb_small c.toNat (by omega)]
