import OmegaJCS.Decode
import OmegaJCS.Encode

namespace OmegaJCS

private theorem hex4Lower_toList (n : Nat) :
    (hex4Lower n).toList =
      [hexDigit ((n >>> 12) &&& 0xF), hexDigit ((n >>> 8) &&& 0xF),
        hexDigit ((n >>> 4) &&& 0xF), hexDigit (n &&& 0xF)] := by
  unfold hex4Lower
  simp [String.toList_ofList]

private theorem hex4Lower_parseHex4 (n : Nat) (hn : n < 0x20) (rest : List Char) :
    parseHex4 ((hex4Lower n).toList ++ rest) = some (n, rest) := by sorry

example (c : Char) (acc rest : List Char) (hlt : c.toNat < 0x20)
    (h1 : c ≠ Char.ofNat 0x08) (h2 : c ≠ Char.ofNat 0x0C) (h3 : c ≠ Char.ofNat 0x0A)
    (h4 : c ≠ Char.ofNat 0x0D) (h5 : c ≠ Char.ofNat 0x09) :
    parseStringChars (escapeCharList c ++ rest) acc =
      parseStringChars rest (acc ++ [c]) := by
  simp [parseStringChars, escapeCharList, escapeChar, parseStringCharsGo, beq_iff_eq,
    h1, h2, h3, h4, h5, if_false, if_pos, String.append, String.toList, List.cons_append,
    hex4Lower, hex4Lower_toList]
  rw [hex4Lower_parseHex4 c.toNat (by omega) rest]
