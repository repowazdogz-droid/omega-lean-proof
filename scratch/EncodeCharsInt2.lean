import OmegaJCS.Encode
open OmegaJCS

theorem jcsEncodeChars_int (n : Int) :
    jcsEncodeChars (OmegaJson.int n) = intToStringChars n := by
  unfold jcsEncodeChars jcsEncode intToString intToStringChars
  cases n <;> rfl

theorem jcsEncodeChars_str (s : String) :
    jcsEncodeChars (OmegaJson.str s) = jcsEscapeStringChars s := by
  unfold jcsEncodeChars jcsEncode jcsEscapeString jcsEscapeStringChars
  have hq : "\"".toList = ['"'] := rfl
  rw [String.toList_append, String.toList_append, hq]
  simp [stringJoin_map_escapeChar]
