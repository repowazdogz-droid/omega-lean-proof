import OmegaJCS.Encode
open OmegaJCS

theorem jcsEncodeChars_int (n : Int) :
    jcsEncodeChars (OmegaJson.int n) = intToStringChars n := by
  cases n <;> native_decide

theorem jcsEncodeChars_str (s : String) :
    jcsEncodeChars (OmegaJson.str s) = jcsEscapeStringChars s := by
  native_decide
