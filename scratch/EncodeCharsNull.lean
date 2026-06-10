import OmegaJCS.Encode
open OmegaJCS

theorem jcsEncodeChars_null : jcsEncodeChars OmegaJson.null = "null".toList := by native_decide

theorem jcsEncodeChars_true : jcsEncodeChars (OmegaJson.bool true) = "true".toList := by native_decide

theorem jcsEncodeChars_false : jcsEncodeChars (OmegaJson.bool false) = "false".toList := by native_decide
