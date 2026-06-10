import OmegaJCS.Encode
import OmegaJCS.Types
open OmegaJCS

example : nodeCount OmegaJson.null < (jcsEncodeChars OmegaJson.null).length + 1 := by
  native_decide
