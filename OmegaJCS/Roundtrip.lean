import OmegaJCS.Types
import OmegaJCS.Encode
import OmegaJCS.Decode

namespace OmegaJCS

/-- Roundtrip on encoder output (verification artifact; decoder is not a general JSON parser). -/

theorem decode_encode (v : OmegaJson) (h : v.WF) :
    jcsDecode (jcsEncode v) = some v := by
  sorry

theorem jcsEncode_injective (v w : OmegaJson) :
    v.WF → w.WF → jcsEncode v = jcsEncode w → v = w := by
  sorry

theorem canonicalBytesJCS_injective (v w : OmegaJson) :
    v.WF → w.WF → canonicalBytesJCS v = canonicalBytesJCS w → v = w := by
  sorry

#print axioms decode_encode
#print axioms jcsEncode_injective
#print axioms canonicalBytesJCS_injective

end OmegaJCS
