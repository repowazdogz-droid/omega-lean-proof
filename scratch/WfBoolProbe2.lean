import OmegaJCS.Types

namespace OmegaJCS

example (xs : List OmegaJson) : OmegaJson.wfBool (.arr xs) = xs.all OmegaJson.wfBool := by
  delta OmegaJson.wfBool
  rfl

example (xs : List OmegaJson) : OmegaJson.wfBool (.arr xs) = xs.all OmegaJson.wfBool := by
  dsimp [OmegaJson.wfBool]
  rfl

example (xs : List OmegaJson) : OmegaJson.wfBool (.arr xs) = xs.all OmegaJson.wfBool := by
  unfold OmegaJson.wfBool
  rfl

example (xs : List OmegaJson) : OmegaJson.wfBool (.arr xs) = xs.all OmegaJson.wfBool := by
  cases xs <;> simp [OmegaJson.wfBool]

end OmegaJCS
