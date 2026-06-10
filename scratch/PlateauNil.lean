import OmegaJCS.Decode

namespace OmegaJCS

theorem parseStringCharsGoFuel_plateau_nil (acc : List Char) (fuel extra : Nat)
    (hfuel : fuel ≥ 1) (hextra : extra ≥ 1) (hle : extra ≤ fuel) :
    parseStringCharsGoFuel fuel [] acc = parseStringCharsGoFuel extra [] acc := by
  cases fuel with
  | zero => simp at hfuel
  | succ f =>
    cases extra with
    | zero => simp at hextra
    | succ e => simp [parseStringCharsGoFuel]

example (acc rest : List Char) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  trace_state
  dsimp [escapeCharList, escapeChar, parseStringChars, parseStringCharsFuelBound,
    parseStringCharsGoFuel]
  trace_state

end OmegaJCS
