import OmegaJCS.Decode

namespace OmegaJCS

theorem parseStringCharsGoFuel_plateau (rest : List Char) (acc : List Char) (fuel extra : Nat)
    (hfuel : fuel ≥ rest.length * 6 + 1) (hextra : extra ≥ rest.length * 6 + 1)
    (hle : extra ≤ fuel) :
    parseStringCharsGoFuel fuel rest acc = parseStringCharsGoFuel extra rest acc := by
  induction rest generalizing acc fuel extra with
  | nil =>
    cases fuel with
    | zero => simp at hfuel
    | succ f =>
      cases extra with
      | zero => simp at hextra
      | succ e => simp [parseStringCharsGoFuel]
  | cons c rest ih =>
    cases fuel with
    | zero => simp at hfuel
    | succ f =>
      cases extra with
      | zero => simp at hextra
      | succ e =>
        simp only [parseStringCharsGoFuel]
        have hf' : f ≥ rest.length * 6 + 1 := by omega
        have he' : e ≥ rest.length * 6 + 1 := by omega
        have hle' : e ≤ f := Nat.le_of_succ_le_succ hle
        rw [ih (acc ++ [c]) f e hf' he' hle']

theorem parseStringChars_escapeCharList_quote (acc rest : List Char) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  dsimp [escapeCharList, escapeChar, parseStringChars, parseStringCharsFuelBound,
    parseStringCharsGoFuel]
  have ht : ("\\\"").toList = ['\\', '"'] := rfl
  simp only [ht, List.cons_append, List.nil_append, List.length_cons]
  simp only [parseStringCharsGoFuel]
  exact parseStringCharsGoFuel_plateau rest (acc ++ ['"'])
    ((rest.length + 2) * 6) (rest.length * 6 + 1) (by omega) (by omega) (by omega)

end OmegaJCS
