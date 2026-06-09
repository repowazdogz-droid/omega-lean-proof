/- OMEGA JCS profile — value types and well-formedness (NOT a shipped Lake root).
   Lean `String`/`Char` carry Unicode scalar values only (no lone surrogates). -/
namespace OmegaJCS

def maxProfileInt : Nat := 9007199254740991

def intInProfileRange (n : Int) : Prop :=
  (-maxProfileInt : Int) ≤ n ∧ n ≤ maxProfileInt

def intInProfileRangeBool (n : Int) : Bool :=
  decide ((-maxProfileInt : Int) ≤ n ∧ n ≤ maxProfileInt)

inductive OmegaJson where
  | null
  | bool (b : Bool)
  | int (n : Int)
  | str (s : String)
  | arr (xs : List OmegaJson)
  | obj (kvs : List (String × OmegaJson))
  deriving Repr, Inhabited

partial def OmegaJson.beq : OmegaJson → OmegaJson → Bool
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .int a, .int b => a == b
  | .str a, .str b => a == b
  | .arr a, .arr b =>
      a.length == b.length && (List.zip a b).all fun p => OmegaJson.beq p.1 p.2
  | .obj a, .obj b =>
      a.length == b.length &&
        (List.zip a b).all fun p => p.1.1 == p.2.1 && OmegaJson.beq p.1.2 p.2.2
  | _, _ => false

instance : BEq OmegaJson where beq := OmegaJson.beq

def utf16EncodeScalar (c : Char) : List UInt16 := Id.run do
  let cp := c.toNat
  if cp < 0x10000 then
    return [UInt16.ofNat cp]
  else
    let x := cp - 0x10000
    let lo := (x % 0x400) + 0xDC00
    let hi := (x / 0x400) + 0xD800
    return [UInt16.ofNat hi, UInt16.ofNat lo]

def utf16Units (s : String) : List UInt16 :=
  s.toList.flatMap utf16EncodeScalar

def utf16UnitsLtBool : List UInt16 → List UInt16 → Bool
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | a :: as, b :: bs =>
      if a.toNat < b.toNat then true
      else if a = b then utf16UnitsLtBool as bs
      else false

def utf16UnitsLt (u v : List UInt16) : Prop :=
  utf16UnitsLtBool u v = true

def utf16LtBool (a b : String) : Bool :=
  utf16UnitsLtBool (utf16Units a) (utf16Units b)

def utf16Lt (a b : String) : Prop :=
  utf16LtBool a b = true

private def keysStrictSortedBool : List String → Bool
  | [] | [_] => true
  | a :: b :: rest => utf16LtBool a b && keysStrictSortedBool (b :: rest)

def objKeysStrictSorted (kvs : List (String × OmegaJson)) : Prop :=
  keysStrictSortedBool (kvs.map Prod.fst) = true

partial def OmegaJson.wfBool : OmegaJson → Bool
  | .null => true
  | .bool _ => true
  | .int n => intInProfileRangeBool n
  | .str _ => true
  | .arr xs => xs.all OmegaJson.wfBool
  | .obj kvs =>
      kvs.all (fun kv => kv.snd.wfBool) && keysStrictSortedBool (kvs.map Prod.fst)

def OmegaJson.WF (v : OmegaJson) : Prop := wfBool v = true

/-- UTF-16 code-unit lexicographic order is irreflexive (strict). -/
theorem utf16UnitsLtBool_irrefl : ∀ u, utf16UnitsLtBool u u = false := by
  intro u
  induction u with
  | nil => simp [utf16UnitsLtBool]
  | cons a as ih => simp [utf16UnitsLtBool, Nat.lt_irrefl, beq_self_eq_true, ih]

theorem utf16Lt_irrefl (s : String) : ¬ utf16Lt s s := by
  intro h
  have hf := utf16UnitsLtBool_irrefl (utf16Units s)
  simp only [utf16Lt, utf16LtBool, utf16UnitsLt] at h
  rw [hf] at h
  exact Bool.false_ne_true h

theorem utf16Units_eq_of_not_lt (u v : List UInt16) :
    utf16UnitsLtBool u v = false → utf16UnitsLtBool v u = false → u = v := by
  sorry

theorem utf16UnitsLt_trichotomy (u v : List UInt16) :
    utf16UnitsLtBool u v = true ∨ u = v ∨ utf16UnitsLtBool v u = true := by
  sorry

theorem utf16_eq_of_units_eq (a b : String) (h : utf16Units a = utf16Units b) : a = b := by
  sorry

theorem utf16Lt_trichotomy (a b : String) :
    utf16Lt a b ∨ a = b ∨ utf16Lt b a := by
  sorry

theorem utf16Lt_trans (a b c : String) (hab : utf16Lt a b) (hbc : utf16Lt b c) : utf16Lt a c := by
  sorry

section EvalSanity

#eval utf16Units "Ā"
#eval utf16Units "𝐀"
#eval utf16LtBool "Ā" "𝐀"
#eval utf16LtBool "peach" "péché"
#eval utf16LtBool "péché" "pêche"
#eval utf16LtBool "pêche" "sin"
#eval utf16LtBool "\n" "1"

end EvalSanity

end OmegaJCS
