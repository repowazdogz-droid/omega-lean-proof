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

/-- Proof-friendly well-formedness used in roundtrip theorems. -/
inductive OmegaJson.WF : OmegaJson → Prop
  | null : WF OmegaJson.null
  | bool (b : Bool) : WF (OmegaJson.bool b)
  | int (n : Int) (h : intInProfileRange n) : WF (OmegaJson.int n)
  | str (s : String) : WF (OmegaJson.str s)
  | arr (xs : List OmegaJson) (h : ∀ x ∈ xs, WF x) : WF (OmegaJson.arr xs)
  | obj (kvs : List (String × OmegaJson)) (h : ∀ kv ∈ kvs, WF kv.2) (hs : objKeysStrictSorted kvs) :
      WF (OmegaJson.obj kvs)

mutual
  def nodeCount : OmegaJson → Nat
    | .null | .bool _ | .int _ | .str _ => 1
    | .arr xs => 1 + nodeCountList xs
    | .obj kvs => 1 + nodeCountObj kvs

  def nodeCountList : List OmegaJson → Nat
    | [] => 0
    | v :: vs => nodeCount v + nodeCountList vs

  def nodeCountObj : List (String × OmegaJson) → Nat
    | [] => 0
    | ⟨_, v⟩ :: kvs => nodeCount v + nodeCountObj kvs
end

theorem nodeCountList_map (xs : List OmegaJson) :
    nodeCountList xs = (xs.map nodeCount).sum := by
  induction xs with
  | nil => rfl
  | cons v vs ih => simp [nodeCountList, ih, List.sum_cons]

theorem nodeCountObj_map (kvs : List (String × OmegaJson)) :
    nodeCountObj kvs = (kvs.map (fun kv => nodeCount kv.2)).sum := by
  induction kvs with
  | nil => rfl
  | cons kv kvs ih => simp [nodeCountObj, ih, List.sum_cons]

theorem nodeCount_ge_one (v : OmegaJson) : 1 ≤ nodeCount v := by
  cases v <;> simp [nodeCount, nodeCountList, nodeCountObj]

theorem nodeCount_arr (xs : List OmegaJson) :
    nodeCount (OmegaJson.arr xs) = 1 + (xs.map nodeCount).sum := by
  simp [nodeCount, nodeCountList_map]

theorem nodeCount_obj (kvs : List (String × OmegaJson)) :
    nodeCount (OmegaJson.obj kvs) = 1 + (kvs.map (fun kv => nodeCount kv.2)).sum := by
  simp [nodeCount, nodeCountObj_map]

theorem nodeCount_lt_arr_cons (v : OmegaJson) (vs : List OmegaJson) :
    nodeCount v < nodeCount (OmegaJson.arr (v :: vs)) := by
  simp [nodeCount, nodeCountList]
  omega

theorem nodeCount_lt_obj_cons (kv : String × OmegaJson) (kvs : List (String × OmegaJson)) :
    nodeCount kv.2 < nodeCount (OmegaJson.obj (kv :: kvs)) := by
  simp [nodeCount, nodeCountObj]
  omega

theorem arr_wf_all (xs : List OmegaJson) (h : (OmegaJson.arr xs).WF) :
    ∀ x ∈ xs, x.WF := by
  cases h
  assumption

theorem obj_wf_values (kvs : List (String × OmegaJson)) (h : (OmegaJson.obj kvs).WF) :
    ∀ kv ∈ kvs, kv.2.WF := by
  cases h
  assumption

/-- UTF-16 code-unit lexicographic order is irreflexive (strict). -/
theorem utf16UnitsLtBool_irrefl : ∀ u, utf16UnitsLtBool u u = false := by
  intro u
  induction u with
  | nil => simp [utf16UnitsLtBool]
  | cons a as ih => simp [utf16UnitsLtBool, ih, Nat.lt_irrefl]

theorem utf16Lt_irrefl (s : String) : ¬ utf16Lt s s := by
  intro h
  have hf := utf16UnitsLtBool_irrefl (utf16Units s)
  simp only [utf16Lt, utf16LtBool, utf16UnitsLt] at h
  rw [hf] at h
  exact Bool.false_ne_true h

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
