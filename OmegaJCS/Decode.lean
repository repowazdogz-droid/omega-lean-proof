import OmegaJCS.Types
import OmegaJCS.Encode

namespace OmegaJCS

def startsWith (s : List Char) (pre : String) : Bool :=
  s.take pre.length = pre.toList

def takePrefix (s : List Char) (pre : String) : Option (List Char) :=
  if startsWith s pre then some (s.drop pre.length) else none

def isDigit (c : Char) : Bool :=
  '0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat

def parseNatDigits (s : List Char) (acc : Nat) : Option (Nat × List Char) :=
  match s with
  | [] => some (acc, [])
  | c :: rest =>
      if isDigit c then
        parseNatDigits rest (acc * 10 + (c.toNat - '0'.toNat))
      else
        some (acc, s)
termination_by s.length
decreasing_by
  all_goals simp only [List.length_cons]; apply Nat.lt_succ_self

def parseInt (s : List Char) : Option (Int × List Char) :=
  match s with
  | '-' :: rest =>
      match parseNatDigits rest 0 with
      | some (n, rest') => some (-Int.ofNat n, rest')
      | none => none
  | c :: _ =>
      if isDigit c then
        match parseNatDigits s 0 with
        | some (n, rest') => some (Int.ofNat n, rest')
        | none => none
      else none
  | [] => none

def hexValue (c : Char) : Option Nat :=
  if '0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat then some (c.toNat - '0'.toNat)
  else if 'a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'f'.toNat then some (c.toNat - 'a'.toNat + 10)
  else if 'A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'F'.toNat then some (c.toNat - 'A'.toNat + 10)
  else none

def parseHex4 (s : List Char) : Option (Nat × List Char) :=
  match s with
  | a :: b :: c :: d :: rest =>
      match hexValue a, hexValue b, hexValue c, hexValue d with
      | some ha, some hb, some hc, some hd =>
          some (ha * 4096 + hb * 256 + hc * 16 + hd, rest)
      | _, _, _, _ => none
  | _ => none

def parseStringChars (s : List Char) (acc : List Char) : Option (String × List Char) :=
  match s with
  | [] => none
  | '"' :: rest => some (String.ofList acc, rest)
  | '\\' :: rest =>
      match rest with
      | [] => none
      | '"' :: r => parseStringChars r (acc ++ ['"'])
      | '\\' :: r => parseStringChars r (acc ++ ['\\'])
      | 'b' :: r => parseStringChars r (acc ++ [Char.ofNat 0x08])
      | 'f' :: r => parseStringChars r (acc ++ [Char.ofNat 0x0C])
      | 'n' :: r => parseStringChars r (acc ++ [Char.ofNat 0x0A])
      | 'r' :: r => parseStringChars r (acc ++ [Char.ofNat 0x0D])
      | 't' :: r => parseStringChars r (acc ++ [Char.ofNat 0x09])
      | 'u' :: a :: b :: c :: d :: r =>
          match hexValue a, hexValue b, hexValue c, hexValue d with
          | some ha, some hb, some hc, some hd =>
              parseStringChars r (acc ++ [Char.ofNat (ha * 4096 + hb * 256 + hc * 16 + hd)])
          | _, _, _, _ => none
      | _ => none
  | c :: rest => parseStringChars rest (acc ++ [c])
termination_by s.length
decreasing_by
  all_goals simp only [List.length_cons]; omega

def parseString (s : List Char) : Option (String × List Char) :=
  match s with
  | '"' :: rest => parseStringChars rest []
  | _ => none

mutual
  def parseValueFuel : Nat → List Char → Option (OmegaJson × List Char)
    | 0, _ => none
    | fuel + 1, s =>
        if let some rest := takePrefix s "null" then
          some (OmegaJson.null, rest)
        else if let some rest := takePrefix s "true" then
          some (OmegaJson.bool true, rest)
        else if let some rest := takePrefix s "false" then
          some (OmegaJson.bool false, rest)
        else if let some (n, rest) := parseInt s then
          some (OmegaJson.int n, rest)
        else if let some (str, rest) := parseString s then
          some (OmegaJson.str str, rest)
        else if let some rest := takePrefix s "[" then
          parseArrayFuel fuel rest []
        else if let some rest := takePrefix s "{" then
          parseObjectFuel fuel rest []
        else none

  def parseArrayFuel : Nat → List Char → List OmegaJson → Option (OmegaJson × List Char)
    | 0, _, _ => none
    | fuel + 1, ']' :: rest, acc => some (OmegaJson.arr acc.reverse, rest)
    | fuel + 1, s, acc =>
        match parseValueFuel fuel s with
        | some (v, rest') =>
            match rest' with
            | ',' :: rest'' => parseArrayFuel fuel rest'' (v :: acc)
            | ']' :: rest'' => some (OmegaJson.arr (v :: acc).reverse, rest'')
            | _ => none
        | none => none

  def parseObjectPairFuel : Nat → List Char → Option (String × OmegaJson × List Char)
    | 0, _ => none
    | fuel + 1, s =>
        match parseString s with
        | some (k, rest) =>
            match rest with
            | ':' :: rest' =>
                match parseValueFuel fuel rest' with
                | some (v, rest'') => some (k, v, rest'')
                | none => none
            | _ => none
        | none => none

  def parseObjectFuel : Nat → List Char → List (String × OmegaJson) → Option (OmegaJson × List Char)
    | 0, _, _ => none
    | fuel + 1, '}' :: rest, acc => some (OmegaJson.obj acc.reverse, rest)
    | fuel + 1, s, acc =>
        match parseObjectPairFuel fuel s with
        | some (k, v, rest') =>
            match rest' with
            | ',' :: rest'' => parseObjectFuel fuel rest'' ((k, v) :: acc)
            | '}' :: rest'' => some (OmegaJson.obj ((k, v) :: acc).reverse, rest'')
            | _ => none
        | none => none
end

def parseFuel (s : List Char) : Nat := s.length + 1

def parseValue (s : List Char) : Option (OmegaJson × List Char) :=
  parseValueFuel (parseFuel s) s

def parseArray (s : List Char) (acc : List OmegaJson) : Option (OmegaJson × List Char) :=
  parseArrayFuel (parseFuel s) s acc

def parseObjectPair (s : List Char) : Option (String × OmegaJson × List Char) :=
  parseObjectPairFuel (parseFuel s) s

def parseObject (s : List Char) (acc : List (String × OmegaJson)) :
    Option (OmegaJson × List Char) :=
  parseObjectFuel (parseFuel s) s acc

def jcsDecode (s : String) : Option OmegaJson :=
  match parseValue s.toList with
  | some (v, []) => some v
  | _ => none

end OmegaJCS
