import OmegaJCS.Types

namespace OmegaJCS

def intToStringChars (n : Int) : List Char := if n < 0 then ['-'] else ['0']
def jcsEscapeStringChars (s : String) : List Char := '"' :: s.toList ++ ['"']

partial def jcsEncodeChars : OmegaJson → List Char
  | .null => "null".toList
  | .bool true => "true".toList
  | .bool false => "false".toList
  | .int n => intToStringChars n
  | .str s => jcsEscapeStringChars s
  | .arr _ => ['[']
  | .obj _ => ['{']

theorem t1 : jcsEncodeChars OmegaJson.null = "null".toList := rfl
theorem t2 (n : Int) : jcsEncodeChars (OmegaJson.int n) = intToStringChars n := rfl
