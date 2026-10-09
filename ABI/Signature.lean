import ABI.Types

/-! Function signatures and their canonical string form, as hashed for the 4-byte selector. -/

namespace ABI

structure Signature where
  name : String
  paramTypes : List ABIType
  deriving DecidableEq, Repr

-- TODO: maybe turn all of the following into a typeclass

def intTypeToSigStr : IntType → String
  | .uint b => "uint" ++ Nat.repr b.val
  | .sint b => "int" ++ Nat.repr b.val

def fixedTypeToSigStr : FixedType → String
  | .ufixed m n => "ufixed" ++ Nat.repr m.val ++ "x" ++ Nat.repr n.val
  | .fixed m n => "fixed" ++ Nat.repr m.val ++ "x" ++ Nat.repr n.val

def elemToSigStr : ElemType → String
  | .int i => intTypeToSigStr i
  | .bool => "bool"
  | .address => "address"
  | .bytes n => "bytes" ++ Nat.repr (n.val + 1)
  | .fixed f => fixedTypeToSigStr f
  | .function => "function"

def abiToSigStr : ABIType → String
  | .elem t => elemToSigStr t
  | .array t n => abiToSigStr t ++ "[" ++ Nat.repr n ++ "]"
  | .tuple ts => "(" ++ (",".intercalate <| ts.map abiToSigStr) ++ ")"
  | .string => "string"
  | .bytes => "bytes"
  | .dynamicArray t => abiToSigStr t ++ "[]"

def printSignature (sig : Signature) : String :=
  let argList := ",".intercalate <| sig.paramTypes.map abiToSigStr
  sig.name ++ "(" ++ argList ++ ")"
