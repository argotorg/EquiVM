import ABI.Types

namespace ABI

structure Signature where
  name : String
  paramTypes : List ABIType
  deriving DecidableEq, Repr

-- TODO: maybe turn all of the following into a typeclass

def intTypeToSigStr : IntType → String
  | .uint b => "uint" ++ reprStr b
  | .sint b => "int" ++ reprStr b

def fixedTypeToSigStr : FixedType → String
  | .ufixed m n => "ufixed" ++ reprStr m ++ "x" ++ reprStr n
  | .fixed m n => "fixed" ++ reprStr m ++ "x" ++ reprStr n

def elemToSigStr : ElemType → String
  | .int i => intTypeToSigStr i
  | .bool => "bool"
  | .address => "address"
  | .bytes n => "bytes" ++ reprStr (n+1)
  | .fixed f => fixedTypeToSigStr f
  | .function => "function"

def abiToSigStr : ABIType → String
  | .elem t => elemToSigStr t
  | .array t n => abiToSigStr t ++ "[" ++ reprStr n ++ "]"
  | .tuple ts => "(" ++ (",".intercalate <| ts.map abiToSigStr) ++ ")"
  | .string => "string"
  | .bytes => "bytes"
  | .dynamicArray t => abiToSigStr t ++ "[]"

def printSignature (sig : Signature) : String :=
  let argList := ",".intercalate <| sig.paramTypes.map abiToSigStr
  sig.name ++ "(" ++ argList ++ ")"
