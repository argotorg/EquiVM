import EVM.Types
import ABI.Types
import Solm.Syntax

namespace Solm

/- Solm in-memory value representation. -/
inductive Value where
  /- Local variables can store unbounded integers -/
  | int : Int -> Value
  | bool : Bool -> Value
  | address : EVM.Address -> Value
  | struct : Ident -> List (Ident × Value) -> Value
  | array : List Value -> Value /- arrays can be copied to memory, so we need array values -/
  | tuple : List Value -> Value
  /- Fixed-size `bytesN`, carrying the ABI type index and the bytes in Solidity order. -/
  | fixedBytes : Fin 32 -> List UInt8 -> Value
  /- dynamic `bytes` (arbitrary-length byte string), e.g. low-level `.call` calldata -/
  | bytes : ByteArray -> Value
  /- Storage reference alias -/
  | storageRef : EvaledStorageRef -> StorageType -> Value
  | unit : Value
  deriving Inhabited

end Solm
