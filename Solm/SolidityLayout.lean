import EVM.Types
import ABI.Types
import ABI.Encode
import Solm.Value
import Solm.Storage

namespace Solm
open ABI

/-! Shared Solidity storage-layout primitives. Compile-time layout generation lives in `Solm.MetaSolidityLayout`. -/

def elemTypeSoliditySize (t : ElemType) : Fin 33 :=
  match t with
  | .bool => 1
  | .address => 20
  | .int it => intTypeSize it
  | .fixed ft => fixedTypeSize ft
  | .bytes n => ⟨n+1, by omega⟩
  | .function => 24

def checkBytesPacked (slot : EVM.Word) (state : EVM.State) : Bool :=
  let slot := EVM.storageLoad state state.executionEnv.codeOwner slot
  (slot.val % 2) == 0

def solidityBytesDataBaseSlot (baseSlot : EVM.Word) : EVM.Word :=
  Ethereum.uInt256OfByteArray (Ethereum.KEC baseSlot.toByteArray)

def solidityBytesDataSlot (baseSlot : EVM.Word) (wordIndex : Nat) : EVM.Word :=
  solidityBytesDataBaseSlot baseSlot + Ethereum.UInt256.ofNat wordIndex

/-- ABI-encode constructor arguments and append them to the pure initialization bytecode. -/
def genSolidityConstructorDeployment (params : List Param) (pureInit : EVM.Bytes) (values : List Value) : Option EVM.Bytes := do
  let args ← ABI.encodeABIValues? (params.map Param.ty) values
  pureInit ++ args.toByteArray

end Solm
