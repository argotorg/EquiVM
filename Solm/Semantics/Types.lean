import Solm.Storage
import Solm.Value
import ABI.Decode

/-! Shared execution context: external-call ABI, configuration, and frames. -/

namespace Solm

open ABI

structure ExternalCallABI where
  encode? : Ident -> List Value -> Option EVM.Bytes
  decode? : Ident -> EVM.Bytes-> Option (List Value)

structure Config where
  storage : StorageLayout
  externalABI : ExternalCallABI
  abiDecodeMode : ABI.DecodeMode := ABI.DecodeMode.modern
  /- Initialisation code (creation bytecode ++ ABI-encoded constructor args) for a
     `new` of the named contract. -/
  creationCode : Ident -> List Value -> Option EVM.Bytes := fun _ _ => none

  /- Scheme for initialisation code (creation bytecode ++ ABI-encoded constructor args) for
     deployment of the contract's constructor -/
  selfDeployment : EVM.Bytes → List Value → Option EVM.Bytes

structure Frame where
  contract : ContractDecl
  locals : Store

end Solm
