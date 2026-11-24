import Benchmarks.CompoundIII.Comet.WithdrawCollateralModel

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: emitting an event preserves state or halts a static execution.
def emitOutcome (evm : EVM.State) : InternalOutcome :=
  if evm.executionEnv.perm then .ok evm else .staticViolation

inductive WithdrawCollateralTransfer (fork : Ethereum.Fork) (asset recipient : AccountAddress) (amount : UInt256)
    (evm : EVM.State) : InternalOutcome → Prop where
  | failed (ht : TransferOutTrace fork asset recipient amount evm none) :
      WithdrawCollateralTransfer fork asset recipient amount evm .reverted
  | done {evm'} (ht : TransferOutTrace fork asset recipient amount evm (some evm')) :
      WithdrawCollateralTransfer fork asset recipient amount evm (emitOutcome evm')

inductive WithdrawCollateralCheck (fork : Ethereum.Fork) (v : CometWithExtendedAssetListImmutables)
    (src recipient asset : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    InternalOutcome → Prop where
  | failed (ht : CollateralCheckTrace fork v true src evm none) :
      WithdrawCollateralCheck fork v src recipient asset amount evm .reverted
  | rejected {evm'} (ht : CollateralCheckTrace fork v true src evm (some (evm', false))) :
      WithdrawCollateralCheck fork v src recipient asset amount evm .reverted
  | accepted {evm' result} (ht : CollateralCheckTrace fork v true src evm (some (evm', true)))
      (tail : WithdrawCollateralTransfer fork asset recipient amount evm' result) :
      WithdrawCollateralCheck fork v src recipient asset amount evm result

inductive WithdrawCollateralMember (fork : Ethereum.Fork) (v : CometWithExtendedAssetListImmutables)
    (src recipient asset : AccountAddress) (amount balance next : UInt256)
    (evm : EVM.State) (out : ByteArray) : InternalOutcome → Prop where
  | reverted (hm : assetMembershipResult evm src (calldataWord out 0) balance next = .reverted) :
      WithdrawCollateralMember fork v src recipient asset amount balance next evm out .reverted
  | staticViolation
      (hm : assetMembershipResult evm src (calldataWord out 0) balance next = .staticViolation) :
      WithdrawCollateralMember fork v src recipient asset amount balance next evm out .staticViolation
  | done {evm' result}
      (hm : assetMembershipResult evm src (calldataWord out 0) balance next = .ok evm')
      (tail : WithdrawCollateralCheck fork v src recipient asset amount evm' result) :
      WithdrawCollateralMember fork v src recipient asset amount balance next evm out result

inductive WithdrawCollateralTailTrace (fork : Ethereum.Fork) (v : CometWithExtendedAssetListImmutables)
    (src recipient asset : AccountAddress) (amount balance next : UInt256)
    (evm : EVM.State) : InternalOutcome → Prop where
  | failed (ht : AssetSearch fork v asset 0 evm none) :
      WithdrawCollateralTailTrace fork v src recipient asset amount balance next evm .reverted
  | found {evm' out result} (ht : AssetSearch fork v asset 0 evm (some (evm', out)))
      (hv : AssetValid out)
      (tail : WithdrawCollateralMember fork v src recipient asset amount balance next evm' out result) :
      WithdrawCollateralTailTrace fork v src recipient asset amount balance next evm result

inductive WithdrawCollateralTrace (fork : Ethereum.Fork) (v : CometWithExtendedAssetListImmutables)
    (src recipient asset : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    InternalOutcome → Prop where
  | reverted (hp : withdrawCollateralPrefixOutcome evm src asset amount = .reverted) :
      WithdrawCollateralTrace fork v src recipient asset amount evm .reverted
  | staticViolation (hp : withdrawCollateralPrefixOutcome evm src asset amount = .staticViolation) :
      WithdrawCollateralTrace fork v src recipient asset amount evm .staticViolation
  | done {evm' result} (hp : withdrawCollateralPrefixOutcome evm src asset amount = .ok evm')
      (tail : WithdrawCollateralTailTrace fork v src recipient asset amount
        (withdrawCollateralBalance evm src asset)
        (UInt256.sub (withdrawCollateralBalance evm src asset) amount) evm' result) :
      WithdrawCollateralTrace fork v src recipient asset amount evm result

end Benchmarks.CompoundIII.Comet
