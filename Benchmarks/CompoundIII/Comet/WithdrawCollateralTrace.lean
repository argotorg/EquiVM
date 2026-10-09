import Benchmarks.CompoundIII.Comet.WithdrawCollateralModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: emitting an event preserves state or halts a static execution.
def emitOutcome (evm : EVM.State) : InternalOutcome :=
  if evm.executionEnv.perm then .ok evm else .staticViolation

inductive WithdrawCollateralTransfer (asset recipient : AccountAddress) (amount : UInt256)
    (evm : EVM.State) : InternalOutcome → Prop where
  | failed (ht : TransferOutTrace asset recipient amount evm none) :
      WithdrawCollateralTransfer asset recipient amount evm .reverted
  | done {evm'} (ht : TransferOutTrace asset recipient amount evm (some evm')) :
      WithdrawCollateralTransfer asset recipient amount evm (emitOutcome evm')

inductive WithdrawCollateralCheck (v : CometWithExtendedAssetListImmutables)
    (src recipient asset : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    InternalOutcome → Prop where
  | failed (ht : CollateralCheckTrace v true src evm none) :
      WithdrawCollateralCheck v src recipient asset amount evm .reverted
  | rejected {evm'} (ht : CollateralCheckTrace v true src evm (some (evm', false))) :
      WithdrawCollateralCheck v src recipient asset amount evm .reverted
  | accepted {evm' result} (ht : CollateralCheckTrace v true src evm (some (evm', true)))
      (tail : WithdrawCollateralTransfer asset recipient amount evm' result) :
      WithdrawCollateralCheck v src recipient asset amount evm result

inductive WithdrawCollateralMember (v : CometWithExtendedAssetListImmutables)
    (src recipient asset : AccountAddress) (amount balance next : UInt256)
    (evm : EVM.State) (out : ByteArray) : InternalOutcome → Prop where
  | reverted (hm : assetMembershipResult evm src (calldataWord out 0) balance next = .reverted) :
      WithdrawCollateralMember v src recipient asset amount balance next evm out .reverted
  | staticViolation
      (hm : assetMembershipResult evm src (calldataWord out 0) balance next = .staticViolation) :
      WithdrawCollateralMember v src recipient asset amount balance next evm out .staticViolation
  | done {evm' result}
      (hm : assetMembershipResult evm src (calldataWord out 0) balance next = .ok evm')
      (tail : WithdrawCollateralCheck v src recipient asset amount evm' result) :
      WithdrawCollateralMember v src recipient asset amount balance next evm out result

inductive WithdrawCollateralTailTrace (v : CometWithExtendedAssetListImmutables)
    (src recipient asset : AccountAddress) (amount balance next : UInt256)
    (evm : EVM.State) : InternalOutcome → Prop where
  | failed (ht : AssetSearch v asset 0 evm none) :
      WithdrawCollateralTailTrace v src recipient asset amount balance next evm .reverted
  | found {evm' out result} (ht : AssetSearch v asset 0 evm (some (evm', out)))
      (hv : AssetValid out)
      (tail : WithdrawCollateralMember v src recipient asset amount balance next evm' out result) :
      WithdrawCollateralTailTrace v src recipient asset amount balance next evm result

inductive WithdrawCollateralTrace (v : CometWithExtendedAssetListImmutables)
    (src recipient asset : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    InternalOutcome → Prop where
  | reverted (hp : withdrawCollateralPrefixOutcome evm src asset amount = .reverted) :
      WithdrawCollateralTrace v src recipient asset amount evm .reverted
  | staticViolation (hp : withdrawCollateralPrefixOutcome evm src asset amount = .staticViolation) :
      WithdrawCollateralTrace v src recipient asset amount evm .staticViolation
  | done {evm' result} (hp : withdrawCollateralPrefixOutcome evm src asset amount = .ok evm')
      (tail : WithdrawCollateralTailTrace v src recipient asset amount
        (withdrawCollateralBalance evm src asset)
        (UInt256.sub (withdrawCollateralBalance evm src asset) amount) evm' result) :
      WithdrawCollateralTrace v src recipient asset amount evm result

end Benchmarks.CompoundIII.Comet
