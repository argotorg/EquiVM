import Benchmarks.CompoundIII.Comet.TransferCollateralModel
import Benchmarks.CompoundIII.Comet.WithdrawCollateralTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

inductive TransferCollateralCheck (v : CometWithExtendedAssetListImmutables)
    (src : AccountAddress) (evm : EVM.State) : InternalOutcome → Prop where
  | failed (ht : CollateralCheckTrace v true src evm none) :
      TransferCollateralCheck v src evm .reverted
  | rejected {evm'} (ht : CollateralCheckTrace v true src evm (some (evm', false))) :
      TransferCollateralCheck v src evm .reverted
  | accepted {evm'} (ht : CollateralCheckTrace v true src evm (some (evm', true))) :
      TransferCollateralCheck v src evm (emitOutcome evm')

inductive TransferCollateralDstMember (v : CometWithExtendedAssetListImmutables)
    (src dst : AccountAddress) (balance next : UInt256) (evm : EVM.State)
    (out : ByteArray) : InternalOutcome → Prop where
  | reverted (hm : assetMembershipResult evm dst (calldataWord out 0) balance next = .reverted) :
      TransferCollateralDstMember v src dst balance next evm out .reverted
  | staticViolation
      (hm : assetMembershipResult evm dst (calldataWord out 0) balance next = .staticViolation) :
      TransferCollateralDstMember v src dst balance next evm out .staticViolation
  | done {evm' result}
      (hm : assetMembershipResult evm dst (calldataWord out 0) balance next = .ok evm')
      (tail : TransferCollateralCheck v src evm' result) :
      TransferCollateralDstMember v src dst balance next evm out result

inductive TransferCollateralSrcMember (v : CometWithExtendedAssetListImmutables)
    (src dst : AccountAddress) (srcBalance srcNext dstBalance dstNext : UInt256)
    (evm : EVM.State) (out : ByteArray) : InternalOutcome → Prop where
  | reverted
      (hm : assetMembershipResult evm src (calldataWord out 0) srcBalance srcNext = .reverted) :
      TransferCollateralSrcMember v src dst srcBalance srcNext dstBalance dstNext evm out .reverted
  | staticViolation
      (hm : assetMembershipResult evm src (calldataWord out 0) srcBalance srcNext = .staticViolation) :
      TransferCollateralSrcMember v src dst srcBalance srcNext dstBalance dstNext evm out
        .staticViolation
  | done {evm' result}
      (hm : assetMembershipResult evm src (calldataWord out 0) srcBalance srcNext = .ok evm')
      (tail : TransferCollateralDstMember v src dst dstBalance dstNext evm' out result) :
      TransferCollateralSrcMember v src dst srcBalance srcNext dstBalance dstNext evm out result

inductive TransferCollateralTailTrace (v : CometWithExtendedAssetListImmutables)
    (src dst asset : AccountAddress) (srcBalance srcNext dstBalance dstNext : UInt256)
    (evm : EVM.State) : InternalOutcome → Prop where
  | failed (ht : AssetSearch v asset 0 evm none) :
      TransferCollateralTailTrace v src dst asset srcBalance srcNext dstBalance dstNext evm .reverted
  | found {evm' out result} (ht : AssetSearch v asset 0 evm (some (evm', out)))
      (hv : AssetValid out)
      (tail : TransferCollateralSrcMember v src dst srcBalance srcNext dstBalance dstNext
        evm' out result) :
      TransferCollateralTailTrace v src dst asset srcBalance srcNext dstBalance dstNext evm result

inductive TransferCollateralTrace (v : CometWithExtendedAssetListImmutables)
    (src dst asset : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    InternalOutcome → Prop where
  | reverted (hp : transferCollateralPrefixOutcome evm src dst asset amount = .reverted) :
      TransferCollateralTrace v src dst asset amount evm .reverted
  | staticViolation
      (hp : transferCollateralPrefixOutcome evm src dst asset amount = .staticViolation) :
      TransferCollateralTrace v src dst asset amount evm .staticViolation
  | done {evm' result} (hp : transferCollateralPrefixOutcome evm src dst asset amount = .ok evm')
      (tail : TransferCollateralTailTrace v src dst asset
        (withdrawCollateralBalance evm src asset) (transferCollateralSrcNext evm src asset amount)
        (withdrawCollateralBalance evm dst asset) (transferCollateralDstNext evm dst asset amount)
        evm' result) :
      TransferCollateralTrace v src dst asset amount evm result

end Benchmarks.CompoundIII.Comet
