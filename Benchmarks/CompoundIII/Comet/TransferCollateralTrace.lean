import Benchmarks.CompoundIII.Comet.TransferCollateralModel
import Benchmarks.CompoundIII.Comet.WithdrawCollateralTrace

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

inductive TransferCollateralCheck (fork : Ethereum.Fork) (v : CometWithExtendedAssetListImmutables)
    (src : AccountAddress) (evm : EVM.State) : InternalOutcome → Prop where
  | failed (ht : CollateralCheckTrace fork v true src evm none) :
      TransferCollateralCheck fork v src evm .reverted
  | rejected {evm'} (ht : CollateralCheckTrace fork v true src evm (some (evm', false))) :
      TransferCollateralCheck fork v src evm .reverted
  | accepted {evm'} (ht : CollateralCheckTrace fork v true src evm (some (evm', true))) :
      TransferCollateralCheck fork v src evm (emitOutcome evm')

inductive TransferCollateralDstMember (fork : Ethereum.Fork) (v : CometWithExtendedAssetListImmutables)
    (src dst : AccountAddress) (balance next : UInt256) (evm : EVM.State)
    (out : ByteArray) : InternalOutcome → Prop where
  | reverted (hm : assetMembershipResult evm dst (calldataWord out 0) balance next = .reverted) :
      TransferCollateralDstMember fork v src dst balance next evm out .reverted
  | staticViolation
      (hm : assetMembershipResult evm dst (calldataWord out 0) balance next = .staticViolation) :
      TransferCollateralDstMember fork v src dst balance next evm out .staticViolation
  | done {evm' result}
      (hm : assetMembershipResult evm dst (calldataWord out 0) balance next = .ok evm')
      (tail : TransferCollateralCheck fork v src evm' result) :
      TransferCollateralDstMember fork v src dst balance next evm out result

inductive TransferCollateralSrcMember (fork : Ethereum.Fork) (v : CometWithExtendedAssetListImmutables)
    (src dst : AccountAddress) (srcBalance srcNext dstBalance dstNext : UInt256)
    (evm : EVM.State) (out : ByteArray) : InternalOutcome → Prop where
  | reverted
      (hm : assetMembershipResult evm src (calldataWord out 0) srcBalance srcNext = .reverted) :
      TransferCollateralSrcMember fork v src dst srcBalance srcNext dstBalance dstNext evm out .reverted
  | staticViolation
      (hm : assetMembershipResult evm src (calldataWord out 0) srcBalance srcNext = .staticViolation) :
      TransferCollateralSrcMember fork v src dst srcBalance srcNext dstBalance dstNext evm out
        .staticViolation
  | done {evm' result}
      (hm : assetMembershipResult evm src (calldataWord out 0) srcBalance srcNext = .ok evm')
      (tail : TransferCollateralDstMember fork v src dst dstBalance dstNext evm' out result) :
      TransferCollateralSrcMember fork v src dst srcBalance srcNext dstBalance dstNext evm out result

inductive TransferCollateralTailTrace (fork : Ethereum.Fork) (v : CometWithExtendedAssetListImmutables)
    (src dst asset : AccountAddress) (srcBalance srcNext dstBalance dstNext : UInt256)
    (evm : EVM.State) : InternalOutcome → Prop where
  | failed (ht : AssetSearch fork v asset 0 evm none) :
      TransferCollateralTailTrace fork v src dst asset srcBalance srcNext dstBalance dstNext evm .reverted
  | found {evm' out result} (ht : AssetSearch fork v asset 0 evm (some (evm', out)))
      (hv : AssetValid out)
      (tail : TransferCollateralSrcMember fork v src dst srcBalance srcNext dstBalance dstNext
        evm' out result) :
      TransferCollateralTailTrace fork v src dst asset srcBalance srcNext dstBalance dstNext evm result

inductive TransferCollateralTrace (fork : Ethereum.Fork) (v : CometWithExtendedAssetListImmutables)
    (src dst asset : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    InternalOutcome → Prop where
  | reverted (hp : transferCollateralPrefixOutcome evm src dst asset amount = .reverted) :
      TransferCollateralTrace fork v src dst asset amount evm .reverted
  | staticViolation
      (hp : transferCollateralPrefixOutcome evm src dst asset amount = .staticViolation) :
      TransferCollateralTrace fork v src dst asset amount evm .staticViolation
  | done {evm' result} (hp : transferCollateralPrefixOutcome evm src dst asset amount = .ok evm')
      (tail : TransferCollateralTailTrace fork v src dst asset
        (withdrawCollateralBalance evm src asset) (transferCollateralSrcNext evm src asset amount)
        (withdrawCollateralBalance evm dst asset) (transferCollateralDstNext evm dst asset amount)
        evm' result) :
      TransferCollateralTrace fork v src dst asset amount evm result

end Benchmarks.CompoundIII.Comet
