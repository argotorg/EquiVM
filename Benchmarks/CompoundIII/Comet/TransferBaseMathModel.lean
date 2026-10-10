import Benchmarks.CompoundIII.Comet.WithdrawBaseMathModel
import Benchmarks.CompoundIII.Comet.SupplyBaseMathModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def TransferBaseBalanceFits (evm : EVM.State) (srcPrincipal dstPrincipal amount : UInt256) : Prop :=
  WithdrawBaseBalanceFits evm srcPrincipal amount ∧ SupplyBaseBalanceFits evm dstPrincipal amount

def TransferBaseMathFits (evm : EVM.State) (srcPrincipal dstPrincipal amount : UInt256) : Prop :=
  WithdrawBaseMathFits evm srcPrincipal amount ∧ SupplyBaseMathFits evm dstPrincipal amount

instance (evm : EVM.State) (srcPrincipal dstPrincipal amount : UInt256) :
    Decidable (TransferBaseBalanceFits evm srcPrincipal dstPrincipal amount) := by
  unfold TransferBaseBalanceFits; infer_instance

instance (evm : EVM.State) (srcPrincipal dstPrincipal amount : UInt256) :
    Decidable (TransferBaseMathFits evm srcPrincipal dstPrincipal amount) := by
  unfold TransferBaseMathFits; infer_instance

def transferBaseBalanceStack (evm : EVM.State)
    (srcPrincipal dstPrincipal srcPtr dstPtr src dst amount ret : UInt256)
    (R : List UInt256) : List UInt256 :=
  [supplyBaseBalance evm dstPrincipal amount, srcPtr, dstPtr,
    withdrawBaseBalance evm srcPrincipal amount,
    UInt256.signextend (UInt256.ofNat 12) dstPrincipal, src,
    UInt256.signextend (UInt256.ofNat 12) srcPrincipal, dst, ret] ++ R

def transferBasePrincipalStack (evm : EVM.State)
    (srcPrincipal dstPrincipal srcPtr dstPtr src dst amount ret : UInt256)
    (R : List UInt256) : List UInt256 :=
  [supplyBasePrincipal evm dstPrincipal amount, withdrawBasePrincipal evm srcPrincipal amount,
    srcPtr, withdrawBasePrincipal evm srcPrincipal amount, dstPtr,
    withdrawBaseBalance evm srcPrincipal amount,
    UInt256.signextend (UInt256.ofNat 12) dstPrincipal, src,
    UInt256.signextend (UInt256.ofNat 12) srcPrincipal, dst, ret] ++ R

def transferBaseMathStack (evm : EVM.State)
    (srcPrincipal dstPrincipal srcPtr dstPtr src dst amount ret : UInt256)
    (R : List UInt256) : List UInt256 :=
  [supplyAmount dstPrincipal (supplyBasePrincipal evm dstPrincipal amount),
    repayAmount dstPrincipal (supplyBasePrincipal evm dstPrincipal amount),
    withdrawBasePrincipal evm srcPrincipal amount, srcPtr,
    supplyBasePrincipal evm dstPrincipal amount, dstPtr,
    withdrawBaseBalance evm srcPrincipal amount,
    withdrawSupplyAmount srcPrincipal (withdrawBasePrincipal evm srcPrincipal amount), src,
    withdrawBorrowAmount srcPrincipal (withdrawBasePrincipal evm srcPrincipal amount), dst, ret] ++ R

end Benchmarks.CompoundIII.Comet
