import Benchmarks.CompoundIII.Comet.TransferOutSource
import Benchmarks.CompoundIII.Comet.CollateralCheckSource
import Benchmarks.CompoundIII.Comet.SignedNegation
import Benchmarks.CompoundIII.Comet.InternalOutcome

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

inductive WithdrawBaseTransfer (v : CometWithExtendedAssetListImmutables)
    (recipient : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    InternalOutcome → Prop where
  | failed (ht : TransferOutTrace v.baseToken recipient amount evm none) :
      WithdrawBaseTransfer v recipient amount evm .reverted
  | done {evm'} (ht : TransferOutTrace v.baseToken recipient amount evm (some evm')) :
      WithdrawBaseTransfer v recipient amount evm (.ok evm')

def WithdrawBaseBorrowMin (v : CometWithExtendedAssetListImmutables)
    (balance : UInt256) : Prop := Int.ofNat v.baseBorrowMin.toNat ≤ -signedWord balance

instance (v : CometWithExtendedAssetListImmutables) (balance : UInt256) :
    Decidable (WithdrawBaseBorrowMin v balance) := by
  unfold WithdrawBaseBorrowMin; infer_instance

inductive WithdrawBaseTailTrace (v : CometWithExtendedAssetListImmutables)
    (src recipient : AccountAddress) (amount balance : UInt256) (evm : EVM.State) :
    InternalOutcome → Prop where
  | nonnegative {result} (hn : 0 ≤ signedWord balance)
      (tail : WithdrawBaseTransfer v recipient amount evm result) :
      WithdrawBaseTailTrace v src recipient amount balance evm result
  | tooSmall (hn : signedWord balance < 0) (hmin : ¬ WithdrawBaseBorrowMin v balance) :
      WithdrawBaseTailTrace v src recipient amount balance evm .reverted
  | failed (hn : signedWord balance < 0) (hmin : WithdrawBaseBorrowMin v balance)
      (hc : CollateralCheckTrace v true src evm none) :
      WithdrawBaseTailTrace v src recipient amount balance evm .reverted
  | rejected {evm'} (hn : signedWord balance < 0) (hmin : WithdrawBaseBorrowMin v balance)
      (hc : CollateralCheckTrace v true src evm (some (evm', false))) :
      WithdrawBaseTailTrace v src recipient amount balance evm .reverted
  | accepted {evm' result} (hn : signedWord balance < 0)
      (hmin : WithdrawBaseBorrowMin v balance)
      (hc : CollateralCheckTrace v true src evm (some (evm', true)))
      (tail : WithdrawBaseTransfer v recipient amount evm' result) :
      WithdrawBaseTailTrace v src recipient amount balance evm result

end Benchmarks.CompoundIII.Comet
