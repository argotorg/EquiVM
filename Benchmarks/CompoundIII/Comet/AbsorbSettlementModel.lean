import Benchmarks.CompoundIII.Comet.AbsorbClearMembers
import Benchmarks.CompoundIII.Comet.AbsorbRepayModel
import Benchmarks.CompoundIII.Comet.AbsorbDebtModel
import Benchmarks.CompoundIII.Comet.AbsorbEventsSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

inductive AbsorbSettlementTrace (v : CometWithExtendedAssetListImmutables) (evm : State)
    (account : AccountAddress) (oldPrincipal principal old next price : UInt256) :
    InternalOutcome → Prop where
  | repayReverted
      (hr : absorbRepayOutcome (absorbClearState evm account) oldPrincipal principal = .reverted) :
      AbsorbSettlementTrace v evm account oldPrincipal principal old next price .reverted
  | repayStatic
      (hr : absorbRepayOutcome (absorbClearState evm account) oldPrincipal principal = .staticViolation) :
      AbsorbSettlementTrace v evm account oldPrincipal principal old next price .staticViolation
  | debtReverted (totaled : State)
      (hr : absorbRepayOutcome (absorbClearState evm account) oldPrincipal principal = .ok totaled)
      (hd : ¬ AbsorbDebtValid v old next price) :
      AbsorbSettlementTrace v evm account oldPrincipal principal old next price .reverted
  | ok (totaled : State)
      (hr : absorbRepayOutcome (absorbClearState evm account) oldPrincipal principal = .ok totaled)
      (hd : AbsorbDebtValid v old next price) :
      AbsorbSettlementTrace v evm account oldPrincipal principal old next price (.ok totaled)

def absorbSettlementBlock : List Stmt :=
  absorbClearBlock ++ (absorbRepayBlock ++ (absorbDebtArithmeticBlock ++ absorbEventsBlock))

end Benchmarks.CompoundIII.Comet
