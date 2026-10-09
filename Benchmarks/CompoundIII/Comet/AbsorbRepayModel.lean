import Benchmarks.CompoundIII.Comet.RepayAmountsModel
import Benchmarks.CompoundIII.Comet.SupplyBaseTotalsModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def absorbRepayOutcome (evm : State) (old next : UInt256) : InternalOutcome :=
  if RepayAmountsFits old next then
    supplyBaseTotalsOutcome evm (supplyAmount old next) (repayAmount old next)
  else .reverted

def absorbRepayBlock : List Stmt :=
  [.internalCall "repayAndSupplyAmount" [.var "oldPrincipal", .var "newPrincipal"] "__c12",
    .letDecl "repayAmount" (some (.elem (.int (.uint ⟨104, by decide⟩))))
      (.tupleGet (.var "__c12") 0),
    .letDecl "supplyAmount" (some (.elem (.int (.uint ⟨104, by decide⟩))))
      (.tupleGet (.var "__c12") 1)] ++ supplyBaseTotalsBlock

def absorbRepayFrame (frame : Frame) (old next : UInt256) : Frame :=
  { frame with
    locals := ((frame.locals.insert "__c12"
      (.tuple [.int (repayAmount old next).toNat, .int (supplyAmount old next).toNat])).insert
        "repayAmount" (.int (repayAmount old next).toNat)).insert
        "supplyAmount" (.int (supplyAmount old next).toNat) }

def absorbRepayResult (frame : Frame) (evm : State) (old next : UInt256) : ExecResult :=
  if RepayAmountsFits old next then
    supplyBaseTotalsResult (absorbRepayFrame frame old next) evm
      (supplyAmount old next) (repayAmount old next)
  else .reverted

end Benchmarks.CompoundIII.Comet
