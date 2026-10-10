import Benchmarks.CompoundIII.Comet.AbsorbBalanceModel
import Benchmarks.CompoundIII.Comet.AbsorbFinishModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

inductive AbsorbAfterLoopTrace (v : CometWithExtendedAssetListImmutables)
    (account : AccountAddress) (basic : UserBasicData) (old delta price : UInt256)
    (evm : State) : InternalOutcome → Prop where
  | balanceReverted (hv : ¬ AbsorbBalanceValid v old delta price) :
      AbsorbAfterLoopTrace v account basic old delta price evm .reverted
  | finished {result} (hv : AbsorbBalanceValid v old delta price)
      (ht : AbsorbFinishTrace v evm account basic old (absorbBalanceWord v old delta price) price result) :
      AbsorbAfterLoopTrace v account basic old delta price evm result

def absorbAfterLoopBlock : List Stmt := absorbBalanceBlock ++ absorbFinishBlock

end Benchmarks.CompoundIII.Comet
