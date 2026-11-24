import Benchmarks.CompoundIII.Comet.AbsorbLoopModel
import Benchmarks.CompoundIII.Comet.AbsorbAfterLoopModel

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

inductive AbsorbLoopTailTrace (fork : Ethereum.Fork) (v : CometWithExtendedAssetListImmutables) (account : AccountAddress)
    (basic : UserBasicData) (old price : UInt256) (i : Nat) (delta : UInt256)
    (evm : State) : InternalOutcome → Prop where
  | loopReverted (ht : AbsorbLoopTrace fork v account basic.assets basic.reserved i delta evm .reverted) :
      AbsorbLoopTailTrace fork v account basic old price i delta evm .reverted
  | loopStatic (ht : AbsorbLoopTrace fork v account basic.assets basic.reserved i delta evm .staticViolation) :
      AbsorbLoopTailTrace fork v account basic old price i delta evm .staticViolation
  | finished {evm' finalDelta result}
      (ht : AbsorbLoopTrace fork v account basic.assets basic.reserved i delta evm (.ok evm' finalDelta))
      (hf : AbsorbAfterLoopTrace v account basic old finalDelta price evm' result) :
      AbsorbLoopTailTrace fork v account basic old price i delta evm result

def absorbLoopTailBlock : List Stmt := absorbLoopBlock ++ absorbAfterLoopBlock

end Benchmarks.CompoundIII.Comet
