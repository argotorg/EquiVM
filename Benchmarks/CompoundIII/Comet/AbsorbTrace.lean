import Benchmarks.CompoundIII.Comet.AbsorbBeforePointsModel
import Benchmarks.CompoundIII.Comet.AbsorbPointsModel

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

inductive AbsorbTrace (fork : Ethereum.Fork) (v : CometWithExtendedAssetListImmutables) (cd : ByteArray)
    (addr : AccountAddress) (evm : State) : InternalOutcome → Prop where
  | reverted (ht : AbsorbBeforePointsTrace fork v cd evm .reverted) : AbsorbTrace fork v cd addr evm .reverted
  | staticViolation (ht : AbsorbBeforePointsTrace fork v cd evm .staticViolation) :
      AbsorbTrace fork v cd addr evm .staticViolation
  | finished {evm' : State} (startGas endGas : UInt256)
      (ht : AbsorbBeforePointsTrace fork v cd evm (.ok evm')) :
      AbsorbTrace fork v cd addr evm
        (absorbAfterAccountsOutcome evm' addr (UInt256.ofNat (absorbArrayLength cd)) startGas endGas)

end Benchmarks.CompoundIII.Comet
