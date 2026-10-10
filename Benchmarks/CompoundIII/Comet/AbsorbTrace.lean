import Benchmarks.CompoundIII.Comet.AbsorbBeforePointsModel
import Benchmarks.CompoundIII.Comet.AbsorbPointsModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

inductive AbsorbTrace (v : CometWithExtendedAssetListImmutables) (cd : ByteArray)
    (addr : AccountAddress) (evm : State) : InternalOutcome → Prop where
  | reverted (ht : AbsorbBeforePointsTrace v cd evm .reverted) : AbsorbTrace v cd addr evm .reverted
  | staticViolation (ht : AbsorbBeforePointsTrace v cd evm .staticViolation) :
      AbsorbTrace v cd addr evm .staticViolation
  | finished {evm' : State} (startGas endGas : UInt256)
      (ht : AbsorbBeforePointsTrace v cd evm (.ok evm')) :
      AbsorbTrace v cd addr evm
        (absorbAfterAccountsOutcome evm' addr (UInt256.ofNat (absorbArrayLength cd)) startGas endGas)

end Benchmarks.CompoundIII.Comet
