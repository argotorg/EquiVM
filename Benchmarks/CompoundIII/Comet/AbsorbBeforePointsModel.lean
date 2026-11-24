import Benchmarks.CompoundIII.Comet.AbsorbAccountsModel
import Benchmarks.CompoundIII.Comet.AccrueInternalModel
import Benchmarks.CompoundIII.Comet.PauseCommon

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

inductive AbsorbBeforePointsTrace (fork : Ethereum.Fork) (v : CometWithExtendedAssetListImmutables) (cd : ByteArray)
    (evm : State) : InternalOutcome → Prop where
  | paused (hp : (pauseBitWord evm ⟨3, by decide⟩).toNat ≠ 0) :
      AbsorbBeforePointsTrace fork v cd evm .reverted
  | accrueReverted (hp : (pauseBitWord evm ⟨3, by decide⟩).toNat = 0)
      (ha : accrueOutcome v evm = .reverted) :
      AbsorbBeforePointsTrace fork v cd evm .reverted
  | accrueStatic (hp : (pauseBitWord evm ⟨3, by decide⟩).toNat = 0)
      (ha : accrueOutcome v evm = .staticViolation) :
      AbsorbBeforePointsTrace fork v cd evm .staticViolation
  | accrued {evm' result} (hp : (pauseBitWord evm ⟨3, by decide⟩).toNat = 0)
      (ha : accrueOutcome v evm = .ok evm')
      (ht : AbsorbAccountsTrace fork v cd 0 evm' result) :
      AbsorbBeforePointsTrace fork v cd evm result

end Benchmarks.CompoundIII.Comet
