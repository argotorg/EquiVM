import Benchmarks.CompoundIII.Comet.AbsorbAccountsModel
import Benchmarks.CompoundIII.Comet.AccrueInternalModel
import Benchmarks.CompoundIII.Comet.PauseCommon

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

inductive AbsorbBeforePointsTrace (v : CometWithExtendedAssetListImmutables) (cd : ByteArray)
    (evm : State) : InternalOutcome → Prop where
  | paused (hp : (pauseBitWord evm ⟨3, by decide⟩).toNat ≠ 0) :
      AbsorbBeforePointsTrace v cd evm .reverted
  | accrueReverted (hp : (pauseBitWord evm ⟨3, by decide⟩).toNat = 0)
      (ha : accrueOutcome v evm = .reverted) :
      AbsorbBeforePointsTrace v cd evm .reverted
  | accrueStatic (hp : (pauseBitWord evm ⟨3, by decide⟩).toNat = 0)
      (ha : accrueOutcome v evm = .staticViolation) :
      AbsorbBeforePointsTrace v cd evm .staticViolation
  | accrued {evm' result} (hp : (pauseBitWord evm ⟨3, by decide⟩).toNat = 0)
      (ha : accrueOutcome v evm = .ok evm')
      (ht : AbsorbAccountsTrace v cd 0 evm' result) :
      AbsorbBeforePointsTrace v cd evm result

end Benchmarks.CompoundIII.Comet
