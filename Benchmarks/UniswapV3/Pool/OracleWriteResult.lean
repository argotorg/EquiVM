import Benchmarks.UniswapV3.Pool.OracleWriteSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def oracleWriteValid (a : OracleWriteArgs) (evm : EVM.State) : Prop :=
  a.index.toNat < 65535 ∧ (oracleWriteSame a evm = true ∨ (oracleWriteCardinality a).toNat ≠ 0)

def oracleWriteResultIndex (a : OracleWriteArgs) (evm : EVM.State) : UInt256 :=
  if oracleWriteSame a evm then a.index else oracleWriteIndex a

def oracleWriteResultCardinality (a : OracleWriteArgs) (evm : EVM.State) : UInt256 :=
  if oracleWriteSame a evm then a.cardinality else oracleWriteCardinality a

def oracleWriteState (a : OracleWriteArgs) (evm : EVM.State) : EVM.State :=
  if oracleWriteSame a evm then evm else oracleWriteFinalState a evm

def oracleWriteReturnFrame (imms : Store) (a : OracleWriteArgs) (evm : EVM.State) : Frame :=
  if oracleWriteSame a evm then oracleWriteLastFrame imms a evm
  else oracleWriteTransformedFrame imms a evm

theorem oracleWriteSourceReturns (imms : Store) (evm : EVM.State) (a : OracleWriteArgs)
    (hv : oracleWriteValid a evm) (hfit : a.Fits) :
    ExecFuncBody config (oracleWriteFrame imms a) evm oracleWriteFunction.body
      (.returned (oracleWriteReturnFrame imms a evm) (oracleWriteState a evm)
        (some [.int (Int.ofNat (oracleWriteResultIndex a evm).toNat),
          .int (Int.ofNat (oracleWriteResultCardinality a evm).toNat)])) := by
  cases hs : oracleWriteSame a evm
  · have hn : (oracleWriteCardinality a).toNat ≠ 0 := hv.2.resolve_left (by simp only [hs]; decide)
    simpa only [oracleWriteReturnFrame, oracleWriteState, oracleWriteResultIndex,
      oracleWriteResultCardinality, hs, Bool.false_eq_true, if_false] using
      oracleWriteReturns imms evm a hv.1 hs hn hfit
  · simpa only [oracleWriteReturnFrame, oracleWriteState, oracleWriteResultIndex,
      oracleWriteResultCardinality, hs, if_true] using oracleWriteSameReturns imms evm a hv.1 hs

theorem oracleWriteSourceReverts (imms : Store) (evm : EVM.State) (a : OracleWriteArgs)
    (hv : ¬ oracleWriteValid a evm) :
    ExecFuncBody config (oracleWriteFrame imms a) evm oracleWriteFunction.body .reverted := by
  by_cases hi : a.index.toNat < 65535
  · have hs : oracleWriteSame a evm = false := by
      cases he : oracleWriteSame a evm
      · rfl
      · exact False.elim (hv ⟨hi, Or.inl he⟩)
    have hz : (oracleWriteCardinality a).toNat = 0 := by
      by_contra hn
      exact hv ⟨hi, Or.inr hn⟩
    exact oracleWriteCardinalityReverts imms evm a hi hs hz
  · exact oracleWriteReadReverts imms evm a hi

theorem oracleWriteState_executionEnv (a : OracleWriteArgs) (evm : EVM.State) :
    (oracleWriteState a evm).executionEnv = evm.executionEnv := by
  unfold oracleWriteState
  split
  · rfl
  · exact oracleObservationState_executionEnv _ _ _

theorem oracleWriteResultIndex_lt (a : OracleWriteArgs) (evm : EVM.State)
    (hv : oracleWriteValid a evm) (hfit : a.Fits) :
    (oracleWriteResultIndex a evm).toNat < 65535 := by
  cases hs : oracleWriteSame a evm
  · simp only [oracleWriteResultIndex, hs, Bool.false_eq_true, if_false]
    exact oracleWriteIndex_lt a hfit (hv.2.resolve_left (by simp only [hs]; decide))
  · simpa only [oracleWriteResultIndex, hs, if_true] using hv.1

theorem oracleWriteResultCardinality_lt (a : OracleWriteArgs) (evm : EVM.State)
    (hfit : a.Fits) : (oracleWriteResultCardinality a evm).toNat < 2 ^ 16 := by
  cases hs : oracleWriteSame a evm
  · simpa only [oracleWriteResultCardinality, hs, Bool.false_eq_true, if_false] using
      oracleWriteCardinality_lt a hfit
  · simpa only [oracleWriteResultCardinality, hs, if_true] using hfit.2.2.2.2.1

end Benchmarks.UniswapV3.Pool
