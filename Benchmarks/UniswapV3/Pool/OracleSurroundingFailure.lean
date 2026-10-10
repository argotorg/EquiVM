import Benchmarks.UniswapV3.Pool.OracleSurroundingSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

inductive OracleSurroundingFailure (time target index card : UInt256)
    (σ : AccountMap) (I : ExecutionEnv) : Prop where
  | index : ¬ index.toNat < 65535 → OracleSurroundingFailure time target index card σ I
  | zero : index.toNat < 65535 → card = ⟨0⟩ →
      oracleSurroundingFirst time target index σ I = false →
      OracleSurroundingFailure time target index card σ I
  | old : index.toNat < 65535 → card.toNat ≠ 0 →
      oracleSurroundingFirst time target index σ I = false →
      oracleSurroundingOldEnough time target index card σ I = false →
      OracleSurroundingFailure time target index card σ I

theorem oracleSurroundingReverts (imms : Store) (evm : EVM.State) (time target : UInt256)
    (tick : Int) (index liquidity card : UInt256) (ht : target.toNat < 2 ^ 32)
    (hc : card.toNat < 2 ^ 16)
    (hfail : OracleSurroundingFailure time target index card evm.accountMap evm.executionEnv) :
    ExecFuncBody config (oracleSurroundingFrame imms time target tick index liquidity card)
      evm oracleSurroundingFunction.body .reverted := by
  cases hfail with
  | index hi => exact oracleSurroundingIndexReverts imms evm time target tick index liquidity card hi
  | zero hi hz hf =>
      subst card
      exact oracleSurroundingZeroReverts imms evm time target tick index liquidity hi ht hf
  | old hi hn hf ho =>
      exact oracleSurroundingOldReverts imms evm time target tick index liquidity card hi ht hn hc hf ho

end Benchmarks.UniswapV3.Pool
