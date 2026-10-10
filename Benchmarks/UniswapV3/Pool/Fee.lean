import Benchmarks.UniswapV3.Pool.Dispatch
import Benchmarks.UniswapV3.Pool.Routines

/-!
# UniswapV3Pool `fee()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 2048; reach lemma `uniswapV3PoolReachFeeBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV3.Pool.Immutables

namespace Benchmarks.UniswapV3.Pool

set_option maxRecDepth 2000000

theorem uniswapV3PoolFeeReturns (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (locals : Store) (hwv : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm locals feeTransition.body
      (.returned { contract := contract, locals := locals, immutables := immStore v } evm
        (some [.int (normalizeInt (.uint ⟨24, by decide⟩)
          (Int.ofNat v.fee.toNat))])) (immStore v) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns
      (evalExpr_intCast (.uint ⟨24, by decide⟩)
        (evalImmutable_fee config contract locals evm v))

theorem uniswapV3PoolFeeX {σ σ₀ A I} {g : Sat256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (uniswapV3PoolSelBytes 22)) :
    RDret (deployedRuntime v) g (initState σ σ₀ g A I) σ
      (UInt256.toByteArray (UInt256.land v.fee (UInt256.ofNat 16777215))) := by
  obtain ⟨k, C, rdEntry⟩ := uniswapV3PoolReachFeeBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hwv hsz hsize hsel
  have rdRoutine := uniswapV3PoolBlocks.uniswapV3Pool_block_2048
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdEntry
  have rdReturn := uniswapV3PoolBlocks.uniswapV3Pool_block_10563
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdRoutine
  simp only [uniswapV3PoolBlocks.uniswapV3Pool_block_10563_stack,
    wordsOf_immStore_fee, wordOfInt_ofNat_toNat_gen, u256_ofNat_toNat] at rdReturn
  have hret := uniswapV3PoolBlocks.uniswapV3Pool_block_2056
    (immWords := wordsOf (immStore v)) (mem := solcFreePtrMem) (by simp) rdReturn
  simpa only [solcScalarReturnBytes] using hret

/-- `fee()`: the theorem `Correct.lean` routes selector 22 to. -/
theorem uniswapV3PoolFeeBody {σ σ₀ A I} {g : UInt256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (uniswapV3PoolSelBytes 22)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (uniswapV3PoolSelBytes 22) rfl hsel
  have hd : dispatchMsg contract I.calldata = some feeTransition := by
    apply uniswapV3PoolDispatch_fee <;>
      first | exact hsel | exact selectorMismatch_of_match hsel (by decide +kernel)
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (feeTransition.params.map Param.name)
      (transitionSignature feeTransition).paramTypes
      I.calldata = some (∅ : Store) := decodeCalldataWithMode_empty_ok hsz
  exact (uniswapV3PoolFeeX (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel)
    |>.reEquivExecution hcode hd hdec (uniswapV3PoolFeeReturns v _ ∅ hwv)
      (returnEquiv_of_encode (uintCastReturnEncoding ⟨24, by decide⟩ v.fee
        (UInt256.ofNat 16777215) (by native_decide)))

end Benchmarks.UniswapV3.Pool
