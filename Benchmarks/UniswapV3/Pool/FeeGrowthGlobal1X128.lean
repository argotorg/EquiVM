import Benchmarks.UniswapV3.Pool.Dispatch
import Benchmarks.UniswapV3.Pool.Routines
import Benchmarks.UniswapV3.Pool.Storage

/-!
# UniswapV3Pool `feeGrowthGlobal1X128()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1110; reach lemma `uniswapV3PoolReachFeeGrowthGlobal1X128Body`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV3.Pool.Immutables

namespace Benchmarks.UniswapV3.Pool

set_option maxRecDepth 2000000

theorem uniswapV3PoolFeeGrowthGlobal1X128Returns (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (locals : Store) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? "feeGrowthGlobal1X128" = none) :
    ExecTransitionBody config contract evm locals feeGrowthGlobal1X128Transition.body
      (.returned { contract := contract, locals := locals, immutables := immStore v } evm
        (some [.int (Int.ofNat
          (solcSlotWordAt ⟨2⟩ evm.accountMap evm.executionEnv).toNat)])) (immStore v) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns
      (evalFeeGrowthGlobal1X128 locals (immStore v) evm hbase)

theorem uniswapV3PoolFeeGrowthGlobal1X128X {σ σ₀ A I} {g : Sat256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (uniswapV3PoolSelBytes 8)) :
    RDret (deployedRuntime v) g (initState σ σ₀ g A I) σ
      (UInt256.toByteArray (solcSlotWordAt ⟨2⟩ σ I)) := by
  obtain ⟨k, C, rdEntry⟩ := uniswapV3PoolReachFeeGrowthGlobal1X128Body (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hwv hsz hsize hsel
  have rdRoutine := uniswapV3PoolBlocks.uniswapV3Pool_block_1110
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdEntry
  obtain ⟨k', C', rdReturn⟩ := uniswapV3PoolBlocks.uniswapV3Pool_block_6434
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdRoutine
  simp only [uniswapV3PoolBlocks.uniswapV3Pool_block_6434_stack] at rdReturn
  exact RD.poolReturnWord (v := v) rdReturn (by simp)

/-- `feeGrowthGlobal1X128()`: the theorem `Correct.lean` routes selector 8 to. -/
theorem uniswapV3PoolFeeGrowthGlobal1X128Body {σ σ₀ A I} {g : UInt256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (uniswapV3PoolSelBytes 8)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (uniswapV3PoolSelBytes 8) rfl hsel
  have hd : dispatchMsg contract I.calldata = some feeGrowthGlobal1X128Transition := by
    apply uniswapV3PoolDispatch_feeGrowthGlobal1X128 <;>
      first | exact hsel | exact selectorMismatch_of_match hsel (by decide +kernel)
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (feeGrowthGlobal1X128Transition.params.map Param.name)
      (transitionSignature feeGrowthGlobal1X128Transition).paramTypes
      I.calldata = some (∅ : Store) := decodeCalldataWithMode_empty_ok hsz
  exact (uniswapV3PoolFeeGrowthGlobal1X128X (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel)
    |>.reEquivExecution hcode hd hdec (uniswapV3PoolFeeGrowthGlobal1X128Returns v _ ∅ hwv (by simp))
      (returnEquiv_of_encode (uint256ReturnEncoding (solcSlotWordAt ⟨2⟩ σ I)))

end Benchmarks.UniswapV3.Pool
