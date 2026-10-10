import Benchmarks.UniswapV3.Pool.Dispatch
import Benchmarks.UniswapV3.Pool.Routines
import Benchmarks.UniswapV3.Pool.Storage

/-!
# UniswapV3Pool `liquidity()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 646; reach lemma `uniswapV3PoolReachLiquidityBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV3.Pool.Immutables

namespace Benchmarks.UniswapV3.Pool

set_option maxRecDepth 2000000

theorem uniswapV3PoolLiquidityReturns (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (locals : Store) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? "liquidity" = none) :
    ExecTransitionBody config contract evm locals liquidityTransition.body
      (.returned { contract := contract, locals := locals, immutables := immStore v } evm
        (some [.int (Int.ofNat
          (UInt256.land (solcSlotWordAt ⟨4⟩ evm.accountMap evm.executionEnv)
            (UInt256.ofNat (2 ^ 128 - 1))).toNat)])) (immStore v) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns
      (evalLiquidity locals (immStore v) evm hbase)

theorem uniswapV3PoolLiquidityX {σ σ₀ A I} {g : Sat256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (uniswapV3PoolSelBytes 2)) :
    RDret (deployedRuntime v) g (initState σ σ₀ g A I) σ
      (UInt256.toByteArray (UInt256.land (solcSlotWordAt ⟨4⟩ σ I) (UInt256.ofNat (2 ^ 128 - 1)))) := by
  obtain ⟨k, C, rdEntry⟩ := uniswapV3PoolReachLiquidityBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hwv hsz hsize hsel
  have rdRoutine := uniswapV3PoolBlocks.uniswapV3Pool_block_646
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdEntry
  obtain ⟨k', C', rdReturn⟩ := uniswapV3PoolBlocks.uniswapV3Pool_block_5293
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdRoutine
  simp only [uniswapV3PoolBlocks.uniswapV3Pool_block_5293_stack] at rdReturn
  rw [solcMask128] at rdReturn
  have hret := RD.poolReturnUint128 (v := v) rdReturn (by simp)
  simpa only [u256_land_comm (UInt256.ofNat (2 ^ 128 - 1)), maskTwice] using hret

/-- `liquidity()`: the theorem `Correct.lean` routes selector 2 to. -/
theorem uniswapV3PoolLiquidityBody {σ σ₀ A I} {g : UInt256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (uniswapV3PoolSelBytes 2)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (uniswapV3PoolSelBytes 2) rfl hsel
  have hd : dispatchMsg contract I.calldata = some liquidityTransition := by
    apply uniswapV3PoolDispatch_liquidity <;>
      first | exact hsel | exact selectorMismatch_of_match hsel (by decide +kernel)
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (liquidityTransition.params.map Param.name)
      (transitionSignature liquidityTransition).paramTypes
      I.calldata = some (∅ : Store) := decodeCalldataWithMode_empty_ok hsz
  exact (uniswapV3PoolLiquidityX (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel)
    |>.reEquivExecution hcode hd hdec (uniswapV3PoolLiquidityReturns v _ ∅ hwv (by simp))
      (returnEquiv_of_encode (uintReturnEncoding ⟨128, by decide⟩ (UInt256.land (solcSlotWordAt ⟨4⟩ σ I) (UInt256.ofNat (2 ^ 128 - 1)))
        (u256LandMaskToNatLtOfToNat _ _ (by native_decide))))

end Benchmarks.UniswapV3.Pool
