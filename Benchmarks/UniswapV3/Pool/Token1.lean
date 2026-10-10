import Benchmarks.UniswapV3.Pool.Dispatch
import Benchmarks.UniswapV3.Pool.Routines

/-!
# UniswapV3Pool `token1()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 2040; reach lemma `uniswapV3PoolReachToken1Body`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV3.Pool.Immutables

namespace Benchmarks.UniswapV3.Pool

set_option maxRecDepth 2000000

theorem uniswapV3PoolToken1Returns (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (locals : Store) (hwv : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm locals token1Transition.body
      (.returned { contract := contract, locals := locals, immutables := immStore v }
        evm (some [.address v.token1])) (immStore v) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns
      (evalImmutable_token1 config contract locals evm v)

theorem uniswapV3PoolToken1X {σ σ₀ A I} {g : Sat256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (uniswapV3PoolSelBytes 21)) :
    RDret (deployedRuntime v) g (initState σ σ₀ g A I) σ
      (UInt256.toByteArray (EVM.word v.token1.val)) := by
  obtain ⟨k, C, rd2040⟩ := uniswapV3PoolReachToken1Body (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hwv hsz hsize hsel
  have rd10527 := uniswapV3PoolBlocks.uniswapV3Pool_block_2040
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd2040
  have rd443 := uniswapV3PoolBlocks.uniswapV3Pool_block_10527
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd10527
  simp only [uniswapV3PoolBlocks.uniswapV3Pool_block_10527_stack,
    wordsOf_immStore_token1] at rd443
  have hret := RD.poolReturnAddress (v := v) rd443 (by simp)
  change RDret (deployedRuntime v) g (initState σ σ₀ g A I) σ
    (UInt256.toByteArray (UInt256.land (EVM.word v.token1.val) solcAddrMask)) at hret
  rwa [addressWord_val_clean] at hret

/-- `token1()`: the theorem `Correct.lean` routes selector 21 to. -/
theorem uniswapV3PoolToken1Body {σ σ₀ A I} {g : UInt256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (uniswapV3PoolSelBytes 21)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (uniswapV3PoolSelBytes 21) rfl hsel
  have hd : dispatchMsg contract I.calldata = some token1Transition := by
    apply uniswapV3PoolDispatch_token1 <;>
      first | exact hsel | exact selectorMismatch_of_match hsel (by decide +kernel)
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (token1Transition.params.map Param.name) (transitionSignature token1Transition).paramTypes
      I.calldata = some (∅ : Store) := decodeCalldataWithMode_empty_ok hsz
  exact (uniswapV3PoolToken1X (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel)
    |>.reEquivExecution hcode hd hdec
      (uniswapV3PoolToken1Returns v _ ∅ hwv)
      (returnEquiv_of_encode (addressReturnEncoding v.token1))

end Benchmarks.UniswapV3.Pool
