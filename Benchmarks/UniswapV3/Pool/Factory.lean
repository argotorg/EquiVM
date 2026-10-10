import Benchmarks.UniswapV3.Pool.Dispatch
import Benchmarks.UniswapV3.Pool.Routines

/-!
# UniswapV3Pool `factory()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 2001; reach lemma `uniswapV3PoolReachFactoryBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV3.Pool.Immutables

namespace Benchmarks.UniswapV3.Pool

set_option maxRecDepth 2000000

theorem uniswapV3PoolFactoryReturns (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (locals : Store) (hwv : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm locals factoryTransition.body
      (.returned { contract := contract, locals := locals, immutables := immStore v }
        evm (some [.address v.factory])) (immStore v) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns
      (evalImmutable_factory config contract locals evm v)

theorem uniswapV3PoolFactoryX {σ σ₀ A I} {g : Sat256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (uniswapV3PoolSelBytes 19)) :
    RDret (deployedRuntime v) g (initState σ σ₀ g A I) σ
      (UInt256.toByteArray (EVM.word v.factory.val)) := by
  obtain ⟨k, C, rd2001⟩ := uniswapV3PoolReachFactoryBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hwv hsz hsize hsel
  have rd10455 := uniswapV3PoolBlocks.uniswapV3Pool_block_2001
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd2001
  have rd443 := uniswapV3PoolBlocks.uniswapV3Pool_block_10455
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd10455
  simp only [uniswapV3PoolBlocks.uniswapV3Pool_block_10455_stack,
    wordsOf_immStore_factory] at rd443
  have hret := RD.poolReturnAddress (v := v) rd443 (by simp)
  change RDret (deployedRuntime v) g (initState σ σ₀ g A I) σ
    (UInt256.toByteArray (UInt256.land (EVM.word v.factory.val) solcAddrMask)) at hret
  rwa [addressWord_val_clean] at hret

/-- `factory()`: the theorem `Correct.lean` routes selector 19 to. -/
theorem uniswapV3PoolFactoryBody {σ σ₀ A I} {g : UInt256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (uniswapV3PoolSelBytes 19)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (uniswapV3PoolSelBytes 19) rfl hsel
  have hd : dispatchMsg contract I.calldata = some factoryTransition := by
    apply uniswapV3PoolDispatch_factory <;>
      first | exact hsel | exact selectorMismatch_of_match hsel (by decide +kernel)
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (factoryTransition.params.map Param.name) (transitionSignature factoryTransition).paramTypes
      I.calldata = some (∅ : Store) := decodeCalldataWithMode_empty_ok hsz
  exact (uniswapV3PoolFactoryX (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel)
    |>.reEquivExecution hcode hd hdec
      (uniswapV3PoolFactoryReturns v _ ∅ hwv)
      (returnEquiv_of_encode (addressReturnEncoding v.factory))

end Benchmarks.UniswapV3.Pool
