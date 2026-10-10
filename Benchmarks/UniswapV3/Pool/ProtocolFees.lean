import Benchmarks.UniswapV3.Pool.Dispatch
import Benchmarks.UniswapV3.Pool.TupleReturn
import Benchmarks.UniswapV3.Pool.Storage

/-!
# UniswapV3Pool `protocolFees()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 682; reach lemma `uniswapV3PoolReachProtocolFeesBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV3.Pool.Immutables

namespace Benchmarks.UniswapV3.Pool

set_option maxRecDepth 2000000

theorem uniswapV3PoolProtocolFeesReturns (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (locals : Store) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? "protocolFees" = none) :
    ExecTransitionBody config contract evm locals protocolFeesTransition.body
      (.returned { contract := contract, locals := locals, immutables := immStore v } evm
        (some [.int (Int.ofNat (protocolFeesToken0Word evm.accountMap evm.executionEnv).toNat),
          .int (Int.ofNat (protocolFeesToken1Word evm.accountMap evm.executionEnv).toNat)]))
      (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply ABlock.returnsMany (ABlock.start.requireStep (evalCallvalueEq_true hwv))
  simp only [evalExprs?.eq_def, evalProtocolFeesToken0 locals (immStore v) evm hbase,
    evalProtocolFeesToken1 locals (immStore v) evm hbase, EvalResult.bind, bind, pure]

theorem uniswapV3PoolProtocolFeesX {σ σ₀ A I} {g : Sat256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (uniswapV3PoolSelBytes 3)) :
    RDret (deployedRuntime v) g (initState σ σ₀ g A I) σ
      ((protocolFeesToken0Word σ I).toByteArray ++ (protocolFeesToken1Word σ I).toByteArray) := by
  obtain ⟨k, C, rdEntry⟩ := uniswapV3PoolReachProtocolFeesBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hwv hsz hsize hsel
  have rdRoutine := uniswapV3PoolBlocks.uniswapV3Pool_block_682
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdEntry
  obtain ⟨k', C', rdReturn⟩ := uniswapV3PoolBlocks.uniswapV3Pool_block_5308
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdRoutine
  have hshift : UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128) =
      UInt256.ofNat (2 ^ 128) := by native_decide
  simp only [uniswapV3PoolBlocks.uniswapV3Pool_block_5308_stack, solcMask128] at rdReturn
  rw [hshift] at rdReturn
  have hret := RD.poolReturnUint128Pair (v := v) rdReturn (by simp)
  simpa only [protocolFeesToken0Word, protocolFeesToken1Word,
    u256_land_comm (UInt256.ofNat (2 ^ 128 - 1)), maskTwice] using hret

/-- `protocolFees()`: the theorem `Correct.lean` routes selector 3 to. -/
theorem uniswapV3PoolProtocolFeesBody {σ σ₀ A I} {g : UInt256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (uniswapV3PoolSelBytes 3)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (uniswapV3PoolSelBytes 3) rfl hsel
  have hd : dispatchMsg contract I.calldata = some protocolFeesTransition := by
    apply uniswapV3PoolDispatch_protocolFees <;>
      first | exact hsel | exact selectorMismatch_of_match hsel (by decide +kernel)
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (protocolFeesTransition.params.map Param.name)
      (transitionSignature protocolFeesTransition).paramTypes
      I.calldata = some (∅ : Store) := decodeCalldataWithMode_empty_ok hsz
  exact (uniswapV3PoolProtocolFeesX (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel)
    |>.reEquivExecution hcode hd hdec (uniswapV3PoolProtocolFeesReturns v _ ∅ hwv (by simp))
      (returnEquiv.returned rfl (uintPairReturnEncoding ⟨128, by decide⟩ ⟨128, by decide⟩
        (protocolFeesToken0Word σ I) (protocolFeesToken1Word σ I)
        (u256LandMaskToNatLtOfToNat _ _ (by native_decide))
        (u256LandMaskToNatLtOfToNat _ _ (by native_decide))))

end Benchmarks.UniswapV3.Pool
