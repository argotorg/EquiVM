import Benchmarks.UniswapV3.Pool.Dispatch
import Benchmarks.UniswapV3.Pool.Routines
import Benchmarks.UniswapV3.Pool.SignedWords

/-!
# UniswapV3Pool `tickSpacing()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 2009; reach lemma `uniswapV3PoolReachTickSpacingBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV3.Pool.Immutables

namespace Benchmarks.UniswapV3.Pool

set_option maxRecDepth 2000000

theorem uniswapV3PoolTickSpacingReturns (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (locals : Store) (hwv : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm locals tickSpacingTransition.body
      (.returned { contract := contract, locals := locals, immutables := immStore v } evm
        (some [.int (normalizeInt (.sint ⟨24, by decide⟩)
          (Int.ofNat v.tickSpacing.toNat))])) (immStore v) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns
      (evalExpr_intCast (.sint ⟨24, by decide⟩)
        (evalImmutable_tickSpacing config contract locals evm v))

theorem uniswapV3PoolTickSpacingX {σ σ₀ A I} {g : Sat256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (uniswapV3PoolSelBytes 20)) :
    RDret (deployedRuntime v) g (initState σ σ₀ g A I) σ
      (UInt256.toByteArray (UInt256.signextend (UInt256.ofNat 2) v.tickSpacing)) := by
  obtain ⟨k, C, rdEntry⟩ := uniswapV3PoolReachTickSpacingBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hwv hsz hsize hsel
  have rdRoutine := uniswapV3PoolBlocks.uniswapV3Pool_block_2009
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdEntry
  have rdReturn := uniswapV3PoolBlocks.uniswapV3Pool_block_10491
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdRoutine
  simp only [uniswapV3PoolBlocks.uniswapV3Pool_block_10491_stack,
    wordsOf_immStore_tickSpacing, wordOfInt_ofNat_toNat_gen, u256_ofNat_toNat] at rdReturn
  have hret := uniswapV3PoolBlocks.uniswapV3Pool_block_2017
    (immWords := wordsOf (immStore v)) (mem := solcFreePtrMem) (by simp) rdReturn
  simpa only [solcScalarReturnBytes] using hret

/-- `tickSpacing()`: the theorem `Correct.lean` routes selector 20 to. -/
theorem uniswapV3PoolTickSpacingBody {σ σ₀ A I} {g : UInt256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (uniswapV3PoolSelBytes 20)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (uniswapV3PoolSelBytes 20) rfl hsel
  have hd : dispatchMsg contract I.calldata = some tickSpacingTransition := by
    apply uniswapV3PoolDispatch_tickSpacing <;>
      first | exact hsel | exact selectorMismatch_of_match hsel (by decide +kernel)
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (tickSpacingTransition.params.map Param.name)
      (transitionSignature tickSpacingTransition).paramTypes
      I.calldata = some (∅ : Store) := decodeCalldataWithMode_empty_ok hsz
  exact (uniswapV3PoolTickSpacingX (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel)
    |>.reEquivExecution hcode hd hdec (uniswapV3PoolTickSpacingReturns v _ ∅ hwv)
      (returnEquiv_of_encode (sintCastReturnEncoding ⟨24, by decide⟩ (UInt256.ofNat 2)
        v.tickSpacing (by native_decide) (by native_decide)))

end Benchmarks.UniswapV3.Pool
