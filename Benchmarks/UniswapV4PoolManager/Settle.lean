import Benchmarks.UniswapV4PoolManager.Dispatch
import Benchmarks.UniswapV4PoolManager.SettleTrace
import Benchmarks.UniswapV4PoolManager.SettleEntrySource
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_030
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_006

/-!
# PoolManager `settle()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 10885; reach lemma `poolManagerReachSettleBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager

set_option maxRecDepth 5000

/-- `settle()`: the theorem `Correct.lean` routes selector 3 to. -/
theorem poolManagerSettleBody {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (_hWF : Syntax.poolManagerWF σ I)
    (_hGas : Syntax.poolManagerGasBound g)
    (hsel : selIs I (poolManagerSelBytes 3)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (poolManagerSelBytes 3) rfl hsel
  have hd : dispatchMsg contract I.calldata = some settleTransition := by
    apply poolManagerDispatch_settle <;> first
    | exact hsel
    | exact selectorNe_of_selIs hsel (by decide +kernel)
  have hdec : decodeCalldataWithMode config.abiDecodeMode (settleTransition.params.map Param.name)
      (transitionSignature settleTransition).paramTypes I.calldata = some ∅ :=
    decodeCalldataWithMode_empty_ok hsz
  obtain ⟨k, C, rdEntry⟩ := poolManagerReachSettleBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  change RD (deployedRuntime v) I (Sat256.ofUInt256 g)
    (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨10885⟩ [solcSelectorWord I]
    entryMemory ⟨3⟩ .empty σ k C at rdEntry
  by_cases hhi : I.calldata.size < calldataLimit
  · have rdLock := poolManagerBlocks.poolManager_block_10885_fallthrough (by simp)
      (viaIRStaticLenCheckOk (words := 0) hsz hhi hsize) rdEntry
    let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
    have hI : evm.executionEnv = I := rfl
    by_cases hl : transientWord evm lockSlot = ⟨0⟩
    · have rdRevert := poolManagerBlocks.poolManager_block_10927_taken (by simp)
        (by change UInt256.isZero (codeOwnerTransientWord I evm.accountMap lockSlot) ≠ ⟨0⟩
            rw [← transientWord_accountMap hI, hl]; decide)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rdLock
      exact (poolManagerBlocks.poolManager_block_1239 (by simp) rdRevert).reEquivExecutionRevert hcode hd hdec
        (settleEntryLocked (.env .caller) hhi hl)
    · have rdCall := poolManagerBlocks.poolManager_block_10927_fallthrough (by simp)
        (by change UInt256.isZero (codeOwnerTransientWord I evm.accountMap lockSlot) = ⟨0⟩
            rw [← transientWord_accountMap hI]; exact isZero_eq_zero_of_ne hl) rdLock
      have rdSettle := poolManagerBlocks.poolManager_block_10966 (by simp)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rdCall
      let caller := settleEntryFrame ∅ (immStore v) evm
      let callee : Frame := {caller with locals := (∅ : Store).insert "recipient" (.address I.source)}
      obtain ⟨result, hb, ht⟩ := settleFunctionTrace (evm := evm) (f := callee) (ptr := ⟨160⟩) v (by simp)
        hI rfl rfl (store_get_self _ _ _) entryMemory_wordReturn (by decide) (by decide) (by native_decide)
        entryMemory_load64 rdSettle
      have hbody := settleEntryReturnsCall (locals := ∅) (imms := immStore v) hhi hl
        (show evalExpr? config caller evm (.env .caller) = .ok (.address I.source) by
          simp only [evalExpr?, envValue, pure, hI]) hb
      exact uint256ResultTrace_refinement hcode hd hdec hbody
        (uint256ResultTrace_returnCall caller "__c1" ht) rfl rfl rfl
  · have hguard := viaIRStaticLenCheckHuge (words := 0) (Nat.le_of_not_gt hhi) hsize (by decide)
    have rdRevert := poolManagerBlocks.poolManager_block_10885_taken (by simp)
      (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz))
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rdEntry
    exact (emptyRevert v (by simp) rdRevert).reEquivExecutionRevert hcode hd hdec
      (calldataBodyReverts (rest := settleTransition.body.drop 2) hhi)

end Benchmarks.UniswapV4PoolManager
