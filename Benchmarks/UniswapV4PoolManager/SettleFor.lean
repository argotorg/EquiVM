import Benchmarks.UniswapV4PoolManager.Dispatch
import Benchmarks.UniswapV4PoolManager.SettleTrace
import Benchmarks.UniswapV4PoolManager.SettleEntrySource
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_027
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_006

/-!
# PoolManager `settleFor(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 9593; reach lemma `poolManagerReachSettleForBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager

set_option maxRecDepth 5000

/-- `settleFor(address)`: the theorem `Correct.lean` routes selector 12 to. -/
theorem poolManagerSettleForBody {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (_hWF : Syntax.poolManagerWF σ I)
    (_hGas : Syntax.poolManagerGasBound g)
    (hsel : selIs I (poolManagerSelBytes 12)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (poolManagerSelBytes 12) rfl hsel
  have hd : dispatchMsg contract I.calldata = some settleForTransition := by
    apply poolManagerDispatch_settleFor <;> first
    | exact hsel
    | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rdEntry⟩ := poolManagerReachSettleForBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  change RD (deployedRuntime v) I (Sat256.ofUInt256 g)
    (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9593⟩ [solcSelectorWord I]
    entryMemory ⟨3⟩ .empty σ k C at rdEntry
  have hjump : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 816) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  by_cases hlen : 36 ≤ I.calldata.size
  · by_cases hhi : I.calldata.size < calldataLimit
    · have rdDecode := poolManagerBlocks.poolManager_block_9593_fallthrough (by simp)
        (viaIRStaticLenCheckOk (words := 1) hlen hhi hsize) rdEntry
      have rdAddr := poolManagerBlocks.poolManager_block_9636 (by simp)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rdDecode
      by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
      · obtain ⟨k1, C1, rdLock⟩ := decodeAddress4 v (by simp) hcanon
          (by rw [deployedRuntime_jumps]; jump_dest) rdAddr
        let recipient := AccountAddress.ofNat (calldataWord I.calldata 4).toNat
        let args := (∅ : Store).insert "recipient" (.address recipient)
        let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
        have hI : evm.executionEnv = I := rfl
        have hword : accountWord recipient = calldataWord I.calldata 4 :=
          (accountWord_eq_iff recipient _ hcanon).1 rfl
        have hdec : decodeCalldataWithMode config.abiDecodeMode (settleForTransition.params.map Param.name)
            (transitionSignature settleForTransition).paramTypes I.calldata = some args :=
          decodeCalldata_address_ok hlen hhi hcanon
        by_cases hl : transientWord evm lockSlot = ⟨0⟩
        · have rdRevert := poolManagerBlocks.poolManager_block_9643_taken (by simp)
            (by change UInt256.isZero (codeOwnerTransientWord I evm.accountMap lockSlot) ≠ ⟨0⟩
                rw [← transientWord_accountMap hI, hl]; decide)
            (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rdLock
          exact (poolManagerBlocks.poolManager_block_1239 (by simp) rdRevert).reEquivExecutionRevert hcode hd hdec
            (settleEntryLocked (.var "recipient") hhi hl)
        · have rdCall := poolManagerBlocks.poolManager_block_9643_fallthrough (by simp)
            (by change UInt256.isZero (codeOwnerTransientWord I evm.accountMap lockSlot) = ⟨0⟩
                rw [← transientWord_accountMap hI]; exact isZero_eq_zero_of_ne hl) rdLock
          have rdSettle := poolManagerBlocks.poolManager_block_9683 (by simp)
            (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rdCall
          change RD _ _ _ _ ⟨13357⟩
            (calldataWord I.calldata 4 :: ⟨1954⟩ :: ⟨32⟩ :: [solcSelectorWord I]) _ _ _ _ _ _ at rdSettle
          rw [← hword] at rdSettle
          let caller := settleEntryFrame args (immStore v) evm
          let callee : Frame := {caller with locals := (∅ : Store).insert "recipient" (.address recipient)}
          obtain ⟨result, hb, ht⟩ := settleFunctionTrace (evm := evm) (f := callee) (ptr := ⟨160⟩) v (by simp)
            hI rfl rfl (store_get_self _ _ _) entryMemory_wordReturn (by decide) (by decide) (by native_decide)
            entryMemory_load64 rdSettle
          have hbody := settleEntryReturnsCall (locals := args) (imms := immStore v) hhi hl
            (show evalExpr? config caller evm (.var "recipient") = .ok (.address recipient) from
              evalLocalValue ((store_get_ne _ _ (by decide : ("__c0" == "recipient") = false)).trans
                ((store_get_ne _ _ (by decide : ("__calldata" == "recipient") = false)).trans (store_get_self _ _ _)))) hb
          exact uint256ResultTrace_refinement hcode hd hdec hbody
            (uint256ResultTrace_returnCall caller "__c1" ht) rfl rfl rfl
      · exact (decodeAddress4Reverts v (by simp) hcanon rdAddr).reEquivDecodingFailed hcode hd
          (decodeCalldata_address_none_noncanon hlen hhi hcanon)
    · have hguard := viaIRStaticLenCheckHuge (words := 1) (Nat.le_of_not_gt hhi) hsize (by decide)
      have rdRevert := poolManagerBlocks.poolManager_block_9593_taken (by simp)
        (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdEntry
      exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
        (decodeCalldata_address_none_huge (Nat.le_of_not_gt hhi))
  · have hguard := viaIRStaticLenCheckShort (words := 1) hsz (Nat.lt_of_not_ge hlen) (by decide) hsize
    have rdRevert := poolManagerBlocks.poolManager_block_9593_taken (by simp)
      (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdEntry
    exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
      (decodeCalldata_address_none_short hsz (Nat.lt_of_not_ge hlen))

end Benchmarks.UniswapV4PoolManager
