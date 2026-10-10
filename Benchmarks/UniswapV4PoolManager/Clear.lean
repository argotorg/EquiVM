import Benchmarks.UniswapV4PoolManager.Dispatch
import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.ClearSource
import Benchmarks.UniswapV4PoolManager.ClearTrace

/-!
# PoolManager `clear(address,uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 3463; reach lemma `poolManagerReachClearBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager

set_option maxRecDepth 2000000

theorem poolManagerClearBodyCore {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (poolManagerSelBytes 26)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (poolManagerSelBytes 26) rfl hsel
  have hd : dispatchMsg contract I.calldata = some clearTransition := by
    apply poolManagerDispatch_clear <;> first
    | exact hsel
    | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rdEntry⟩ := poolManagerReachClearBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  change RD (deployedRuntime v) I (Sat256.ofUInt256 g)
    (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3463⟩ [solcSelectorWord I]
    entryMemory ⟨3⟩ .empty σ k C at rdEntry
  have hjump : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 816) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rdSize := poolManagerBlocks.poolManager_block_3463_fallthrough (by simp) hwv rdEntry
    by_cases hlen : 68 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < calldataLimit
      · have rdDecode := poolManagerBlocks.poolManager_block_3469_fallthrough (by simp)
          (viaIRStaticLenCheckOk (words := 2) hlen hhi hsize) rdSize
        have hjDecode : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 11583) = true := by
          rw [deployedRuntime_jumps]; jump_dest
        have rdAddr := poolManagerBlocks.poolManager_block_3511 (by simp) hjDecode rdDecode
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · have hjReturn : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 3518) = true := by
            rw [deployedRuntime_jumps]; jump_dest
          obtain ⟨k', C', rdBody⟩ := decodeAddress4 v (by simp) hcanon hjReturn rdAddr
          let currency := AccountAddress.ofNat (calldataWord I.calldata 4).toNat
          let amount := calldataWord I.calldata 36
          let args := ((∅ : Store).insert "currency" (.address currency)).insert "amount" (.int (Int.ofNat amount.toNat))
          let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
          have hI : evm.executionEnv = I := rfl
          have hdec : decodeCalldataWithMode config.abiDecodeMode (clearTransition.params.map Param.name)
              (transitionSignature clearTransition).paramTypes I.calldata = some args :=
            decodeCalldata_addr_uint256_ok hlen hhi hcanon
          have hc : args.get? "currency" = some (.address currency) :=
            (store_get_ne _ _ (by decide : ("amount" == "currency") = false)).trans (store_get_self _ _ _)
          have ha : args.get? "amount" = some (.int (Int.ofNat amount.toNat)) := store_get_self _ _ _
          have hbody := clearBodyExec (imms := immStore v) (evm := evm) hwv hhi hc ha
          have hcurrency : accountWord currency = calldataWord I.calldata 4 :=
            (accountWord_eq_iff currency _ hcanon).mp rfl
          rw [← hcurrency] at rdBody
          have htrace := clearTrace (evm := evm) v (by simp) hI (show calldataWord I.calldata 36 = amount from rfl) rdBody
          simp only [clearBodyResult, hI] at hbody
          rw [clearTraceResult] at htrace
          by_cases hl : transientWord evm lockSlot = ⟨0⟩
          · rw [if_pos hl] at hbody htrace
            exact htrace.reEquivExecutionRevert hcode hd hdec hbody
          · rw [if_neg hl] at hbody htrace
            by_cases hfit : amount.toNat < 2^127
            · rw [if_pos hfit] at hbody htrace
              by_cases heq : Int.ofNat amount.toNat = currencyDeltaValue evm I.source currency
              · rw [if_pos heq] at hbody htrace
                by_cases hp : amount.toNat ≠ 0 ∧ I.perm = false
                · rw [if_pos hp] at hbody htrace
                  exact htrace.reEquivStaticHalt hcode hd hdec hbody
                · rw [if_neg hp] at hbody htrace
                  exact htrace.reEquivExecutionGen hcode hd hdec hbody rfl
                    (.fallthrough rfl rfl (by native_decide))
              · rw [if_neg heq] at hbody htrace
                exact htrace.reEquivExecutionRevert hcode hd hdec hbody
            · rw [if_neg hfit] at hbody htrace
              exact htrace.reEquivExecutionRevert hcode hd hdec hbody
        · exact (decodeAddress4Reverts v (by simp) hcanon rdAddr).reEquivDecodingFailed hcode hd
            (decodeCalldata_addr_uint256_none_noncanon hlen hhi hcanon)
      · have hguard := viaIRStaticLenCheckHuge (words := 2) (Nat.le_of_not_gt hhi) hsize (by decide)
        have rdRevert := poolManagerBlocks.poolManager_block_3469_taken (by simp)
          (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
        exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
          (decodeCalldata_addr_uint256_none_huge (Nat.le_of_not_gt hhi))
    · have hguard := viaIRStaticLenCheckShort (words := 2) hsz (Nat.lt_of_not_ge hlen) (by decide) hsize
      have rdRevert := poolManagerBlocks.poolManager_block_3469_taken (by simp)
        (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
      exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
        (decodeCalldata_addr_uint256_none_short hsz (Nat.lt_of_not_ge hlen))
  · have rdRevert := poolManagerBlocks.poolManager_block_3463_taken (by simp) hwv hjump rdEntry
    exact selectedRevert hcode (emptyRevert v (by simp) rdRevert) hd
      (fun _ => bodyReverts_nonPayable hwv)

/-- `clear(address,uint256)`: the theorem `Correct.lean` routes selector 26 to. -/
theorem poolManagerClearBody {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (_hWF : Syntax.poolManagerWF σ I) (_hGas : Syntax.poolManagerGasBound g)
    (hsel : selIs I (poolManagerSelBytes 26)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) :=
  poolManagerClearBodyCore v hcode hsize hsel

end Benchmarks.UniswapV4PoolManager
