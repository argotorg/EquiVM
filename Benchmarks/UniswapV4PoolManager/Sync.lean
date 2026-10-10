import Benchmarks.UniswapV4PoolManager.Dispatch
import Benchmarks.UniswapV4PoolManager.SyncSource
import Benchmarks.UniswapV4PoolManager.SyncStoreTrace
import Benchmarks.UniswapV4PoolManager.CurrencyBalanceTrace

/-!
# PoolManager `sync(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 2662; reach lemma `poolManagerReachSyncBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager

set_option maxRecDepth 5000

/-- `sync(address)`: the theorem `Correct.lean` routes selector 19 to. -/
theorem poolManagerSyncBody {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (_hWF : Syntax.poolManagerWF σ I)
    (_hGas : Syntax.poolManagerGasBound g)
    (hsel : selIs I (poolManagerSelBytes 19)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (poolManagerSelBytes 19) rfl hsel
  have hd : dispatchMsg contract I.calldata = some syncTransition := by
    apply poolManagerDispatch_sync <;> first
    | exact hsel
    | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rdEntry⟩ := poolManagerReachSyncBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  change RD (deployedRuntime v) I (Sat256.ofUInt256 g)
    (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2662⟩ [solcSelectorWord I]
    entryMemory ⟨3⟩ .empty σ k C at rdEntry
  have hjump : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 816) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rdSize := poolManagerBlocks.poolManager_block_2662_fallthrough (by simp) hwv rdEntry
    by_cases hlen : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < calldataLimit
      · have rdDecode := poolManagerBlocks.poolManager_block_2668_fallthrough (by simp)
          (viaIRStaticLenCheckOk (words := 1) hlen hhi hsize) rdSize
        have rdAddr := poolManagerBlocks.poolManager_block_2710 (by simp)
          (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rdDecode
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨k1, C1, rdLoad⟩ := decodeAddress4 v (by simp) hcanon
            (by rw [deployedRuntime_jumps]; jump_dest) rdAddr
          let currency := AccountAddress.ofNat (calldataWord I.calldata 4).toNat
          let args := (∅ : Store).insert "currency" (.address currency)
          let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
          have hI : evm.executionEnv = I := rfl
          have hword : accountWord currency = calldataWord I.calldata 4 :=
            (accountWord_eq_iff currency _ hcanon).1 rfl
          have hclean : UInt256.land (calldataWord I.calldata 4) solcAddrMask = calldataWord I.calldata 4 :=
            solcAddrMask_clean hcanon
          have hdec : decodeCalldataWithMode config.abiDecodeMode (syncTransition.params.map Param.name)
              (transitionSignature syncTransition).paramTypes I.calldata = some args :=
            decodeCalldata_address_ok hlen hhi hcanon
          by_cases hz : currency = AccountAddress.ofNat 0
          · have hwzero : calldataWord I.calldata 4 = ⟨0⟩ :=
              hword.symm.trans ((accountWord_eq_iff currency ⟨0⟩ (by decide)).1 hz)
            have rdStore := poolManagerBlocks.poolManager_block_2717_fallthrough (by simp)
              (hclean.trans hwzero) rdLoad
            have htrace := syncZeroStoreTrace (evm := evm) v (by simp) hI rdStore
            have hbody := syncZeroBody (evm := evm) (imms := immStore v) hwv hhi
              (show args.get? "currency" = some (.address (AccountAddress.ofNat 0)) from by
                rw [← hz]; exact store_get_self _ _ _)
            rw [syncZeroResult, hI] at hbody
            by_cases hp : I.perm = false
            · rw [if_pos hp] at htrace hbody
              exact htrace.reEquivStaticHalt hcode hd hdec hbody
            · rw [if_neg hp] at htrace hbody
              exact htrace.reEquivExecutionGen hcode hd hdec hbody rfl
                (.fallthrough rfl rfl (by native_decide))
          · have hnword : calldataWord I.calldata 4 ≠ ⟨0⟩ := fun he =>
              hz ((accountWord_eq_iff currency ⟨0⟩ (by decide)).2 (hword.trans he))
            have rdCall := poolManagerBlocks.poolManager_block_2717_taken (by simp)
              (by change UInt256.land (calldataWord I.calldata 4) solcAddrMask ≠ ⟨0⟩; rw [hclean]; exact hnword)
              (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rdLoad
            change RD _ _ _ _ ⟨2785⟩
              (calldataWord I.calldata 4 :: UInt256.land (calldataWord I.calldata 4) solcAddrMask :: [solcSelectorWord I])
              _ _ _ _ _ _ at rdCall
            rw [hclean] at rdCall
            have rdBalance := poolManagerBlocks.poolManager_block_2785 (by simp)
              (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rdCall
            change RD _ _ _ _ ⟨14994⟩
              (calldataWord I.calldata 4 :: ⟨2794⟩ :: calldataWord I.calldata 4 :: [solcSelectorWord I])
              entryMemory _ _ _ _ _ at rdBalance
            rw [← hword] at rdBalance
            obtain ⟨evm', z, out, hcall, hI', _, ho, hr⟩ := currencyBalanceTrace (evm := evm) v (by simp)
              hI rfl hz (ptr := ⟨160⟩) (by decide) (by decide) (by native_decide) entryMemory_load64
              (by rw [deployedRuntime_jumps]; jump_dest) rdBalance
            have hbody := syncTokenBody (evm := evm) (imms := immStore v) hwv hhi
              (show args.get? "currency" = some (.address currency) from store_get_self _ _ _)
              hz (lt_trans ho (by decide)) hcall
            rw [syncTokenResult, hI'] at hbody
            rcases hr with ⟨hbad, hrev⟩ | ⟨hztrue, hout, mem', aw', k', C', rdStore⟩
            · rw [if_neg hbad] at hbody
              exact hrev.reEquivExecutionRevert hcode hd hdec hbody
            · rw [if_pos ⟨hztrue, hout⟩] at hbody
              have htrace := syncReservesStoreTrace v (by simp) hI' rdStore
              by_cases hp : I.perm = false
              · rw [if_pos hp] at htrace hbody
                exact htrace.reEquivStaticHalt hcode hd hdec hbody
              · rw [if_neg hp] at htrace hbody
                exact htrace.reEquivExecutionGen hcode hd hdec hbody rfl
                  (.fallthrough rfl rfl (by native_decide))
        · exact (decodeAddress4Reverts v (by simp) hcanon rdAddr).reEquivDecodingFailed hcode hd
            (decodeCalldata_address_none_noncanon hlen hhi hcanon)
      · have hguard := viaIRStaticLenCheckHuge (words := 1) (Nat.le_of_not_gt hhi) hsize (by decide)
        have rdRevert := poolManagerBlocks.poolManager_block_2668_taken (by simp)
          (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
        exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
          (decodeCalldata_address_none_huge (Nat.le_of_not_gt hhi))
    · have hguard := viaIRStaticLenCheckShort (words := 1) hsz (Nat.lt_of_not_ge hlen) (by decide) hsize
      have rdRevert := poolManagerBlocks.poolManager_block_2668_taken (by simp)
        (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
      exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
        (decodeCalldata_address_none_short hsz (Nat.lt_of_not_ge hlen))
  · have rdRevert := poolManagerBlocks.poolManager_block_2662_taken (by simp) hwv hjump rdEntry
    exact selectedRevert hcode (emptyRevert v (by simp) rdRevert) hd
      (fun _ => bodyReverts_nonPayable hwv)

end Benchmarks.UniswapV4PoolManager
