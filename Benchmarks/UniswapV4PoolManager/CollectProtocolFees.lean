import Benchmarks.UniswapV4PoolManager.Dispatch
import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.CollectProtocolFeesTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_011

/-!
# PoolManager `collectProtocolFees(address,address,uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 3121; reach lemma `poolManagerReachCollectProtocolFeesBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager

set_option maxRecDepth 5000

/-- `collectProtocolFees(address,address,uint256)`: the theorem `Correct.lean` routes selector 11 to. -/
theorem poolManagerCollectProtocolFeesBody {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (_hWF : Syntax.poolManagerWF σ I)
    (_hGas : Syntax.poolManagerGasBound g)
    (hsel : selIs I (poolManagerSelBytes 11)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (poolManagerSelBytes 11) rfl hsel
  have hd : dispatchMsg contract I.calldata = some collectProtocolFeesTransition := by
    apply poolManagerDispatch_collectProtocolFees <;> first
    | exact hsel
    | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rdEntry⟩ := poolManagerReachCollectProtocolFeesBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  change RD (deployedRuntime v) I (Sat256.ofUInt256 g)
    (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3121⟩ [solcSelectorWord I]
    entryMemory ⟨3⟩ .empty σ k C at rdEntry
  have hj816 : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 816) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rdSize := poolManagerBlocks.poolManager_block_3121_fallthrough (by simp) hwv rdEntry
    by_cases hlen : 100 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < calldataLimit
      · have rdDecode := poolManagerBlocks.poolManager_block_3127_fallthrough (by simp)
          (viaIRStaticLenCheckOk (words := 3) hlen hhi hsize) rdSize
        have rdAddr0 := poolManagerBlocks.poolManager_block_3169 (by simp)
          (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rdDecode
        by_cases hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨k0, C0, rdNext⟩ := decodeAddress4 v (by simp) hc0
            (by rw [deployedRuntime_jumps]; jump_dest) rdAddr0
          have rdAddr1 := poolManagerBlocks.poolManager_block_3176 (by simp)
            (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rdNext
          by_cases hc1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus
          · obtain ⟨k1, C1, rdBody⟩ := decodeAddress36 v (by simp) hc1
              (by rw [deployedRuntime_jumps]; jump_dest) rdAddr1
            let recipient := AccountAddress.ofNat (calldataWord I.calldata 4).toNat
            let currency := AccountAddress.ofNat (calldataWord I.calldata 36).toNat
            let amount := calldataWord I.calldata 68
            let args := (((∅ : Store).insert "recipient" (.address recipient)).insert "currency" (.address currency)).insert
              "amount" (.int (Int.ofNat amount.toNat))
            have hdec : decodeCalldataWithMode config.abiDecodeMode (collectProtocolFeesTransition.params.map Param.name)
                (transitionSignature collectProtocolFeesTransition).paramTypes I.calldata = some args :=
              decodeCalldata_address_address_uint256_ok hlen hhi hc0 hc1
            let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
            let f := calldataFrame contract args (immStore v) evm
            have hc : f.locals.get? "currency" = some (.address currency) :=
              (store_get_ne _ _ (by decide : ("__calldata" == "currency") = false)).trans
                ((store_get_ne _ _ (by decide : ("amount" == "currency") = false)).trans (store_get_self _ _ _))
            have ht : f.locals.get? "recipient" = some (.address recipient) :=
              (store_get_ne _ _ (by decide : ("__calldata" == "recipient") = false)).trans
                ((store_get_ne _ _ (by decide : ("amount" == "recipient") = false)).trans
                  ((store_get_ne _ _ (by decide : ("currency" == "recipient") = false)).trans (store_get_self _ _ _)))
            have hbase : ∀ name, ("__calldata" == name) = false → ("amount" == name) = false →
                ("currency" == name) = false → ("recipient" == name) = false → f.locals.get? name = none := by
              intro name h0 h1 h2 h3
              exact (store_get_ne _ _ h0).trans ((store_get_ne _ _ h1).trans
                ((store_get_ne _ _ h2).trans ((store_get_ne _ _ h3).trans (store_get_empty _))))
            have ha : f.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)) :=
              (store_get_ne _ _ (by decide : ("__calldata" == "amount") = false)).trans (store_get_self _ _ _)
            have hwc : accountWord currency = calldataWord I.calldata 36 := (accountWord_eq_iff currency _ hc1).1 rfl
            have hwt : accountWord recipient = calldataWord I.calldata 4 := (accountWord_eq_iff recipient _ hc0).1 rfl
            change RD (deployedRuntime v) I (Sat256.ofUInt256 g) evm ⟨3184⟩
              (calldataWord I.calldata 36 :: calldataWord I.calldata 4 :: [solcSelectorWord I])
              entryMemory ⟨3⟩ .empty evm.accountMap k1 C1 at rdBody
            rw [← hwc, ← hwt] at rdBody
            obtain ⟨result, hb, hr⟩ := collectBodyTrace (I := I) (evm := evm) (s0 := evm) (f := f)
              (currency := currency) (recipient := recipient) v (by simp) rfl rfl rfl hc ht ha
              (hbase "protocolFeesAccrued" (by decide) (by decide) (by decide) (by decide))
              (hbase "protocolFeeController" (by decide) (by decide) (by decide) (by decide))
              entryMemory_size entryMemory_load64 rdBody
            have hbody : ExecTransitionBody config contract evm args collectProtocolFeesTransition.body result (immStore v) :=
              nonpayableCalldataBody hwv hhi hb
            exact uint256ResultTrace_refinement hcode hd hdec hbody hr rfl rfl rfl
          · exact (decodeAddress36Reverts v (by simp) hc1 rdAddr1).reEquivDecodingFailed hcode hd
              (decodeCalldata_address_address_uint256_none_noncanon1 hlen hhi hc0 hc1)
        · exact (decodeAddress4Reverts v (by simp) hc0 rdAddr0).reEquivDecodingFailed hcode hd
            (decodeCalldata_address_address_uint256_none_noncanon0 hlen hhi hc0)
      · have hguard := viaIRStaticLenCheckHuge (words := 3) (Nat.le_of_not_gt hhi) hsize (by decide)
        have rdRevert := poolManagerBlocks.poolManager_block_3127_taken (by simp)
          (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hj816 rdSize
        exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
          (decodeCalldata_address_address_uint256_none_huge (Nat.le_of_not_gt hhi))
    · have hguard := viaIRStaticLenCheckShort (words := 3) hsz (Nat.lt_of_not_ge hlen) (by decide) hsize
      have rdRevert := poolManagerBlocks.poolManager_block_3127_taken (by simp)
        (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hj816 rdSize
      exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
        (decodeCalldata_address_address_uint256_none_short hsz (Nat.lt_of_not_ge hlen))
  · have rdRevert := poolManagerBlocks.poolManager_block_3121_taken (by simp) hwv hj816 rdEntry
    exact selectedRevert hcode (emptyRevert v (by simp) rdRevert) hd (fun _ => bodyReverts_nonPayable hwv)

end Benchmarks.UniswapV4PoolManager
