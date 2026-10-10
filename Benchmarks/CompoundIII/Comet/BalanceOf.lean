import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.BalanceExternal
import Benchmarks.CompoundIII.Comet.BalanceEvm
import Benchmarks.CompoundIII.Comet.MappingGetter
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_009
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_012
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_022

/-!
# CometWithExtendedAssetList `balanceOf(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1114; reach lemma `cometWithExtendedAssetListReachBalanceOfBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables
open cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem balanceX {σ σ₀ A I} {g : Sat256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 30)) :
    CheckedAddressGetterResult
      (CurrentIndicesValid v (solcSlotWordAt ⟨0⟩ σ I) (solcSlotWordAt ⟨1⟩ σ I) (timestampWord I))
      (deployedRuntime v) I g (initState σ σ₀ g A I) σ
      (balanceWord v (solcSlotWordAt ⟨0⟩ σ I) (solcSlotWordAt ⟨1⟩ σ I) (timestampWord I)
        (userBasicWord σ I
          (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).toByteArray := by
  obtain ⟨k, C, rd⟩ := cometWithExtendedAssetListReachBalanceOfBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) v hcode hsz hsize hsel
  have rd1 := cometWithExtendedAssetList_block_1114 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd2 := cometWithExtendedAssetList_block_3999_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hv rd1
    by_cases hlo : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · have rd3 := cometWithExtendedAssetList_block_4006_fallthrough
          (immWords := wordsOf (immStore v)) (by decide)
          (calldataLength_ok (need := 32) (by decide) hlo hhi hsize) rd2
        have rd4 := cometWithExtendedAssetList_block_4018
          (immWords := wordsOf (immStore v)) (by decide)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd3
        by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨k', C', rd5⟩ := cometValidateAddress_ok (v := v)
            (ret := UInt256.ofNat 4034) (by change 8 ≤ 1024; decide) hc
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd4
          have rd6 := cometWithExtendedAssetList_block_4034
            (immWords := wordsOf (immStore v)) (by change 4 ≤ 1024; decide)
            (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd5
          have hb := cometBalance (v := v) (by change 35 ≤ 1024; decide) hc
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd6
          dsimp only at hb
          by_cases hvalid : CurrentIndicesValid v (solcSlotWordAt ⟨0⟩ σ I)
              (solcSlotWordAt ⟨1⟩ σ I) (timestampWord I)
          · rw [if_pos hvalid] at hb
            unfold CheckedAddressGetterResult
            rw [if_pos ⟨hv, hlo, hhi, hc, hvalid⟩]
            obtain ⟨aw', k'', C'', rd7⟩ := hb
            have rd8 := cometWithExtendedAssetList_block_1504
              (immWords := wordsOf (immStore v)) (by decide) rd7
            have hout := (mappingGetterReturnData (calldataWord I.calldata 4) ⟨5⟩
              (balanceWord v (solcSlotWordAt ⟨0⟩ σ I) (solcSlotWordAt ⟨1⟩ σ I) (timestampWord I)
                (solcSlotWordAt (solcMappingSlot ⟨5⟩ (calldataWord I.calldata 4)) σ I))) ▸ rd8
            simpa only [userBasicWord, userBasicSlot, addressWord_eq_ofNat_address hc] using hout
          · rw [if_neg hvalid] at hb
            simp only [CheckedAddressGetterResult, hvalid, and_false, if_false]
            exact hb
        · simp only [CheckedAddressGetterResult, hc, false_and, and_false, if_false]
          exact cometValidateAddress_bad (v := v) (by change 8 ≤ 1024; decide) hc rd4
      · simp only [CheckedAddressGetterResult, hhi, false_and, and_false, if_false]
        have rd3 := cometWithExtendedAssetList_block_4006_taken
          (immWords := wordsOf (immStore v)) (by decide)
          (calldataLength_huge (need := 32) (by decide) (by omega) hsize)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
        exact cometRevert1410 (by decide) rd3
    · simp only [CheckedAddressGetterResult, hlo, false_and, and_false, if_false]
      have rd3 := cometWithExtendedAssetList_block_4006_taken
        (immWords := wordsOf (immStore v)) (by decide)
        (calldataLength_short (need := 32) (by decide) hsz (by omega) hsize)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact cometRevert1410 (by decide) rd3
  · simp only [CheckedAddressGetterResult, hv, false_and, if_false]
    have rd2 := cometWithExtendedAssetList_block_3999_taken
      (immWords := wordsOf (immStore v)) (by decide) hv
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact cometRevert1410 (by decide) rd2



/-- `balanceOf(address)`: the theorem `Correct.lean` routes selector 30 to. -/
theorem cometWithExtendedAssetListBalanceOfBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 30)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 30) rfl hsel
  apply checkedAddressGetter_refines (t := balanceOfTransition) hcode hsz
    (cometSelectorDispatch ⟨30, by decide⟩ hsel) rfl balanceTransition_body
    (fun _ ↦ returnEquiv_of_encode (uint256ReturnEncoding _))
    ?_ ?_ (balanceX v hcode hsz hsize hsel)
  · intro hv hhi _ hvalid
    exact getBalance_returns v hv hhi hvalid
  · intro hv hhi hvalid
    exact getBalance_reverts v hv hhi hvalid

end Benchmarks.CompoundIII.Comet
