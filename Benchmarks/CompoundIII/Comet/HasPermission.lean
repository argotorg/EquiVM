import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.PermissionSource
import Benchmarks.CompoundIII.Comet.PermissionEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_008
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_031

/-!
# CometWithExtendedAssetList `hasPermission(address,address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 862; reach lemma `cometWithExtendedAssetListReachHasPermissionBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListBlocks
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem hasPermission_returns {σ σ₀ A I} {g : Sat256} (imms : Store)
    (hvalue : I.weiValue = ⟨0⟩) (hhi : I.calldata.size < 2 ^ 255 + 4) :
    ∃ frame, ExecTransitionBody config contract (initState σ σ₀ g A I)
      (twoAddressGetterArgs "owner" "manager" I) hasPermissionTransition.body
      (.returned frame (initState σ σ₀ g A I)
        (some [.bool (permissionBool (initState σ σ₀ g A I)
          (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
          (AccountAddress.ofNat (calldataWord I.calldata 36).toNat))])) imms := by
  let caller : Frame :=
    { contract := contract, locals := twoAddressGetterArgs "owner" "manager" I, immutables := imms }
  let frame := calldataLocalFrame caller (initState σ σ₀ g A I)
  let value := permissionBool (initState σ σ₀ g A I)
    (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
    (AccountAddress.ofNat (calldataWord I.calldata 36).toNat)
  refine ⟨{ frame with locals := frame.locals.insert "result" (.bool value) }, .execBlockRet ?_⟩
  apply (calldataPrologue_ok hvalue hhi).run
  apply ExecBlock.consNormal
    (hasPermission_call frame (initState σ σ₀ g A I) _ _ (.var "owner") (.var "manager") "result" rfl ?_ ?_)
  · exact ABlock.start.returns (by
      simp only [evalExpr?, EvalResult.ofOption, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      rfl)
  · simp only [evalExpr?, frame, caller, calldataLocalFrame, twoAddressGetterArgs, addressGetterArgs,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  · simp only [evalExpr?, frame, caller, calldataLocalFrame, twoAddressGetterArgs, addressGetterArgs,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl

theorem permissionBool_init {σ σ₀ A I} {g : Sat256} {owner manager : UInt256}
    (ho : owner.toNat < EVM.addressModulus) (hm : manager.toNat < EVM.addressModulus) :
    permissionBool (initState σ σ₀ g A I)
      (AccountAddress.ofNat owner.toNat) (AccountAddress.ofNat manager.toNat) =
      decide ((permissionRuntimeWord σ I owner manager).toNat ≠ 0) := by
  have heq : AccountAddress.ofNat owner.toNat = AccountAddress.ofNat manager.toNat ↔
      owner = manager := by
    simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using
      accountAddress_ofUInt256_eq_iff_of_canonical ho hm
  simp only [permissionBool, storageLoad_initState_solcSlotWord, heq, isAllowedSlot,
    addressWord_eq_ofNat_address ho, addressWord_eq_ofNat_address hm, permissionRuntimeWord]
  by_cases h : owner = manager <;> simp [h, solcSlotWordAt, UInt256.toNat]
  decide

theorem hasPermissionX {σ σ₀ A I} {g : Sat256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 58)) :
    TwoAddressGetterResult (deployedRuntime v) I g (initState σ σ₀ g A I) σ
      (UInt256.isZero (UInt256.isZero (permissionRuntimeWord σ I
        (calldataWord I.calldata 4) (calldataWord I.calldata 36)))).toByteArray := by
  obtain ⟨k, C, rd⟩ := cometWithExtendedAssetListReachHasPermissionBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) v hcode hsz hsize hsel
  have rd1 := cometWithExtendedAssetList_block_862 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd2 := cometWithExtendedAssetList_block_5834_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hv rd1
    have rd3 := cometWithExtendedAssetList_block_5841 (immWords := wordsOf (immStore v))
      (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
    have hdecode := cometDecodeTwoAddresses (v := v) (ret := ⟨5856⟩)
      (by change 11 ≤ 1024; decide) hsz hsize
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd3
    by_cases hd : TwoAddressCalldataValid I
    · rw [if_pos hd] at hdecode
      simp only [TwoAddressGetterResult, hv, true_and,
        show 68 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4 ∧
          (calldataWord I.calldata 4).toNat < EVM.addressModulus ∧
          (calldataWord I.calldata 36).toNat < EVM.addressModulus from hd, if_true]
      obtain ⟨k₄, C₄, rd4⟩ := hdecode
      have hc₀ := hd.2.2.1
      have hc₁ := hd.2.2.2
      have rd5 := cometWithExtendedAssetList_block_5856 (immWords := wordsOf (immStore v))
        (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd4
      obtain ⟨aw₆, k₆, C₆, rd6⟩ := cometHasPermission (v := v)
        (by change 9 ≤ 1024; decide) hc₀ hc₁
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd5
      have rd7 := cometWithExtendedAssetList_block_1455 (immWords := wordsOf (immStore v))
        (by decide) rd6
      let w₀ := calldataWord I.calldata 4
      let w₁ := calldataWord I.calldata 36
      let mem := permissionMemory w₀ w₁ solcFreePtrMem
      have hmem : mem.size = 96 := permissionMemory_size w₀ w₁ solcFreePtrMem_size
      have hload : memLoad (UInt256.ofNat 64) mem = ⟨128⟩ :=
        mloadFreePtrValue (by rw [hmem]; decide)
          (permissionMemory_read64 w₀ w₁ solcFreePtrMem_size solcFreePtrMem_read64)
      let out := UInt256.isZero (UInt256.isZero (permissionRuntimeWord σ I w₀ w₁))
      change RDret _ _ _ _
        ((out.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32).readWithPadding
          (memLoad (UInt256.ofNat 64) mem).toNat 32) at rd7
      rw [hload] at rd7
      exact (solcScratchReturnMem_read128 out hmem) ▸ rd7
    · rw [if_neg hd] at hdecode
      simpa only [TwoAddressGetterResult, hv, true_and, hd, if_false] using hdecode
  · simp only [TwoAddressGetterResult, hv, false_and, if_false]
    have rd2 := cometWithExtendedAssetList_block_5834_taken
      (immWords := wordsOf (immStore v)) (by decide) hv
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact cometRevert1410 (by decide) rd2

/-- `hasPermission(address,address)`: the theorem `Correct.lean` routes selector 58 to. -/
theorem cometWithExtendedAssetListHasPermissionBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 58)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 58) rfl hsel
  let w := permissionRuntimeWord σ I (calldataWord I.calldata 4) (calldataWord I.calldata 36)
  apply twoAddressGetter_refines (t := hasPermissionTransition)
    (values := [.bool (decide (w.toNat ≠ 0))]) hcode hsz
    (cometSelectorDispatch ⟨58, by decide⟩ hsel) rfl rfl ?_ ?_
    (hasPermissionX v hcode hsz hsize hsel)
  · exact returnEquiv_of_encode (nonzeroReturnEncoding w)
  · intro hv hhi hc₀ hc₁
    simpa only [permissionBool_init hc₀ hc₁] using hasPermission_returns (immStore v) hv hhi

end Benchmarks.CompoundIII.Comet
