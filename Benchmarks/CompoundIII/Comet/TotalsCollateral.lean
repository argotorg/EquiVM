import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.PackedReturn
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_010
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_016
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_021
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_022

/-!
# CometWithExtendedAssetList `totalsCollateral(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1141; reach lemma `cometWithExtendedAssetListReachTotalsCollateralBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListBlocks
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def totalsCollateralSlot (addr : AccountAddress) : UInt256 :=
  solcMappingSlot ⟨2⟩ (EVM.word addr.val)

def totalsCollateralWord (σ : AccountMap) (I : ExecutionEnv) (addr : AccountAddress) : UInt256 :=
  solcSlotWordAt (totalsCollateralSlot addr) σ I

theorem evalTotalsCollateralField (evm : EVM.State) (locals imms : Store)
    (addr : AccountAddress) (upper : Bool)
    (hlocal : locals.get? "totalsCollateral" = none)
    (harg : locals.get? "arg0" = some (.address addr)) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm (.storage ⟨"totalsCollateral", [.mindex (.var "arg0"),
        .field (if upper then "_reserved" else "totalSupplyAsset")]⟩) =
      .ok (.int ((if upper then high128 else low128)
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (totalsCollateralSlot addr))).toNat) := by
  cases upper
  · apply evalExpr_storage_scalar_value (hbackend := rfl)
      (loc := { slot := totalsCollateralSlot addr, offset := ⟨0, by decide⟩, size := ⟨16, by decide⟩, hbound := by decide, type := .int (.uint ⟨128, by decide⟩) })
      (er := ⟨"totalsCollateral", [.mindex (.address addr), .field "totalSupplyAsset"]⟩)
      (t := .int (.uint ⟨128, by decide⟩)) hlocal
    · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, harg,
        valueToKey?, pure, bind, EvalResult.bind, EvalResult.ofOption, Bool.false_eq_true, if_false]
    · change storageTypeAt? contract.storage
        ⟨"totalsCollateral", [.mindex (.address addr), .field "totalSupplyAsset"]⟩ = _
      rfl
    · simp only [totalsCollateralSlot, solcMappingSlot, keyValueToWord_address]
      rfl
    · exact low128_load evm (totalsCollateralSlot addr)
  · apply evalExpr_storage_scalar_value (hbackend := rfl)
      (loc := { slot := totalsCollateralSlot addr, offset := ⟨16, by decide⟩, size := ⟨16, by decide⟩, hbound := by decide, type := .int (.uint ⟨128, by decide⟩) })
      (er := ⟨"totalsCollateral", [.mindex (.address addr), .field "_reserved"]⟩)
      (t := .int (.uint ⟨128, by decide⟩)) hlocal
    · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, harg,
        valueToKey?, pure, bind, EvalResult.bind, EvalResult.ofOption, if_true]
    · change storageTypeAt? contract.storage
        ⟨"totalsCollateral", [.mindex (.address addr), .field "_reserved"]⟩ = _
      rfl
    · simp only [totalsCollateralSlot, solcMappingSlot, keyValueToWord_address]
      rfl
    · exact high128_load evm (totalsCollateralSlot addr)

theorem totalsCollateral_returns {σ σ₀ A I} {g : Sat256} (imms : Store)
    (hvalue : I.weiValue = ⟨0⟩) (hhi : I.calldata.size < 2 ^ 255 + 4) :
    ∃ frame, ExecTransitionBody config contract (initState σ σ₀ g A I)
      (addressGetterArgs "arg0" I) totalsCollateralTransition.body
      (.returned frame (initState σ σ₀ g A I)
        (some [.int (low128 (totalsCollateralWord σ I
          (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).toNat,
        .int (high128 (totalsCollateralWord σ I
          (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).toNat])) imms := by
  let frame := calldataLocalFrame
    { contract := contract, locals := addressGetterArgs "arg0" I, immutables := imms }
    (initState σ σ₀ g A I)
  refine ⟨frame, .execBlockRet ?_⟩
  apply (calldataPrologue_ok hvalue hhi).run
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  have he (upper : Bool) := evalTotalsCollateralField (initState σ σ₀ g A I) frame.locals
    imms (AccountAddress.ofNat (calldataWord I.calldata 4).toNat) upper
    (by simp [frame, calldataLocalFrame, addressGetterArgs])
    (by simp only [frame, calldataLocalFrame, addressGetterArgs, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert]; rfl)
  have hlo := he false
  have hhi := he true
  simp only [Bool.false_eq_true, if_false, if_true, storageLoad_initState_solcSlotWord] at hlo hhi
  change evalExpr? config frame _ _ = _ at hlo hhi
  change evalExprs? config frame _ _ = _
  simp only [evalExprs?, hlo, hhi, pure, bind, EvalResult.bind]
  rfl

theorem totalsCollateralX {σ σ₀ A I} {g : Sat256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 27)) :
    AddressGetterResult (deployedRuntime v) I g (initState σ σ₀ g A I) σ
      ((low128 (totalsCollateralWord σ I (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).toByteArray ++
        (high128 (totalsCollateralWord σ I (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).toByteArray) := by
  obtain ⟨k, C, rd⟩ := cometWithExtendedAssetListReachTotalsCollateralBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) v hcode hsz hsize hsel
  have rd1 := cometWithExtendedAssetList_block_1141 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd2 := cometWithExtendedAssetList_block_3814_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hv rd1
    by_cases hlo : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · have rd3 := cometWithExtendedAssetList_block_3821_fallthrough
          (immWords := wordsOf (immStore v)) (by decide)
          (calldataLength_ok (need := 32) (by decide) hlo hhi hsize) rd2
        have rd4 := cometWithExtendedAssetList_block_3833
          (immWords := wordsOf (immStore v)) (by decide)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd3
        by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · simp only [AddressGetterResult, hv, hlo, hhi, hc, and_self, if_true]
          obtain ⟨k', C', rd5⟩ := cometValidateAddress_ok (v := v) (ret := UInt256.ofNat 3844)
            (by change 6 ≤ 1024; decide) hc
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd4
          obtain ⟨k'', C'', rd6⟩ := cometWithExtendedAssetList_block_3844
            (immWords := wordsOf (immStore v)) (by decide)
            (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd5
          let w := calldataWord I.calldata 4
          have hclean : UInt256.land
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))
              (uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32)) = w :=
            solcAddrMask_clean_left hc
          unfold cometWithExtendedAssetList_block_3844_stack
            cometWithExtendedAssetList_block_3844_memory at rd6
          rw [hclean] at rd6
          let mem := twoWordHashMem w ⟨2⟩ solcFreePtrMem
          have hhash : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem =
              solcMappingSlot ⟨2⟩ w := mappingGetterHash w ⟨2⟩
          have hmem : mem.size = 96 := twoWordHashMem_size_96 w ⟨2⟩ solcFreePtrMem_size
          have hload : memLoad (UInt256.ofNat 64) mem = ⟨128⟩ :=
            mloadFreePtrValue (by rw [hmem]; decide)
              (twoWordHashMem_read64 w ⟨2⟩ solcFreePtrMem_size solcFreePtrMem_read64)
          let val := solcSlotWordAt (solcMappingSlot ⟨2⟩ w) σ I
          change RD _ _ _ _ _
            [memLoad (UInt256.ofNat 64) mem,
              UInt256.land (UInt256.ofNat (2 ^ 128 - 1))
                (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem) σ I),
              high128 (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem) σ I),
              UInt256.ofNat 2570, memLoad (UInt256.ofNat 64) mem, memLoad (UInt256.ofNat 64) mem]
            mem _ _ _ _ _ at rd6
          rw [hload, hhash] at rd6
          have hlow : UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) val = low128 val :=
            u256_land_comm _ _
          rw [hlow] at rd6
          have hret := cometReturnUint128Pair (v := v) (by change 9 ≤ 1024; decide)
            (low128_lt val) (high128_lt val) hmem rd6
          simpa only [totalsCollateralWord, totalsCollateralSlot, addressWord_eq_ofNat_address hc]
            using hret
        · simp only [AddressGetterResult, hc, and_false, if_false]
          exact cometValidateAddress_bad (v := v) (by change 6 ≤ 1024; decide) hc rd4
      · simp only [AddressGetterResult, hhi, false_and, and_false, if_false]
        have rd3 := cometWithExtendedAssetList_block_3821_taken
          (immWords := wordsOf (immStore v)) (by decide)
          (calldataLength_huge (need := 32) (by decide) (by omega) hsize)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
        exact cometRevert1410 (by decide) rd3
    · simp only [AddressGetterResult, hlo, false_and, and_false, if_false]
      have rd3 := cometWithExtendedAssetList_block_3821_taken
        (immWords := wordsOf (immStore v)) (by decide)
        (calldataLength_short (need := 32) (by decide) hsz (by omega) hsize)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact cometRevert1410 (by decide) rd3
  · simp only [AddressGetterResult, hv, false_and, if_false]
    have rd2 := cometWithExtendedAssetList_block_3814_taken
      (immWords := wordsOf (immStore v)) (by decide) hv
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact cometRevert1410 (by decide) rd2

/-- `totalsCollateral(address)`: the theorem `Correct.lean` routes selector 27 to. -/
theorem cometWithExtendedAssetListTotalsCollateralBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 27)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 27) rfl hsel
  let w := totalsCollateralWord σ I (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
  apply addressGetterValues_refines (t := totalsCollateralTransition)
    (values := [.int (low128 w).toNat, .int (high128 w).toNat]) hcode hsz
    (cometSelectorDispatch ⟨27, by decide⟩ hsel) rfl rfl ?_ ?_
    (totalsCollateralX v hcode hsz hsize hsel)
  · exact .returned rfl (scalarPairReturnEncoding
      (uintWordEncoding ⟨128, by decide⟩ _ (by decide) (low128_lt _))
      (uintWordEncoding ⟨128, by decide⟩ _ (by decide) (high128_lt _)))
  · intro hv hhi _
    exact totalsCollateral_returns (immStore v) hv hhi

end Benchmarks.CompoundIII.Comet
