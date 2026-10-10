import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.Storage
import Benchmarks.CompoundIII.Comet.MappingGetter
import Benchmarks.CompoundIII.Comet.TwoAddressDecode
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_009
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_026

/-!
# CometWithExtendedAssetList `isAllowed(address,address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 988; reach lemma `cometWithExtendedAssetListReachIsAllowedBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListBlocks
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem isAllowed_returns {σ σ₀ A I} {g : Sat256} (imms : Store)
    (hvalue : I.weiValue = ⟨0⟩) (hhi : I.calldata.size < 2 ^ 255 + 4) :
    ∃ frame, ExecTransitionBody config contract (initState σ σ₀ g A I)
      (twoAddressGetterArgs "arg0" "arg1" I) isAllowedTransition.body
      (.returned frame (initState σ σ₀ g A I)
        (some [wordToElem .bool (isAllowedWord σ I
          (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
          (AccountAddress.ofNat (calldataWord I.calldata 36).toNat))])) imms := by
  let frame := calldataLocalFrame
    { contract := contract, locals := twoAddressGetterArgs "arg0" "arg1" I, immutables := imms }
    (initState σ σ₀ g A I)
  refine ⟨frame, .execBlockRet ?_⟩
  apply (calldataPrologue_ok hvalue hhi).returns
  have he := evalIsAllowed (initState σ σ₀ g A I) frame.locals
    imms (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
    (AccountAddress.ofNat (calldataWord I.calldata 36).toNat) "arg0" "arg1"
    (by simp [frame, calldataLocalFrame, twoAddressGetterArgs, addressGetterArgs])
    (by simp only [frame, calldataLocalFrame, twoAddressGetterArgs, addressGetterArgs,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl)
    (by simp only [frame, calldataLocalFrame, twoAddressGetterArgs, addressGetterArgs,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl)
  simpa only [storageLoad_initState_solcSlotWord, isAllowedWord, solcSlotWordAt] using he

theorem isAllowedX {σ σ₀ A I} {g : Sat256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 45)) :
    TwoAddressGetterResult (deployedRuntime v) I g (initState σ σ₀ g A I) σ
      (UInt256.isZero (UInt256.isZero (isAllowedWord σ I
        (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
        (AccountAddress.ofNat (calldataWord I.calldata 36).toNat)))).toByteArray := by
  obtain ⟨k, C, rd⟩ := cometWithExtendedAssetListReachIsAllowedBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) v hcode hsz hsize hsel
  have rd1 := cometWithExtendedAssetList_block_988 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd2 := cometWithExtendedAssetList_block_4734_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hv rd1
    have rd3 := cometWithExtendedAssetList_block_4741 (immWords := wordsOf (immStore v))
      (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
    have hdecode := cometDecodeTwoAddresses (v := v) (ret := ⟨4758⟩)
      (by change 12 ≤ 1024; decide) hsz hsize
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
      have rd5 := cometWithExtendedAssetList_block_4758 (immWords := wordsOf (immStore v))
        (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd4
      let w₀ := calldataWord I.calldata 4
      let w₁ := calldataWord I.calldata 36
      have hclean₀ : UInt256.land w₀
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
            (UInt256.ofNat 1)) = w₀ := solcAddrMask_clean hc₀
      unfold cometWithExtendedAssetList_block_4758_stack
        cometWithExtendedAssetList_block_4758_memory at rd5
      rw [hclean₀] at rd5
      let mem₀ := twoWordHashMem w₀ ⟨3⟩ solcFreePtrMem
      let slot₀ := solcMappingSlot ⟨3⟩ w₀
      have hhash₀ : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem₀ = slot₀ :=
        mappingGetterHash w₀ ⟨3⟩
      change RD _ _ _ _ _ [keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem₀,
        w₁, ⟨4787⟩, ⟨255⟩, ⟨32⟩] mem₀ _ _ _ _ _ at rd5
      rw [hhash₀] at rd5
      have rd6 := cometWithExtendedAssetList_block_2428 (immWords := wordsOf (immStore v))
        (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd5
      have hclean₁ : UInt256.land
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
            (UInt256.ofNat 1)) w₁ = w₁ := solcAddrMask_clean_left hc₁
      unfold cometWithExtendedAssetList_block_2428_stack
        cometWithExtendedAssetList_block_2428_memory at rd6
      rw [hclean₁] at rd6
      let mem₁ := twoWordHashMem w₁ slot₀ mem₀
      let slot₁ := solcMappingSlot slot₀ w₁
      have hmem₀ : mem₀.size = 96 := twoWordHashMem_size_96 w₀ ⟨3⟩ solcFreePtrMem_size
      have hmem₁ : mem₁.size = 96 := twoWordHashMem_size_96 w₁ slot₀ hmem₀
      have hhash₁ : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem₁ = slot₁ :=
        twoWordHashMem_solcMappingSlot slot₀ w₁ hmem₀
      change RD _ _ _ _ _ [keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem₁, ⟨255⟩, ⟨32⟩]
        mem₁ _ _ _ _ _ at rd6
      rw [hhash₁] at rd6
      have rd7 := cometWithExtendedAssetList_block_4787
        (immWords := wordsOf (immStore v)) (by decide) rd6
      have hload : memLoad (UInt256.ofNat 64) mem₁ = ⟨128⟩ :=
        mloadFreePtrValue (by rw [hmem₁]; decide)
          (twoWordHashMem_read64 w₁ slot₀ hmem₀
            (twoWordHashMem_read64 w₀ ⟨3⟩ solcFreePtrMem_size solcFreePtrMem_read64))
      let val := solcSlotWordAt slot₁ σ I
      let out := UInt256.isZero (UInt256.isZero (UInt256.land val ⟨255⟩))
      change RDret _ _ _ _
        ((out.toByteArray.write 0 mem₁ (memLoad (UInt256.ofNat 64) mem₁).toNat 32).readWithPadding
          (memLoad (UInt256.ofNat 64) mem₁).toNat 32) at rd7
      rw [hload] at rd7
      have hret := (solcScratchReturnMem_read128 out hmem₁) ▸ rd7
      simpa only [isAllowedWord, isAllowedSlot,
        addressWord_eq_ofNat_address hc₀, addressWord_eq_ofNat_address hc₁] using hret
    · rw [if_neg hd] at hdecode
      simpa only [TwoAddressGetterResult, hv, true_and, hd, if_false] using hdecode
  · simp only [TwoAddressGetterResult, hv, false_and, if_false]
    have rd2 := cometWithExtendedAssetList_block_4734_taken
      (immWords := wordsOf (immStore v)) (by decide) hv
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact cometRevert1410 (by decide) rd2

/-- `isAllowed(address,address)`: the theorem `Correct.lean` routes selector 45 to. -/
theorem cometWithExtendedAssetListIsAllowedBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 45)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 45) rfl hsel
  let w := isAllowedWord σ I
    (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
    (AccountAddress.ofNat (calldataWord I.calldata 36).toNat)
  apply twoAddressGetter_refines (t := isAllowedTransition)
    (values := [wordToElem .bool w]) hcode hsz
    (cometSelectorDispatch ⟨45, by decide⟩ hsel) rfl rfl ?_ ?_
    (isAllowedX v hcode hsz hsize hsel)
  · exact returnEquiv_of_encode (boolWordReturnEncoding _)
  · intro hv hhi _ _
    exact isAllowed_returns (immStore v) hv hhi

end Benchmarks.CompoundIII.Comet
