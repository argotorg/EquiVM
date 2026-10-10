import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.UserBasicFields
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_008
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_032

/-!
# CometWithExtendedAssetList `userBasic(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 835; reach lemma `cometWithExtendedAssetListReachUserBasicBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListBlocks
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem userBasic_returns {σ σ₀ A I} {g : Sat256} (imms : Store)
    (hvalue : I.weiValue = ⟨0⟩) (hhi : I.calldata.size < 2 ^ 255 + 4) :
    ∃ frame, ExecTransitionBody config contract (initState σ σ₀ g A I)
      (addressGetterArgs "arg0" I) userBasicTransition.body
      (.returned frame (initState σ σ₀ g A I)
        (some ((userBasicScalars (userBasicWord σ I
          (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).map ScalarReturn.value))) imms := by
  let frame := calldataLocalFrame
    { contract := contract, locals := addressGetterArgs "arg0" I, immutables := imms }
    (initState σ σ₀ g A I)
  let w := userBasicWord σ I (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
  refine ⟨frame, .execBlockRet ?_⟩
  apply (calldataPrologue_ok hvalue hhi).run
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  have he (i : Fin 4) : evalExpr? config frame (initState σ σ₀ g A I) (userBasicFieldExpr i) =
      .ok (.int (userBasicFieldWord w i).toNat) := by
    have h := evalUserBasicField (initState σ σ₀ g A I) frame.locals imms
      (AccountAddress.ofNat (calldataWord I.calldata 4).toNat) i
      (by simp [frame, calldataLocalFrame, addressGetterArgs])
      (by simp only [frame, calldataLocalFrame, addressGetterArgs, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert]; rfl)
    simpa only [storageLoad_initState_solcSlotWord, userBasicWord, solcSlotWordAt] using h
  have hp : evalExpr? config frame (initState σ σ₀ g A I) userBasicPrincipalExpr =
      .ok (.int (signed104 w)) := by
    have h := evalUserBasicPrincipal (initState σ σ₀ g A I) frame.locals imms
      (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
      (by simp [frame, calldataLocalFrame, addressGetterArgs])
      (by simp only [frame, calldataLocalFrame, addressGetterArgs, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert]; rfl)
    simpa only [storageLoad_initState_solcSlotWord, userBasicWord, solcSlotWordAt] using h
  change evalExprs? config frame (initState σ σ₀ g A I)
    [userBasicPrincipalExpr, userBasicFieldExpr 0, userBasicFieldExpr 1, userBasicFieldExpr 2, userBasicFieldExpr 3] = _
  simp only [evalExprs?, hp, he, pure, bind, EvalResult.bind]
  rfl

theorem userBasicX {σ σ₀ A I} {g : Sat256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 61)) :
    AddressGetterResult (deployedRuntime v) I g (initState σ σ₀ g A I) σ
      (wordBytes ((userBasicScalars (userBasicWord σ I
        (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).map ScalarReturn.word)) := by
  obtain ⟨k, C, rd⟩ := cometWithExtendedAssetListReachUserBasicBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) v hcode hsz hsize hsel
  have rd1 := cometWithExtendedAssetList_block_835 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd2 := cometWithExtendedAssetList_block_5932_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hv rd1
    by_cases hlo : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · have rd3 := cometWithExtendedAssetList_block_5939_fallthrough
          (immWords := wordsOf (immStore v)) (by decide)
          (calldataLength_ok (need := 32) (by decide) hlo hhi hsize) rd2
        have rd4 := cometWithExtendedAssetList_block_5951
          (immWords := wordsOf (immStore v)) (by decide)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd3
        by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · simp only [AddressGetterResult, hv, hlo, hhi, hc, and_self, if_true]
          obtain ⟨k', C', rd5⟩ := cometValidateAddress_ok (v := v) (ret := UInt256.ofNat 5962)
            (by change 6 ≤ 1024; decide) hc
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd4
          have rd6 := cometWithExtendedAssetList_block_5962
            (immWords := wordsOf (immStore v)) (by decide) rd5
          let w := calldataWord I.calldata 4
          have hclean : UInt256.land
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))
              (uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32)) = w :=
            solcAddrMask_clean_left hc
          rw [hclean] at rd6
          let mem := twoWordHashMem w ⟨5⟩ solcFreePtrMem
          have hmem : mem.size = 96 := twoWordHashMem_size_96 w ⟨5⟩ solcFreePtrMem_size
          have hhash : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem =
              solcMappingSlot ⟨5⟩ w := mappingGetterHash w ⟨5⟩
          have hload : memLoad (UInt256.ofNat 64) mem = ⟨128⟩ :=
            mloadFreePtrValue (by rw [hmem]; decide)
              (twoWordHashMem_read64 w ⟨5⟩ solcFreePtrMem_size solcFreePtrMem_read64)
          have hmemEq : (UInt256.ofNat 5).toByteArray.write 0
              (w.toByteArray.write 0
                ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty (UInt256.ofNat 64).toNat 32)
                (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32 = mem := rfl
          rw [hmemEq] at rd6
          rw [hhash, hload] at rd6
          let val := solcSlotWordAt (solcMappingSlot ⟨5⟩ w) σ I
          have hvalEq : (σ.get? I.codeOwner |>.option (⟨0⟩ : UInt256)
              (fun ac ↦ ac.storage.getD (solcMappingSlot ⟨5⟩ w) ⟨0⟩)) = val := rfl
          rw [hvalEq] at rd6
          obtain ⟨hf₀, hf₁, hf₂, hf₃⟩ := userBasicFieldWords val
          rw [← hf₀, ← hf₁, ← hf₂, ← hf₃] at rd6
          let a := UInt256.signextend ⟨12⟩ val
          let b := userBasicFieldWord val 0
          let c := userBasicFieldWord val 1
          let d := userBasicFieldWord val 2
          let e := userBasicFieldWord val 3
          change RDret _ _ _ _
            ((e.toByteArray.write 0 (d.toByteArray.write 0 (c.toByteArray.write 0
              (b.toByteArray.write 0 (solcScratchReturnMem mem a) 160 32) 192 32) 224 32)
                256 32).readWithPadding 128 160) at rd6
          rw [scratchWordsMem_single hmem] at rd6
          have hb : b.toByteArray.write 0 (scratchWordsMem mem [a]) 160 32 =
              scratchWordsMem mem [a, b] := scratchWordsMem_write hmem [a] b
          have hcwrite : c.toByteArray.write 0 (scratchWordsMem mem [a, b]) 192 32 =
              scratchWordsMem mem [a, b, c] := scratchWordsMem_write hmem [a, b] c
          have hd : d.toByteArray.write 0 (scratchWordsMem mem [a, b, c]) 224 32 =
              scratchWordsMem mem [a, b, c, d] := scratchWordsMem_write hmem [a, b, c] d
          have he : e.toByteArray.write 0 (scratchWordsMem mem [a, b, c, d]) 256 32 =
              scratchWordsMem mem [a, b, c, d, e] := scratchWordsMem_write hmem [a, b, c, d] e
          rw [hb, hcwrite, hd, he] at rd6
          have hret := (scratchWordsMem_read128 hmem [a, b, c, d, e]
            (by change 0 < 5; decide) (by change 160 < 2 ^ 64; decide)) ▸ rd6
          simpa only [userBasicWord, userBasicSlot, userBasicScalars, userBasicScalar,
            userBasicPrincipalScalar, List.map_cons, List.map_nil, addressWord_eq_ofNat_address hc]
            using hret
        · simp only [AddressGetterResult, hc, and_false, if_false]
          exact cometValidateAddress_bad (v := v) (by change 6 ≤ 1024; decide) hc rd4
      · simp only [AddressGetterResult, hhi, false_and, and_false, if_false]
        have rd3 := cometWithExtendedAssetList_block_5939_taken
          (immWords := wordsOf (immStore v)) (by decide)
          (calldataLength_huge (need := 32) (by decide) (by omega) hsize)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
        exact cometRevert1410 (by decide) rd3
    · simp only [AddressGetterResult, hlo, false_and, and_false, if_false]
      have rd3 := cometWithExtendedAssetList_block_5939_taken
        (immWords := wordsOf (immStore v)) (by decide)
        (calldataLength_short (need := 32) (by decide) hsz (by omega) hsize)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact cometRevert1410 (by decide) rd3
  · simp only [AddressGetterResult, hv, false_and, if_false]
    have rd2 := cometWithExtendedAssetList_block_5932_taken
      (immWords := wordsOf (immStore v)) (by decide) hv
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact cometRevert1410 (by decide) rd2

/-- `userBasic(address)`: the theorem `Correct.lean` routes selector 61 to. -/
theorem cometWithExtendedAssetListUserBasicBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 61)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 61) rfl hsel
  let w := userBasicWord σ I (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
  apply addressGetterValues_refines (t := userBasicTransition)
    (values := (userBasicScalars w).map ScalarReturn.value) hcode hsz
    (cometSelectorDispatch ⟨61, by decide⟩ hsel) rfl rfl ?_ ?_
    (userBasicX v hcode hsz hsize hsel)
  · exact .returned rfl (scalarReturnsEncoding (userBasicScalars w))
  · intro hv hhi _
    exact userBasic_returns (immStore v) hv hhi

end Benchmarks.CompoundIII.Comet
