import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.StaticReturns
import Benchmarks.CompoundIII.Comet.PackedFields
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_008
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_030
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_031

/-!
# CometWithExtendedAssetList `liquidatorPoints(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 880; reach lemma `cometWithExtendedAssetListReachLiquidatorPointsBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListBlocks
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def liquidatorSlot (addr : AccountAddress) : UInt256 :=
  solcMappingSlot ⟨7⟩ (EVM.word addr.val)

def liquidatorWord (σ : AccountMap) (I : ExecutionEnv) (addr : AccountAddress) : UInt256 :=
  solcSlotWordAt (liquidatorSlot addr) σ I

def liquidatorFieldName (i : Fin 4) : Ident :=
  match i.val with
  | 0 => "numAbsorbs"
  | 1 => "numAbsorbed"
  | 2 => "approxSpend"
  | _ => "_reserved"

def liquidatorFieldOffset (i : Fin 4) : Fin 32 :=
  match i.val with
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨4, by decide⟩
  | 2 => ⟨12, by decide⟩
  | _ => ⟨28, by decide⟩

def liquidatorFieldSize (i : Fin 4) : Fin 33 :=
  match i.val with
  | 0 => ⟨4, by decide⟩
  | 1 => ⟨8, by decide⟩
  | 2 => ⟨16, by decide⟩
  | _ => ⟨4, by decide⟩

def liquidatorFieldWidth (i : Fin 4) : BitWidth :=
  ⟨8 * (liquidatorFieldSize i).val, by rcases i with ⟨i, hi⟩; interval_cases i <;> dsimp only [liquidatorFieldSize, liquidatorFieldOffset] <;> decide⟩

def liquidatorFieldWord (w : UInt256) (i : Fin 4) : UInt256 :=
  packedUint w (liquidatorFieldOffset i).val (liquidatorFieldSize i).val

def liquidatorFieldExpr (i : Fin 4) : Expr :=
  .storage ⟨"liquidatorPoints", [.mindex (.var "arg0"), .field (liquidatorFieldName i)]⟩

theorem liquidatorFieldWords (w : UInt256) :
    liquidatorFieldWord w 0 = UInt256.land w (UInt256.ofNat 4294967295) ∧
    liquidatorFieldWord w 1 = UInt256.land (UInt256.shiftRight w (UInt256.ofNat 32))
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1)) ∧
    liquidatorFieldWord w 2 = UInt256.land (UInt256.shiftRight w (UInt256.ofNat 96))
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) ∧
    liquidatorFieldWord w 3 = UInt256.shiftRight w (UInt256.ofNat 224) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change UInt256.land (UInt256.div w ⟨1⟩) _ = _
    rw [word_div_one]
    rfl
  · change UInt256.land (UInt256.div w (UInt256.ofNat (256 ^ (4 : Fin 32).val))) _ = _
    rw [divBytePow_eq_shift]
    rfl
  · change UInt256.land (UInt256.div w (UInt256.ofNat (256 ^ (12 : Fin 32).val))) _ = _
    rw [divBytePow_eq_shift]
    rfl
  · change UInt256.land (UInt256.div w (UInt256.ofNat (256 ^ (28 : Fin 32).val))) _ = _
    rw [divBytePow_eq_shift]
    apply u256LandMaskCleanOfToNat (bits := 32) _ _ rfl
    change (UInt256.shiftRight w ⟨224⟩).toNat < 2 ^ 32
    simp [UInt256.shiftRight, UInt256.toNat, Fin.shiftRight_val,
      Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul w.val.isLt

theorem evalLiquidatorField (evm : EVM.State) (locals imms : Store)
    (addr : AccountAddress) (i : Fin 4)
    (hlocal : locals.get? "liquidatorPoints" = none)
    (harg : locals.get? "arg0" = some (.address addr)) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm (liquidatorFieldExpr i) =
      .ok (.int (liquidatorFieldWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (liquidatorSlot addr)) i).toNat) := by
  have hbound : (liquidatorFieldOffset i).val + (liquidatorFieldSize i).val - 1 < 32 := by
    rcases i with ⟨i, hi⟩; interval_cases i <;> dsimp only [liquidatorFieldSize, liquidatorFieldOffset] <;> decide
  apply evalExpr_storage_scalar_value (hbackend := rfl)
    (loc := { slot := liquidatorSlot addr, offset := liquidatorFieldOffset i,
              size := liquidatorFieldSize i, hbound := hbound,
              type := .int (.uint (liquidatorFieldWidth i)) })
    (er := ⟨"liquidatorPoints", [.mindex (.address addr), .field (liquidatorFieldName i)]⟩)
    (t := .int (.uint (liquidatorFieldWidth i))) hlocal
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, harg,
      valueToKey?, pure, bind, EvalResult.bind, EvalResult.ofOption]
  · change storageTypeAt? contract.storage
      ⟨"liquidatorPoints", [.mindex (.address addr), .field (liquidatorFieldName i)]⟩ = _
    rcases i with ⟨i, hi⟩; interval_cases i <;> rfl
  · rcases i with ⟨i, hi⟩
    interval_cases i <;>
      simp only [liquidatorSlot, liquidatorFieldName, liquidatorFieldOffset, liquidatorFieldSize,
        liquidatorFieldWidth, solcMappingSlot, keyValueToWord_address] <;> rfl
  · exact packedUint_load evm (liquidatorSlot addr) (liquidatorFieldOffset i)
      (liquidatorFieldSize i) (liquidatorFieldWidth i) rfl

def liquidatorScalar (w : UInt256) (i : Fin 4) : ScalarReturn :=
  { type := .int (.uint (liquidatorFieldWidth i))
    value := .int (liquidatorFieldWord w i).toNat
    word := liquidatorFieldWord w i
    encoded := uintWordEncoding (liquidatorFieldWidth i) _
      (Nat.ne_of_gt (liquidatorFieldWidth i).property.1)
      (packedUint_lt w _ (by omega)) }

def liquidatorScalars (w : UInt256) : List ScalarReturn :=
  [liquidatorScalar w 0, liquidatorScalar w 1, liquidatorScalar w 2, liquidatorScalar w 3]

theorem liquidatorPoints_returns {σ σ₀ A I} {g : Sat256} (imms : Store)
    (hvalue : I.weiValue = ⟨0⟩) (hhi : I.calldata.size < 2 ^ 255 + 4) :
    ∃ frame, ExecTransitionBody config contract (initState σ σ₀ g A I)
      (addressGetterArgs "arg0" I) liquidatorPointsTransition.body
      (.returned frame (initState σ σ₀ g A I)
        (some ((liquidatorScalars (liquidatorWord σ I
          (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).map ScalarReturn.value))) imms := by
  let frame := calldataLocalFrame
    { contract := contract, locals := addressGetterArgs "arg0" I, immutables := imms }
    (initState σ σ₀ g A I)
  let w := liquidatorWord σ I (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
  refine ⟨frame, .execBlockRet ?_⟩
  apply (calldataPrologue_ok hvalue hhi).run
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  have he (i : Fin 4) : evalExpr? config frame (initState σ σ₀ g A I) (liquidatorFieldExpr i) =
      .ok (.int (liquidatorFieldWord w i).toNat) := by
    have h := evalLiquidatorField (initState σ σ₀ g A I) frame.locals imms
      (AccountAddress.ofNat (calldataWord I.calldata 4).toNat) i
      (by simp [frame, calldataLocalFrame, addressGetterArgs])
      (by simp only [frame, calldataLocalFrame, addressGetterArgs, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert]; rfl)
    simpa only [storageLoad_initState_solcSlotWord, liquidatorWord, solcSlotWordAt] using h
  change evalExprs? config frame (initState σ σ₀ g A I)
    [liquidatorFieldExpr 0, liquidatorFieldExpr 1, liquidatorFieldExpr 2, liquidatorFieldExpr 3] = _
  simp only [evalExprs?, he, pure, bind, EvalResult.bind]
  rfl

theorem liquidatorPointsX {σ σ₀ A I} {g : Sat256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 56)) :
    AddressGetterResult (deployedRuntime v) I g (initState σ σ₀ g A I) σ
      (wordBytes ((liquidatorScalars (liquidatorWord σ I
        (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).map ScalarReturn.word)) := by
  obtain ⟨k, C, rd⟩ := cometWithExtendedAssetListReachLiquidatorPointsBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) v hcode hsz hsize hsel
  have rd1 := cometWithExtendedAssetList_block_880 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd2 := cometWithExtendedAssetList_block_5672_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hv rd1
    by_cases hlo : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · have rd3 := cometWithExtendedAssetList_block_5679_fallthrough
          (immWords := wordsOf (immStore v)) (by decide)
          (calldataLength_ok (need := 32) (by decide) hlo hhi hsize) rd2
        have rd4 := cometWithExtendedAssetList_block_5691
          (immWords := wordsOf (immStore v)) (by decide)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd3
        by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · simp only [AddressGetterResult, hv, hlo, hhi, hc, and_self, if_true]
          obtain ⟨k', C', rd5⟩ := cometValidateAddress_ok (v := v) (ret := UInt256.ofNat 5702)
            (by change 6 ≤ 1024; decide) hc
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd4
          have rd6 := cometWithExtendedAssetList_block_5702
            (immWords := wordsOf (immStore v)) (by decide) rd5
          let w := calldataWord I.calldata 4
          have hclean : UInt256.land
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))
              (uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32)) = w :=
            solcAddrMask_clean_left hc
          rw [hclean] at rd6
          let mem := twoWordHashMem w ⟨7⟩ solcFreePtrMem
          have hmem : mem.size = 96 := twoWordHashMem_size_96 w ⟨7⟩ solcFreePtrMem_size
          have hhash : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem =
              solcMappingSlot ⟨7⟩ w := mappingGetterHash w ⟨7⟩
          have hload : memLoad (UInt256.ofNat 64) mem = ⟨128⟩ :=
            mloadFreePtrValue (by rw [hmem]; decide)
              (twoWordHashMem_read64 w ⟨7⟩ solcFreePtrMem_size solcFreePtrMem_read64)
          have hmemEq : (UInt256.ofNat 7).toByteArray.write 0
              (w.toByteArray.write 0
                ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty (UInt256.ofNat 64).toNat 32)
                (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32 = mem := rfl
          rw [hmemEq] at rd6
          rw [hhash, hload] at rd6
          let val := solcSlotWordAt (solcMappingSlot ⟨7⟩ w) σ I
          have hvalEq : (σ.get? I.codeOwner |>.option (⟨0⟩ : UInt256)
              (fun ac ↦ ac.storage.getD (solcMappingSlot ⟨7⟩ w) ⟨0⟩)) = val := rfl
          rw [hvalEq] at rd6
          obtain ⟨hf₀, hf₁, hf₂, hf₃⟩ := liquidatorFieldWords val
          rw [← hf₀, ← hf₁, ← hf₂, ← hf₃] at rd6
          let a := liquidatorFieldWord val 0
          let b := liquidatorFieldWord val 1
          let c := liquidatorFieldWord val 2
          let d := liquidatorFieldWord val 3
          change RDret _ _ _ _
            ((d.toByteArray.write 0 (c.toByteArray.write 0
              (b.toByteArray.write 0 (solcScratchReturnMem mem a) 160 32) 192 32) 224 32).readWithPadding
              128 128) at rd6
          rw [scratchWordsMem_single hmem] at rd6
          have hb : b.toByteArray.write 0 (scratchWordsMem mem [a]) 160 32 =
              scratchWordsMem mem [a, b] := scratchWordsMem_write hmem [a] b
          have hcwrite : c.toByteArray.write 0 (scratchWordsMem mem [a, b]) 192 32 =
              scratchWordsMem mem [a, b, c] := scratchWordsMem_write hmem [a, b] c
          have hd : d.toByteArray.write 0 (scratchWordsMem mem [a, b, c]) 224 32 =
              scratchWordsMem mem [a, b, c, d] := scratchWordsMem_write hmem [a, b, c] d
          rw [hb, hcwrite, hd] at rd6
          have hret := (scratchWordsMem_read128 hmem [a, b, c, d]
            (by change 0 < 4; decide) (by change 128 < 2 ^ 64; decide)) ▸ rd6
          simpa only [liquidatorWord, liquidatorSlot, liquidatorScalars, liquidatorScalar,
            List.map_cons, List.map_nil, addressWord_eq_ofNat_address hc]
            using hret
        · simp only [AddressGetterResult, hc, and_false, if_false]
          exact cometValidateAddress_bad (v := v) (by change 6 ≤ 1024; decide) hc rd4
      · simp only [AddressGetterResult, hhi, false_and, and_false, if_false]
        have rd3 := cometWithExtendedAssetList_block_5679_taken
          (immWords := wordsOf (immStore v)) (by decide)
          (calldataLength_huge (need := 32) (by decide) (by omega) hsize)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
        exact cometRevert1410 (by decide) rd3
    · simp only [AddressGetterResult, hlo, false_and, and_false, if_false]
      have rd3 := cometWithExtendedAssetList_block_5679_taken
        (immWords := wordsOf (immStore v)) (by decide)
        (calldataLength_short (need := 32) (by decide) hsz (by omega) hsize)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact cometRevert1410 (by decide) rd3
  · simp only [AddressGetterResult, hv, false_and, if_false]
    have rd2 := cometWithExtendedAssetList_block_5672_taken
      (immWords := wordsOf (immStore v)) (by decide) hv
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact cometRevert1410 (by decide) rd2

/-- `liquidatorPoints(address)`: the theorem `Correct.lean` routes selector 56 to. -/
theorem cometWithExtendedAssetListLiquidatorPointsBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 56)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 56) rfl hsel
  let w := liquidatorWord σ I (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
  apply addressGetterValues_refines (t := liquidatorPointsTransition)
    (values := (liquidatorScalars w).map ScalarReturn.value) hcode hsz
    (cometSelectorDispatch ⟨56, by decide⟩ hsel) rfl rfl ?_ ?_
    (liquidatorPointsX v hcode hsz hsize hsel)
  · exact .returned rfl (scalarReturnsEncoding (liquidatorScalars w))
  · intro hv hhi _
    exact liquidatorPoints_returns (immStore v) hv hhi

end Benchmarks.CompoundIII.Comet
