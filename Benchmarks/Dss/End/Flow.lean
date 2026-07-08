import Benchmarks.Dss.End.Cash
import Benchmarks.Dss.End.Trusted
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.End

set_option maxRecDepth 2000000

attribute [local simp]
  wardsSelectorBytes vatSelectorBytes catSelectorBytes dogSelectorBytes vowSelectorBytes
  potSelectorBytes spotSelectorBytes cureSelectorBytes liveSelectorBytes whenSelectorBytes
  waitSelectorBytes debtSelectorBytes tagSelectorBytes gapSelectorBytes ArtSelectorBytes
  fixSelectorBytes bagSelectorBytes outSelectorBytes relySelectorBytes denySelectorBytes
  fileAddressSelectorBytes fileUintSelectorBytes cageSelectorBytes cageIlkSelectorBytes
  snipSelectorBytes skipSelectorBytes skimSelectorBytes freeSelectorBytes thawSelectorBytes
  flowSelectorBytes packSelectorBytes cashSelectorBytes

abbrev flowIlkWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev flowStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "ilk" (.fixedBytes bytes32Width (EVM.Word.toBytesBE (flowIlkWord I)))

abbrev flowDebtWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord ⟨11⟩ σ I

abbrev flowVatWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord ⟨1⟩ σ I

def flowVatMaskedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (flowVatWord σ I) solcAddrMask

abbrev flowIlkValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (EVM.Word.toBytesBE (flowIlkWord I))

abbrev flowIlkKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (EVM.Word.toBytesBE (flowIlkWord I))

abbrev flowVatIlksSelectorWord : UInt256 := ⟨0xd9638d36⟩
abbrev flowVatIlksSelectorShifted : UInt256 := UInt256.shiftLeft ⟨0x6cb1c69b⟩ ⟨225⟩
abbrev flowVatIlksOutPtr : UInt256 := ⟨128⟩
abbrev flowVatIlksInSize : UInt256 := ⟨36⟩
abbrev flowVatIlksOutSize : UInt256 := ⟨160⟩
abbrev flowVatIlksEndPtr : UInt256 := ⟨164⟩

noncomputable def flowVatIlksSelectorMem (mem : ByteArray) : ByteArray :=
  flowVatIlksSelectorShifted.toByteArray.write 0 mem flowVatIlksOutPtr.toNat 32

noncomputable def flowVatIlksCalldataMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (flowIlkWord I).toByteArray.write 0 (flowVatIlksSelectorMem mem) 132 32

noncomputable def flowVatIlksPostCallMem (I : ExecutionEnv) (base out : ByteArray) : ByteArray :=
  out.write 0 (flowVatIlksCalldataMem I base) flowVatIlksOutPtr.toNat
    (min flowVatIlksOutSize (UInt256.ofNat out.size)).toNat

noncomputable def flowVatIlksWord0 (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

noncomputable def flowVatIlksRateWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 32 64))

noncomputable def flowVatIlksWord2 (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 64 96))

noncomputable def flowVatIlksWord3 (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 96 128))

noncomputable def flowVatIlksWord4 (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 128 160))

noncomputable abbrev flowVatIlksReturnValues (out : ByteArray) : List Value :=
  [ .int (Int.ofNat (flowVatIlksWord0 out).toNat),
    .int (Int.ofNat (flowVatIlksRateWord out).toNat),
    .int (Int.ofNat (flowVatIlksWord2 out).toNat),
    .int (Int.ofNat (flowVatIlksWord3 out).toNat),
    .int (Int.ofNat (flowVatIlksWord4 out).toNat) ]

def flowFixStorageSlot (I : ExecutionEnv) : UInt256 :=
  fixSlot (flowIlkKey I)

def flowFixWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (flowFixStorageSlot I) σ I

def flowArtStorageSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨14⟩ (flowIlkWord I)

def flowArtWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (flowArtStorageSlot I) σ I

def flowTagStorageSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨12⟩ (flowIlkWord I)

def flowTagWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (flowTagStorageSlot I) σ I

def flowGapStorageSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨13⟩ (flowIlkWord I)

def flowGapWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (flowGapStorageSlot I) σ I

theorem flowArtStorageSlot_eq (I : ExecutionEnv) :
    flowArtStorageSlot I = ArtSlot (flowIlkKey I) := by
  unfold flowArtStorageSlot ArtSlot mapSlot solcMappingSlot flowIlkKey flowIlkWord
  unfold bytes32Width
  rw [keyValueToWord_fixedBytes32]

theorem flowTagStorageSlot_eq (I : ExecutionEnv) :
    flowTagStorageSlot I = tagSlot (flowIlkKey I) := by
  unfold flowTagStorageSlot tagSlot mapSlot solcMappingSlot flowIlkKey flowIlkWord
  unfold bytes32Width
  rw [keyValueToWord_fixedBytes32]

theorem flowGapStorageSlot_eq (I : ExecutionEnv) :
    flowGapStorageSlot I = gapSlot (flowIlkKey I) := by
  unfold flowGapStorageSlot gapSlot mapSlot solcMappingSlot flowIlkKey flowIlkWord
  unfold bytes32Width
  rw [keyValueToWord_fixedBytes32]

abbrev flowRayWord : UInt256 :=
  ⟨1000000000000000000000000000⟩

noncomputable abbrev flowDenWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.div (flowDebtWord σ I) flowRayWord

noncomputable abbrev flowWad0MulWord (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) : UInt256 :=
  UInt256.mul (flowArtWord σ I) (flowVatIlksRateWord out)

noncomputable abbrev flowWad0Word (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) : UInt256 :=
  UInt256.div (flowWad0MulWord σ I out) flowRayWord

noncomputable abbrev flowWadMulWord (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) : UInt256 :=
  UInt256.mul (flowWad0Word σ I out) (flowTagWord σ I)

noncomputable abbrev flowWadWord (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) : UInt256 :=
  UInt256.div (flowWadMulWord σ I out) flowRayWord

noncomputable abbrev flowNum0Word (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) : UInt256 :=
  UInt256.sub (flowWadWord σ I out) (flowGapWord σ I)

noncomputable abbrev flowNumWord (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) : UInt256 :=
  UInt256.mul (flowNum0Word σ I out) flowRayWord

noncomputable abbrev flowFixVWord (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) : UInt256 :=
  UInt256.div (flowNumWord σ I out) (flowDenWord σ I)

noncomputable abbrev flowVatIlksLocals (I : ExecutionEnv) (out : ByteArray) : Store :=
  (flowStore I).insert "vatIlk" (collapseReturns (flowVatIlksReturnValues out))

noncomputable abbrev flowRateLocals (I : ExecutionEnv) (out : ByteArray) : Store :=
  (flowVatIlksLocals I out).insert "rate"
    (.int (Int.ofNat (flowVatIlksRateWord out).toNat))

noncomputable abbrev flowWad0Locals (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) : Store :=
  (flowRateLocals I out).insert "wad0" (.int (Int.ofNat (flowWad0Word σ I out).toNat))

noncomputable abbrev flowWadLocals (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) : Store :=
  (flowWad0Locals σ I out).insert "wad" (.int (Int.ofNat (flowWadWord σ I out).toNat))

noncomputable abbrev flowNum0Locals (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) : Store :=
  (flowWadLocals σ I out).insert "num0" (.int (Int.ofNat (flowNum0Word σ I out).toNat))

noncomputable abbrev flowNumLocals (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) : Store :=
  (flowNum0Locals σ I out).insert "num" (.int (Int.ofNat (flowNumWord σ I out).toNat))

noncomputable abbrev flowDenLocals (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) : Store :=
  (flowNumLocals σ I out).insert "den" (.int (Int.ofNat (flowDenWord σ I).toNat))

noncomputable abbrev flowFixVLocals (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) : Store :=
  (flowDenLocals σ I out).insert "fixV" (.int (Int.ofNat (flowFixVWord σ I out).toNat))

theorem flowFixStorageSlot_eq (I : ExecutionEnv) :
    flowFixStorageSlot I = solcMappingSlot ⟨15⟩ (flowIlkWord I) := by
  unfold flowFixStorageSlot fixSlot mapSlot solcMappingSlot flowIlkKey flowIlkWord
  unfold bytes32Width
  rw [keyValueToWord_fixedBytes32]

theorem flow_mul_div_right_cancel {x y : UInt256}
    (hfit : x.toNat * y.toNat < UInt256.size) (hy : y ≠ ⟨0⟩) :
    UInt256.div (UInt256.mul x y) y = x := by
  apply u256_inj
  rw [udiv_toNat, u256_mul_toNat, Nat.mod_eq_of_lt hfit]
  have hyNat : y.toNat ≠ 0 := by
    intro hzero
    exact hy (uint256_toNat_eq_zero hzero)
  rw [Nat.mul_comm x.toNat y.toNat]
  exact Nat.mul_div_right _ (Nat.pos_of_ne_zero hyNat)

theorem flow_udiv_mul_wrap_ne_of_overflow {a b : UInt256}
    (hover : UInt256.size ≤ a.toNat * b.toNat) :
    UInt256.div (UInt256.mul a b) b ≠ a := by
  intro hbad
  have hnat := congrArg UInt256.toNat hbad
  rw [udiv_toNat, u256_mul_toNat] at hnat
  have hle : a.toNat * b.toNat ≤ (UInt256.mul a b).toNat := by
    exact Nat.mul_le_of_le_div b.toNat a.toNat (UInt256.mul a b).toNat
      (by exact le_of_eq hnat.symm)
  have hlt : (UInt256.mul a b).toNat < UInt256.size := (UInt256.mul a b).val.isLt
  exact (not_lt_of_ge (le_trans hover hle)) hlt

theorem evalExpr_flowFixStorage {evm : EVM.State} {locals : Store}
    (hbaseAbsent : "fix" ∉ locals)
    (hget : locals["ilk"]? = some (flowIlkValue evm.executionEnv)) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (fixRef (.var "ilk"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (flowFixStorageSlot evm.executionEnv)).toNat)) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := fixRef (.var "ilk"))
    (er := ({ base := "fix", steps := [.mindex (flowIlkKey evm.executionEnv)] } :
      EvaledStorageRef))
    (t := .int uint256Int)
    (loc := wordLoc (flowFixStorageSlot evm.executionEnv))
    (value := .int (Int.ofNat
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (flowFixStorageSlot evm.executionEnv)).toNat))
    (hbase := by simpa [fixRef] using hbaseAbsent)
    (her := by
      have hlen :
          (EVM.Word.toBytesBE (flowIlkWord evm.executionEnv)).length = bytes32Width.val + 1 := by
        simpa [bytes32Width] using word_toBytesBE_toByteArray_size (flowIlkWord evm.executionEnv)
      simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, fixRef, flowIlkValue,
        flowIlkKey, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, valueToKey?,
        hget, hlen])
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, flowIlkKey, uint256St])
    (hloc := by rfl)
    (hload := by
      simpa [wordLoc, uint256Loc, uint256Int] using
        storageLocLoad_uint256 evm (flowFixStorageSlot evm.executionEnv))]

theorem evalExpr_flowVatStorage (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "vat" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat)) := by
  rw [evalExpr_storage_scalar (er := ({ base := "vat", steps := [] } : EvaledStorageRef))
    (t := .address) (loc := addrLoc ⟨1⟩)]
  · exact congrArg EvalResult.ok (endStorageLocLoad_address_offset0 _ ⟨1⟩)
  · exact hbase
  · simp [vatRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  · simp [storageTypeAt?, contract, storageDecls, addrSt]
  · funext evm
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw]

theorem evalExpr_flowVatCodeGuard_false {evm : EVM.State} {locals : Store}
    {target : AccountAddress}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address target))
    (hcode :
      (UInt256.ofNat ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem evalExpr_flowVatCodeGuard_true {evm : EVM.State} {locals : Store}
    {target : AccountAddress}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address target))
    (hcode :
      (UInt256.ofNat ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat ≠
        0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat]
  exact Nat.pos_of_ne_zero hcode

theorem evalExpr_flowVatIlksRate {evm : EVM.State} {I : ExecutionEnv} {out : ByteArray} :
    evalExpr? config { contract := contract, locals := flowVatIlksLocals I out } evm
      (.tupleGet (.var "vatIlk") 1) =
        .ok (.int (Int.ofNat (flowVatIlksRateWord out).toNat)) := by
  simp [evalExpr?, EvalResult.bind, bind, EvalResult.ofOption, flowVatIlksLocals,
    collapseReturns, tupleGetValue?]

theorem assign_flowFixStorage (evm : EVM.State) {locals : Store}
    (fixV : UInt256)
    (hbaseAbsent : "fix" ∉ locals)
    (hget : locals["ilk"]? = some (flowIlkValue evm.executionEnv)) :
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (fixRef (.var "ilk")) (.int (Int.ofNat fixV.toNat)) =
        .ok ({ contract := contract, locals := locals },
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (flowFixStorageSlot evm.executionEnv) fixV) := by
  exact assignStorageRef_storage_scalar
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (flowFixStorageSlot evm.executionEnv) fixV)
    (slot := fixRef (.var "ilk"))
    (er := ({ base := "fix", steps := [.mindex (flowIlkKey evm.executionEnv)] } :
      EvaledStorageRef))
    (ty := .elem (.int uint256Int))
    (loc := wordLoc (flowFixStorageSlot evm.executionEnv))
    (n := Int.ofNat fixV.toNat)
    (by simpa [fixRef] using hbaseAbsent)
    (by
      have hlen :
          (EVM.Word.toBytesBE (flowIlkWord evm.executionEnv)).length = bytes32Width.val + 1 := by
        simpa [bytes32Width] using word_toBytesBE_toByteArray_size (flowIlkWord evm.executionEnv)
      simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, fixRef, flowIlkValue,
        flowIlkKey, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, valueToKey?,
        hget, hlen])
    (by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, flowIlkKey, uint256St])
    (by rfl)
    (storageLocStore_uint256 evm (flowFixStorageSlot evm.executionEnv) fixV)

theorem evalExpr_flowArtStorage {evm : EVM.State} {locals : Store}
    (hbaseAbsent : "Art" ∉ locals)
    (hget : locals["ilk"]? = some (flowIlkValue evm.executionEnv)) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (ArtRef (.var "ilk"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (flowArtStorageSlot evm.executionEnv)).toNat)) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := ArtRef (.var "ilk"))
    (er := ({ base := "Art", steps := [.mindex (flowIlkKey evm.executionEnv)] } :
      EvaledStorageRef))
    (t := .int uint256Int)
    (loc := wordLoc (flowArtStorageSlot evm.executionEnv))
    (value := .int (Int.ofNat
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (flowArtStorageSlot evm.executionEnv)).toNat))
    (hbase := by simpa [ArtRef] using hbaseAbsent)
    (her := by
      have hlen :
          (EVM.Word.toBytesBE (flowIlkWord evm.executionEnv)).length = bytes32Width.val + 1 := by
        simpa [bytes32Width] using word_toBytesBE_toByteArray_size (flowIlkWord evm.executionEnv)
      simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, ArtRef, flowIlkValue,
        flowIlkKey, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, valueToKey?,
        hget, hlen])
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, flowIlkKey, uint256St])
    (hloc := by
      funext x
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        flowArtStorageSlot_eq])
    (hload := by
      simpa [wordLoc, uint256Loc, uint256Int] using
        storageLocLoad_uint256 evm (flowArtStorageSlot evm.executionEnv))]

theorem evalExpr_flowTagStorage {evm : EVM.State} {locals : Store}
    (hbaseAbsent : "tag" ∉ locals)
    (hget : locals["ilk"]? = some (flowIlkValue evm.executionEnv)) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (tagRef (.var "ilk"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (flowTagStorageSlot evm.executionEnv)).toNat)) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := tagRef (.var "ilk"))
    (er := ({ base := "tag", steps := [.mindex (flowIlkKey evm.executionEnv)] } :
      EvaledStorageRef))
    (t := .int uint256Int)
    (loc := wordLoc (flowTagStorageSlot evm.executionEnv))
    (value := .int (Int.ofNat
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (flowTagStorageSlot evm.executionEnv)).toNat))
    (hbase := by simpa [tagRef] using hbaseAbsent)
    (her := by
      have hlen :
          (EVM.Word.toBytesBE (flowIlkWord evm.executionEnv)).length = bytes32Width.val + 1 := by
        simpa [bytes32Width] using word_toBytesBE_toByteArray_size (flowIlkWord evm.executionEnv)
      simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, tagRef, flowIlkValue,
        flowIlkKey, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, valueToKey?,
        hget, hlen])
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, flowIlkKey, uint256St])
    (hloc := by
      funext x
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        flowTagStorageSlot_eq])
    (hload := by
      simpa [wordLoc, uint256Loc, uint256Int] using
        storageLocLoad_uint256 evm (flowTagStorageSlot evm.executionEnv))]

theorem evalExpr_flowGapStorage {evm : EVM.State} {locals : Store}
    (hbaseAbsent : "gap" ∉ locals)
    (hget : locals["ilk"]? = some (flowIlkValue evm.executionEnv)) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (gapRef (.var "ilk"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (flowGapStorageSlot evm.executionEnv)).toNat)) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := gapRef (.var "ilk"))
    (er := ({ base := "gap", steps := [.mindex (flowIlkKey evm.executionEnv)] } :
      EvaledStorageRef))
    (t := .int uint256Int)
    (loc := wordLoc (flowGapStorageSlot evm.executionEnv))
    (value := .int (Int.ofNat
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (flowGapStorageSlot evm.executionEnv)).toNat))
    (hbase := by simpa [gapRef] using hbaseAbsent)
    (her := by
      have hlen :
          (EVM.Word.toBytesBE (flowIlkWord evm.executionEnv)).length = bytes32Width.val + 1 := by
        simpa [bytes32Width] using word_toBytesBE_toByteArray_size (flowIlkWord evm.executionEnv)
      simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, gapRef, flowIlkValue,
        flowIlkKey, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, valueToKey?,
        hget, hlen])
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, flowIlkKey, uint256St])
    (hloc := by
      funext x
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        flowGapStorageSlot_eq])
    (hload := by
      simpa [wordLoc, uint256Loc, uint256Int] using
        storageLocLoad_uint256 evm (flowGapStorageSlot evm.executionEnv))]

theorem flowVatIlksDecode_none_short {out : ByteArray} (hshort : out.size < 160) :
    config.externalABI.decode? "vatIlks" out = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  change ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
    [uint256, uint256, uint256, uint256, uint256] out = none
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq
    (types := [uint256, uint256, uint256, uint256, uint256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [uint256, uint256, uint256, uint256, uint256]) (bytes := out.toList)
    (cursor := 0) (total := 32 * [uint256, uint256, uint256, uint256, uint256].length)
    (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  by_cases h0 : 32 ≤ out.size
  · have htake0 : ((out.toList.drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, hlen]
      omega
    have hscalar0 : decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 0 =
        some (.int (Int.ofNat (ABI.bytesToWord ((out.toList.drop 0).take 32)).toNat), 0 + 32) := by
      simpa [uint256, uint256Int] using
        decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
          (bytes := out.toList) (start := 0) htake0
    rw [hscalar0]
    by_cases h1 : 64 ≤ out.size
    · have htake32 : ((out.toList.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop, hlen]
        omega
      have hscalar32 :
          decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 32 =
            some (.int (Int.ofNat (ABI.bytesToWord ((out.toList.drop 32).take 32)).toNat),
              32 + 32) := by
        simpa [uint256, uint256Int] using
          decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
            (bytes := out.toList) (start := 32) htake32
      rw [hscalar32]
      by_cases h2 : 96 ≤ out.size
      · have htake64 : ((out.toList.drop 64).take 32).length = 32 := by
          rw [List.length_take, List.length_drop, hlen]
          omega
        have hscalar64 :
            decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 64 =
              some (.int (Int.ofNat (ABI.bytesToWord ((out.toList.drop 64).take 32)).toNat),
                64 + 32) := by
          simpa [uint256, uint256Int] using
            decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
              (bytes := out.toList) (start := 64) htake64
        rw [hscalar64]
        by_cases h3 : 128 ≤ out.size
        · have htake96 : ((out.toList.drop 96).take 32).length = 32 := by
            rw [List.length_take, List.length_drop, hlen]
            omega
          have hscalar96 :
              decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 96 =
                some (.int (Int.ofNat (ABI.bytesToWord ((out.toList.drop 96).take 32)).toNat),
                  96 + 32) := by
            simpa [uint256, uint256Int] using
              decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
                (bytes := out.toList) (start := 96) htake96
          rw [hscalar96]
          have htake128n : ¬ ((out.toList.drop 128).take 32).length = 32 := by
            rw [List.length_take, List.length_drop, hlen]
            omega
          have hscalar128 :
              decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 128 = none := by
            simpa [uint256, uint256Int] using
              decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
                (bytes := out.toList) (start := 128) htake128n
          rw [hscalar128]
          simp
        · have htake96n : ¬ ((out.toList.drop 96).take 32).length = 32 := by
            rw [List.length_take, List.length_drop, hlen]
            omega
          have hscalar96 :
              decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 96 = none := by
            simpa [uint256, uint256Int] using
              decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
                (bytes := out.toList) (start := 96) htake96n
          rw [hscalar96]
          simp
      · have htake64n : ¬ ((out.toList.drop 64).take 32).length = 32 := by
          rw [List.length_take, List.length_drop, hlen]
          omega
        have hscalar64 :
            decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 64 = none := by
          simpa [uint256, uint256Int] using
            decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
              (bytes := out.toList) (start := 64) htake64n
        rw [hscalar64]
        simp
    · have htake32n : ¬ ((out.toList.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop, hlen]
        omega
      have hscalar32 :
          decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 32 = none := by
        simpa [uint256, uint256Int] using
          decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
            (bytes := out.toList) (start := 32) htake32n
      rw [hscalar32]
      simp
  · have htake0n : ¬ ((out.toList.drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, hlen]
      omega
    have hscalar0 : decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 0 =
        none := by
      simpa [uint256, uint256Int] using
        decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
          (bytes := out.toList) (start := 0) htake0n
    rw [hscalar0]
    simp

theorem flowVatIlksBytesToWord0_eq (out : ByteArray) (hlong : 160 ≤ out.size) :
    ABI.bytesToWord ((out.toList.drop 0).take 32) = flowVatIlksWord0 out := by
  rw [decode_word_at_eq_any out 0 (by omega), uInt256OfByteArray_eq]
  unfold flowVatIlksWord0 fromByteArrayBigEndian
  congr 1
  rw [byteArray_toList_eq (out.readBytes 0 32), readBytes_at_toList_any out 0 (by omega)]
  rw [byteArray_toList_eq (out.extract 0 32)]
  simp [ByteArray.data_extract, Array.toList_extract]

theorem flowVatIlksBytesToWord32_eq (out : ByteArray) (hlong : 160 ≤ out.size) :
    ABI.bytesToWord ((out.toList.drop 32).take 32) = flowVatIlksRateWord out := by
  rw [decode_word_at_eq_any out 32 (by omega), uInt256OfByteArray_eq]
  unfold flowVatIlksRateWord fromByteArrayBigEndian
  congr 1
  rw [byteArray_toList_eq (out.readBytes 32 32), readBytes_at_toList_any out 32 (by omega)]
  rw [byteArray_toList_eq (out.extract 32 64)]
  simp [ByteArray.data_extract, Array.toList_extract]

theorem flowVatIlksBytesToWord64_eq (out : ByteArray) (hlong : 160 ≤ out.size) :
    ABI.bytesToWord ((out.toList.drop 64).take 32) = flowVatIlksWord2 out := by
  rw [decode_word_at_eq_any out 64 (by omega), uInt256OfByteArray_eq]
  unfold flowVatIlksWord2 fromByteArrayBigEndian
  congr 1
  rw [byteArray_toList_eq (out.readBytes 64 32), readBytes_at_toList_any out 64 (by omega)]
  rw [byteArray_toList_eq (out.extract 64 96)]
  simp [ByteArray.data_extract, Array.toList_extract]

theorem flowVatIlksBytesToWord96_eq (out : ByteArray) (hlong : 160 ≤ out.size) :
    ABI.bytesToWord ((out.toList.drop 96).take 32) = flowVatIlksWord3 out := by
  rw [decode_word_at_eq_any out 96 (by omega), uInt256OfByteArray_eq]
  unfold flowVatIlksWord3 fromByteArrayBigEndian
  congr 1
  rw [byteArray_toList_eq (out.readBytes 96 32), readBytes_at_toList_any out 96 (by omega)]
  rw [byteArray_toList_eq (out.extract 96 128)]
  simp [ByteArray.data_extract, Array.toList_extract]

set_option maxHeartbeats 800000 in
theorem flowVatIlksBytesToWord128_eq (out : ByteArray) (hlong : 160 ≤ out.size) :
    ABI.bytesToWord ((out.toList.drop 128).take 32) = flowVatIlksWord4 out := by
  rw [decode_word_at_eq_any out 128 (by omega), uInt256OfByteArray_eq]
  unfold flowVatIlksWord4 fromByteArrayBigEndian
  congr 1
  rw [byteArray_toList_eq (out.readBytes 128 32), readBytes_at_toList_any out 128 (by omega)]
  rw [byteArray_toList_eq (out.extract 128 160)]
  simp [ByteArray.data_extract, Array.toList_extract]

theorem flowVatIlksDecode_ok {out : ByteArray} (hlong : 160 ≤ out.size) :
    config.externalABI.decode? "vatIlks" out = some (flowVatIlksReturnValues out) := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  change ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
    [uint256, uint256, uint256, uint256, uint256] out = some (flowVatIlksReturnValues out)
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq
    (types := [uint256, uint256, uint256, uint256, uint256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [uint256, uint256, uint256, uint256, uint256]) (bytes := out.toList)
    (cursor := 0) (total := 32 * [uint256, uint256, uint256, uint256, uint256].length)
    (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  have htake0 : ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have htake32 : ((out.toList.drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have htake64 : ((out.toList.drop 64).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have htake96 : ((out.toList.drop 96).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have htake128 : ((out.toList.drop 128).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have hscalar0 : decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 0 =
      some (.int (Int.ofNat (ABI.bytesToWord ((out.toList.drop 0).take 32)).toNat), 0 + 32) := by
    simpa [uint256, uint256Int] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 0) htake0
  have hscalar32 : decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 32 =
      some (.int (Int.ofNat (ABI.bytesToWord ((out.toList.drop 32).take 32)).toNat),
        32 + 32) := by
    simpa [uint256, uint256Int] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 32) htake32
  have hscalar64 : decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 64 =
      some (.int (Int.ofNat (ABI.bytesToWord ((out.toList.drop 64).take 32)).toNat),
        64 + 32) := by
    simpa [uint256, uint256Int] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 64) htake64
  have hscalar96 : decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 96 =
      some (.int (Int.ofNat (ABI.bytesToWord ((out.toList.drop 96).take 32)).toNat),
        96 + 32) := by
    simpa [uint256, uint256Int] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 96) htake96
  have hscalar128 : decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 128 =
      some (.int (Int.ofNat (ABI.bytesToWord ((out.toList.drop 128).take 32)).toNat),
        128 + 32) := by
    simpa [uint256, uint256Int] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 128) htake128
  rw [hscalar0, hscalar32, hscalar64, hscalar96, hscalar128]
  rw [flowVatIlksBytesToWord0_eq out hlong, flowVatIlksBytesToWord32_eq out hlong,
    flowVatIlksBytesToWord64_eq out hlong, flowVatIlksBytesToWord96_eq out hlong,
    flowVatIlksBytesToWord128_eq out hlong]
  rfl

theorem flowVatIlksSelectorMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (flowVatIlksSelectorMem mem).size = 160 := by
  unfold flowVatIlksSelectorMem flowVatIlksOutPtr
  exact toByteArray_write32_size_of_ge mem flowVatIlksSelectorShifted 128 96 160 hmem
    (by native_decide) (by native_decide) (by native_decide)

theorem flowVatIlksCalldataMem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (flowVatIlksCalldataMem I mem).size = 164 := by
  unfold flowVatIlksCalldataMem
  exact toByteArray_write32_size_of_le (flowVatIlksSelectorMem mem) (flowIlkWord I) 132
    160 164 (flowVatIlksSelectorMem_size hmem)
    (by rw [flowVatIlksSelectorMem_size hmem]; native_decide) (by native_decide)

theorem flowVatIlksSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (flowVatIlksSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold flowVatIlksSelectorMem flowVatIlksOutPtr
  change (flowVatIlksSelectorShifted.toByteArray.write 0 mem 128 32).readWithPadding 64 32 =
    UInt256.toByteArray ⟨128⟩
  rw [toByteArray_write_read_below_of_gap flowVatIlksSelectorShifted mem 128 64
    (by rw [hmem]) (by omega) (by rw [hmem]; native_decide), hread64]

theorem flowVatIlksCalldataMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (flowVatIlksCalldataMem I mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold flowVatIlksCalldataMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [flowVatIlksSelectorMem_size hmem]; omega) (by omega),
    flowVatIlksSelectorMem_read64 hmem hread64]

theorem flowVatIlksCalldataMem_read128_4 (I : ExecutionEnv)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (flowVatIlksCalldataMem I mem).readWithPadding 128 4 = ilksSelector := by
  have hSelectorSize := flowVatIlksSelectorMem_size hmem
  unfold flowVatIlksCalldataMem
  rw [toByteArray_write_read_below_len_of_gap (flowIlkWord I)
      (flowVatIlksSelectorMem mem) 132 128 4
      (by rw [hSelectorSize]; omega)
      (by omega) (by omega) (by omega)
      (by rw [hSelectorSize]; native_decide)]
  unfold flowVatIlksSelectorMem
  change (flowVatIlksSelectorShifted.toByteArray.write 0 mem 128 32).readWithPadding 128 4 =
    ilksSelector
  rw [toByteArray_write_read_window_of_gap flowVatIlksSelectorShifted mem 128 0 4
      (by omega) (by omega) (by omega)
      (by rw [hmem]; native_decide)]
  native_decide

theorem flowVatIlksCalldataMem_read132_32 (I : ExecutionEnv)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (flowVatIlksCalldataMem I mem).readWithPadding 132 32 =
      (flowIlkWord I).toByteArray := by
  unfold flowVatIlksCalldataMem
  rw [toByteArray_write_read_back_of_gap (flowIlkWord I) (flowVatIlksSelectorMem mem) 132
      (by rw [flowVatIlksSelectorMem_size hmem]; native_decide)]

theorem flowVatIlksCalldataMem_read128_36 (I : ExecutionEnv)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (flowVatIlksCalldataMem I mem).readWithPadding 128 36 =
      ilksSelector ++ (flowIlkWord I).toByteArray := by
  have hsize : (flowVatIlksCalldataMem I mem).size = 164 :=
    flowVatIlksCalldataMem_size I hmem
  rw [show 36 = 4 + 32 from rfl,
    byteArray_readWithPadding_split (flowVatIlksCalldataMem I mem) 128 4 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [flowVatIlksCalldataMem_read128_4 I hmem, flowVatIlksCalldataMem_read132_32 I hmem]

theorem flowVatIlksEncodeWords (I : ExecutionEnv) :
    config.externalABI.encode? "vatIlks" [flowIlkValue I] =
      some (ilksSelector ++ (flowIlkWord I).toByteArray) := by
  have hIlk : ABI.encodeABIValue? bytes32 (flowIlkValue I) =
      some (EVM.Word.toBytesBE (flowIlkWord I)) := by
    have hlen : (EVM.Word.toBytesBE (flowIlkWord I)).length = 32 := by
      simpa using word_toBytesBE_toByteArray_size (flowIlkWord I)
    simp [ABI.encodeABIValue?, hlen, zeroBytes, flowIlkValue, bytes32, bytes32Width]
  have hIlk' : ABI.encodeABIValue? (.elem (.bytes bytes32Width)) (flowIlkValue I) =
      some (EVM.Word.toBytesBE (flowIlkWord I)) := by
    simpa [bytes32] using hIlk
  simp [config, externalABI, ilksEncode?, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    ABI.encodeABIValuesFrom?, hIlk', bytes32]
  apply ByteArray.ext
  simp [word_toBytesBE_toByteArray_eq_toByteArray]

theorem flowVatIlksEncode_eq (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 96) :
    config.externalABI.encode? "vatIlks" [flowIlkValue I] =
      some ((flowVatIlksCalldataMem I mem).readWithPadding
        flowVatIlksOutPtr.toNat flowVatIlksInSize.toNat) := by
  rw [show flowVatIlksOutPtr.toNat = 128 by native_decide,
    show flowVatIlksInSize.toNat = 36 by native_decide]
  rw [flowVatIlksCalldataMem_read128_36 I hmem]
  exact flowVatIlksEncodeWords I

theorem flowVatIlksPostCallMem_size_gt64 (I : ExecutionEnv) (base out : ByteArray)
    (hbase : base.size = 96) (hshort : out.size < 160) (hout : out.size < UInt256.size) :
    64 < (flowVatIlksPostCallMem I base out).size := by
  have hmin :
      (min flowVatIlksOutSize (UInt256.ofNat out.size)).toNat = out.size := by
    exact umin_ofNat_right_toNat_of_lt (c := 160) (n := out.size) (by decide) hshort hout
  unfold flowVatIlksPostCallMem
  rw [hmin]
  by_cases hzero : out.size = 0
  · rw [hzero, byteArray_write_len_zero, flowVatIlksCalldataMem_size I hbase]
    omega
  · change 64 < (out.write 0 (flowVatIlksCalldataMem I base) 128 out.size).size
    by_cases hfit : 128 + out.size ≤ (flowVatIlksCalldataMem I base).size
    · rw [write_eq_gen out (flowVatIlksCalldataMem I base) 128 out.size hzero
        le_rfl hfit,
        ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract,
        flowVatIlksCalldataMem_size I hbase]
      omega
    · rw [write_eq_gen_extend out (flowVatIlksCalldataMem I base) 128 out.size hzero
        le_rfl (by rw [flowVatIlksCalldataMem_size I hbase]; omega) (by omega),
        ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
        flowVatIlksCalldataMem_size I hbase]
      omega

theorem flowVatIlksPostCallMem_read64 (I : ExecutionEnv) (base out : ByteArray)
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hshort : out.size < 160) (hout : out.size < UInt256.size) :
    (flowVatIlksPostCallMem I base out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hmin :
      (min flowVatIlksOutSize (UInt256.ofNat out.size)).toNat = out.size := by
    exact umin_ofNat_right_toNat_of_lt (c := 160) (n := out.size) (by decide) hshort hout
  unfold flowVatIlksPostCallMem
  rw [hmin]
  by_cases hzero : out.size = 0
  · rw [hzero, byteArray_write_len_zero]
    exact flowVatIlksCalldataMem_read64 I hbase hread64
  · change (out.write 0 (flowVatIlksCalldataMem I base) 128 out.size).readWithPadding
      64 32 = UInt256.toByteArray ⟨128⟩
    rw [write_read_below_gen_extend out (flowVatIlksCalldataMem I base) 128 out.size
      64 hzero le_rfl
      (by rw [flowVatIlksCalldataMem_size I hbase]; omega) (by omega)]
    exact flowVatIlksCalldataMem_read64 I hbase hread64

theorem flowVatIlksPostCallMem_mload64 (I : ExecutionEnv) (base out : ByteArray)
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hshort : out.size < 160) (hout : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (flowVatIlksPostCallMem I base out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((flowVatIlksPostCallMem I base out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by
      have hgt := flowVatIlksPostCallMem_size_gt64 I base out hbase hshort hout
      omega)
    (by decide)
    (flowVatIlksPostCallMem_read64 I base out hbase hread64 hshort hout)

theorem flowVatIlksPostCallMem_size_long (I : ExecutionEnv) (base out : ByteArray)
    (hbase : base.size = 96) (hlong : 160 ≤ out.size) (hout : out.size < UInt256.size) :
    (flowVatIlksPostCallMem I base out).size = 288 := by
  have hmin :
      (min flowVatIlksOutSize (UInt256.ofNat out.size)).toNat = 160 := by
    exact umin_ofNat_right_toNat_of_ge (c := 160) (n := out.size) (by decide) hlong hout
  unfold flowVatIlksPostCallMem
  rw [hmin]
  change (out.write 0 (flowVatIlksCalldataMem I base) 128 160).size = 288
  rw [write_eq_gen_extend out (flowVatIlksCalldataMem I base) 128 160
    (by omega) (by omega)
    (by rw [flowVatIlksCalldataMem_size I hbase]; omega)
    (by rw [flowVatIlksCalldataMem_size I hbase]; omega)]
  rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    flowVatIlksCalldataMem_size I hbase]
  omega

theorem flowVatIlksPostCallMem_read64_long (I : ExecutionEnv) (base out : ByteArray)
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlong : 160 ≤ out.size) (hout : out.size < UInt256.size) :
    (flowVatIlksPostCallMem I base out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hmin :
      (min flowVatIlksOutSize (UInt256.ofNat out.size)).toNat = 160 := by
    exact umin_ofNat_right_toNat_of_ge (c := 160) (n := out.size) (by decide) hlong hout
  unfold flowVatIlksPostCallMem
  rw [hmin]
  change (out.write 0 (flowVatIlksCalldataMem I base) 128 160).readWithPadding 64 32 =
    UInt256.toByteArray ⟨128⟩
  rw [write_read_below_gen_extend out (flowVatIlksCalldataMem I base) 128 160
    64 (by omega) (by omega)
    (by rw [flowVatIlksCalldataMem_size I hbase]; omega) (by omega)]
  exact flowVatIlksCalldataMem_read64 I hbase hread64

theorem flowVatIlksPostCallMem_mload64_long (I : ExecutionEnv) (base out : ByteArray)
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlong : 160 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (flowVatIlksPostCallMem I base out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((flowVatIlksPostCallMem I base out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [flowVatIlksPostCallMem_size_long I base out hbase hlong hout]; decide)
    (by decide)
    (flowVatIlksPostCallMem_read64_long I base out hbase hread64 hlong hout)

theorem flowVatIlksPostCallMem_read160_long (I : ExecutionEnv) (base out : ByteArray)
    (hbase : base.size = 96) (hlong : 160 ≤ out.size) (hout : out.size < UInt256.size) :
    (flowVatIlksPostCallMem I base out).readWithPadding 160 32 = out.extract 32 64 := by
  have hmin :
      (min flowVatIlksOutSize (UInt256.ofNat out.size)).toNat = 160 := by
    exact umin_ofNat_right_toNat_of_ge (c := 160) (n := out.size) (by decide) hlong hout
  unfold flowVatIlksPostCallMem
  rw [hmin]
  change (out.write 0 (flowVatIlksCalldataMem I base) 128 160).readWithPadding 160 32 =
    out.extract 32 64
  rw [write_eq_gen_extend out (flowVatIlksCalldataMem I base) 128 160
    (by omega) (by omega)
    (by rw [flowVatIlksCalldataMem_size I hbase]; omega)
    (by rw [flowVatIlksCalldataMem_size I hbase]; omega)]
  have hprefix : ((flowVatIlksCalldataMem I base).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, flowVatIlksCalldataMem_size I hbase]
    omega
  have hsrc : (out.extract 0 160).size = 160 := by
    rw [ByteArray.size_extract]
    omega
  have hmemSize :
      ((flowVatIlksCalldataMem I base).extract 0 128 ++ out.extract 0 160).size = 288 := by
    rw [ByteArray.size_append, hprefix, hsrc]
  have hreadIn :
      160 + 32 ≤ ((flowVatIlksCalldataMem I base).extract 0 128 ++
        out.extract 0 160).size := by
    rw [hmemSize]
    omega
  rw [readWithPadding_eq_extract _ 160 hreadIn]
  rw [extract_append_right_window _ _ 160 192 (by rw [hprefix]; omega), hprefix]
  rw [show 160 - 128 = 32 by omega, show 192 - 128 = 64 by omega]
  rw [extract_extract_BA]
  norm_num

theorem flowVatIlksPostCallMem_mload160_long (I : ExecutionEnv) (base out : ByteArray)
    (hbase : base.size = 96) (hlong : 160 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨160⟩ : UInt256).toNat ≥ (flowVatIlksPostCallMem I base out).size
        ∨ (⟨160⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((flowVatIlksPostCallMem I base out).readWithPadding (⟨160⟩ : UInt256).toNat 32))) =
      flowVatIlksRateWord out := by
  unfold flowVatIlksRateWord
  rw [if_neg]
  · change UInt256.ofNat
      (fromByteArrayBigEndian ((flowVatIlksPostCallMem I base out).readWithPadding 160 32)) =
        UInt256.ofNat (fromByteArrayBigEndian (out.extract 32 64))
    rw [flowVatIlksPostCallMem_read160_long I base out hbase hlong hout]
  · exact not_or.mpr
      ⟨by rw [flowVatIlksPostCallMem_size_long I base out hbase hlong hout]; decide,
        by native_decide⟩

theorem flow_wordAt0Mem_size_of_ge32 {mem : ByteArray} (word : UInt256)
    (hmem : 32 ≤ mem.size) :
    (wordAt0Mem word mem).size = mem.size := by
  unfold wordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
  omega

theorem flow_wordAt32Mem_size_of_ge64 {mem : ByteArray} (word : UInt256)
    (hmem : 64 ≤ mem.size) :
    (wordAt32Mem word mem).size = mem.size := by
  unfold wordAt32Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
  omega

theorem flow_twoWordHashMem_size_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).size = mem.size := by
  unfold twoWordHashMem
  rw [flow_wordAt32Mem_size_of_ge64 slot (by
    rw [flow_wordAt0Mem_size_of_ge32 key (by omega)]
    exact hmem)]
  exact flow_wordAt0Mem_size_of_ge32 key (by omega)

theorem flow_twoWordHashMem_read0_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 = UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
    (by rw [flow_wordAt0Mem_size_of_ge32 key (by omega)]; omega) (by omega)]
  exact wordAt0Mem_read0 key mem

theorem flow_twoWordHashMem_read32_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 = UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [flow_wordAt0Mem_size_of_ge32 key (by omega)]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray slot).size ≤ 32
    rw [toByteArray_size])

theorem flow_twoWordHashMem_read64_of_ge96 {mem : ByteArray} (key slot : UInt256)
    (hmem : 96 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [flow_wordAt0Mem_size_of_ge32 key (by omega)]; omega) (by omega)
      (by rw [flow_wordAt0Mem_size_of_ge32 key (by omega)]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by omega) (by omega)
      (by omega)]
  exact hread64

theorem flow_twoWordHashMem_read0_64_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [flow_twoWordHashMem_size_of_ge64 key slot hmem]; omega)]
  have hleft :
      (twoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [flow_twoWordHashMem_size_of_ge64 key slot hmem]; omega),
      flow_twoWordHashMem_read0_of_ge64 key slot hmem]
  have hright :
      (twoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [flow_twoWordHashMem_size_of_ge64 key slot hmem]; omega),
      flow_twoWordHashMem_read32_of_ge64 key slot hmem]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem flow_twoWordHashMem_solcMappingSlot_of_ge64 (baseSlot key : UInt256)
    {mem : ByteArray} (hmem : 64 ≤ mem.size) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  rw [flow_twoWordHashMem_read0_64_of_ge64 key baseSlot hmem]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

theorem flowEvmAddress_ofNat_toNat_eq_ofUInt256 (w : UInt256) :
    EVM.address (↑(AccountAddress.ofNat w.toNat) : ℕ) = AccountAddress.ofUInt256 w := by
  apply Fin.ext
  simp [EVM.address, EVM.uintN, AccountAddress.ofNat, AccountAddress.ofUInt256,
    UInt256.toNat]
  rw [show AccountAddress.size = EVM.twoPow 160 from by decide]
  rw [Nat.mod_mod]

theorem endDecode_flow_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (flowTransition.params.map Param.name)
      (transitionSignature flowTransition).paramTypes I.calldata = some (flowStore I) := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["ilk"] [bytes32] I.calldata =
    some (flowStore I)
  simpa [flowStore, flowIlkWord] using
    endDecodeCalldata_legacyBytes32_ok (cd := I.calldata) (x := "ilk") hsz36

theorem endDecode_flow_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (flowTransition.params.map Param.name)
      (transitionSignature flowTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["ilk"] [bytes32] I.calldata = none
  simpa using endDecodeCalldata_legacyBytes32_none_short (cd := I.calldata) (x := "ilk")
    hsz4 hshort

theorem endDispatchFlowLocal {I : ExecutionEnv} (hsel : selIs I (endSelBytes 29)) :
    dispatchMsg contract I.calldata = some flowTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 29 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some flowTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

set_option maxHeartbeats 5000000 in
theorem endReachFlowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (endSelBytes 29)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨635⟩ [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x4a10eaa6⟩ :=
    endSelWord_eq_of_beq I hsz 0x4a 0x10 0xea 0xa6 ⟨0x4a10eaa6⟩
      (by native_decide) (by simpa [endSelBytes] using hsel)
  obtain ⟨_, _, h32⟩ :=
    endReachRootSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have hroot :
      UInt256.gt (armSelNat endBytecode (⟨32⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h271 := RD.selectorSplitTakenAuto h32
    (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
    hroot (by jump_dest) (by simp)
  have h272 := h271.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  have h272gt :
      UInt256.gt (armSelNat endBytecode (⟨272⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h391 := RD.selectorSplitTakenAuto h272
    (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
    h272gt (by jump_dest) (by simp)
  have h392 := h391.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  have h392gt :
      UInt256.gt (armSelNat endBytecode (⟨392⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have h403 := by
    simpa [selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc,
      selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h392
        (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
        h392gt (by simp)
  have hflow :
      UInt256.eq (armSelNat endBytecode (⟨403⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h635 := h403.selectorArmTakenAuto
    (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
    hflow (by jump_dest) (by simp)
  exact ⟨_, _, h635⟩

theorem endFlowX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨635⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2718⟩
        [flowIlkWord I, ⟨562⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := endBytecode) (sel := sel) (entry := ⟨635⟩) (ret := ⟨562⟩)
    (decoded := ⟨657⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneBytes32ExternalJump
    (code := endBytecode) (decoded := ⟨657⟩) (ret := ⟨562⟩) (routine := ⟨2718⟩)
    (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by simpa [flowIlkWord] using hroutine⟩

theorem endFlowX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨635⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := endBytecode) (sel := sel)
    (entry := ⟨635⟩) (ret := ⟨562⟩) (decoded := ⟨657⟩)
    (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem endFlowX_debtZero {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hdebt : flowDebtWord σ I = ⟨0⟩)
    (h : RD endBytecode I g s0 ⟨2718⟩
      [flowIlkWord I, ⟨562⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g s0 := by
  have rd2721pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨11⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k2722, C2722, rd2722raw⟩ := rd2721pre.sload (by native_decide) (by evm_ov)
  have rd2722 : RD endBytecode I g s0 ⟨2722⟩
      (flowDebtWord σ I :: flowIlkWord I :: ⟨562⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2722 C2722 := by
    simpa [flowDebtWord, endSlotWord] using rd2722raw
  have rd2725pre := rd2722.pushConst (⟨2786⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  rw [hdebt] at rd2725pre
  have rd2726 := rd2725pre.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨2726⟩)
    (len := ⟨13⟩)
    (rawWord := ⟨5500907680949753345960233497199⟩)
    (shift := ⟨152⟩)
    (word := ⟨31404631181696111852587681435152519789922048605590159656180814133474522824704⟩)
    (op := .PUSH13)
    (width := 13)
    rd2726
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    (by native_decide)
    solcFreePtrMem_size
    solcFreePtrMem_read64
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endFlowX_toFixGuard {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hdebt : flowDebtWord σ I ≠ ⟨0⟩)
    (h : RD endBytecode I g s0 ⟨2718⟩
      [flowIlkWord I, ⟨562⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨2786⟩
      [flowIlkWord I, ⟨562⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd2721pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨11⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k2722, C2722, rd2722raw⟩ := rd2721pre.sload (by native_decide) (by evm_ov)
  have rd2722 : RD endBytecode I g s0 ⟨2722⟩
      (flowDebtWord σ I :: flowIlkWord I :: ⟨562⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2722 C2722 := by
    simpa [flowDebtWord, endSlotWord] using rd2722raw
  have rd2725pre := rd2722.pushConst (⟨2786⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2725pre.jumpiT (by native_decide) hdebt (by jump_dest) (by evm_ov)⟩

theorem endFlowX_fixNonzero {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hfix : flowFixWord σ I ≠ ⟨0⟩)
    (h : RD endBytecode I g s0 ⟨2786⟩
      [flowIlkWord I, ⟨562⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g s0 := by
  have hslot :
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC ((twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem).readWithPadding
              0 64))) =
        flowFixStorageSlot I := by
    rw [twoWordHashMem_solcMappingSlot ⟨15⟩ (flowIlkWord I) solcFreePtrMem_size]
    exact (flowFixStorageSlot_eq I).symm
  have rd2800pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (flowIlkWord I) solcFreePtrMem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by simp [wordAt0Mem])
      (by native_decide) (by evm_ov),
    raw push1 ⟨15⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by
        simp [twoWordHashMem, wordAt32Mem,
          show (⟨32⟩ : UInt256).toNat = 32 from by native_decide])
      (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2801hash := rd2800pre.keccak256 0 (flowFixStorageSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨k2802, C2802, rd2802raw⟩ := rd2801hash.sload (by native_decide) (by evm_ov)
  have rd2802 : RD endBytecode I g s0 ⟨2802⟩
      (flowFixWord σ I :: flowIlkWord I :: ⟨562⟩ :: [sel])
      (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k2802 C2802 := by
    simpa [flowFixWord, endSlotWord, flowFixStorageSlot] using rd2802raw
  have rd2806pre := evm_run rd2802 with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨2883⟩ (by native_decide) (by evm_ov)]
  rw [isZero_eq_zero_of_ne hfix] at rd2806pre
  have rd2807 := rd2806pre.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTailPush32
    (pc := ⟨2807⟩)
    (len := ⟨27⟩)
    (word := ⟨31404631181908416848914724429500628695992939512474877550326037193834511728640⟩)
    rd2807
    (by
      unfold solcErrorStringRevertTailPush32Wf
      repeat' first | apply And.intro | native_decide)
    (twoWordHashMem_size_96 (flowIlkWord I) ⟨15⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 (flowIlkWord I) ⟨15⟩ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endFlowX_fixZero_toVat {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hfix : flowFixWord σ I = ⟨0⟩)
    (h : RD endBytecode I g s0 ⟨2786⟩
      [flowIlkWord I, ⟨562⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨2887⟩
      [flowVatWord σ I, flowIlkWord I, ⟨562⟩, sel]
      (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hslot :
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC ((twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem).readWithPadding
              0 64))) =
        flowFixStorageSlot I := by
    rw [twoWordHashMem_solcMappingSlot ⟨15⟩ (flowIlkWord I) solcFreePtrMem_size]
    exact (flowFixStorageSlot_eq I).symm
  have rd2800pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (flowIlkWord I) solcFreePtrMem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by simp [wordAt0Mem])
      (by native_decide) (by evm_ov),
    raw push1 ⟨15⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by
        simp [twoWordHashMem, wordAt32Mem,
          show (⟨32⟩ : UInt256).toNat = 32 from by native_decide])
      (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2801hash := rd2800pre.keccak256 0 (flowFixStorageSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨k2802, C2802, rd2802raw⟩ := rd2801hash.sload (by native_decide) (by evm_ov)
  have rd2802 : RD endBytecode I g s0 ⟨2802⟩
      (flowFixWord σ I :: flowIlkWord I :: ⟨562⟩ :: [sel])
      (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k2802 C2802 := by
    simpa [flowFixWord, endSlotWord, flowFixStorageSlot] using rd2802raw
  have rd2806pre := evm_run rd2802 with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨2883⟩ (by native_decide) (by evm_ov)]
  have hiszero : UInt256.isZero (flowFixWord σ I) ≠ ⟨0⟩ := by
    rw [hfix]
    native_decide
  have rd2883 := rd2806pre.jumpiT (by native_decide) hiszero (by jump_dest) (by evm_ov)
  have rd2886pre := rd2883.jumpdest (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  obtain ⟨k2887, C2887, rd2887raw⟩ := rd2886pre.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [flowVatWord, endSlotWord] using rd2887raw⟩

theorem RD.endFlowVatIlksExtcodesizeGuard
    {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨2887⟩
      [flowVatWord σ I, flowIlkWord I, ⟨562⟩, sel]
      (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨2948⟩
      (flowVatMaskedWord σ I :: flowVatMaskedWord σ I :: ⟨0⟩ ::
        flowVatIlksOutPtr :: flowVatIlksInSize :: flowVatIlksOutPtr ::
        flowVatIlksOutSize :: flowVatIlksEndPtr :: flowVatIlksSelectorWord ::
        flowVatMaskedWord σ I :: ⟨0⟩ :: flowIlkWord I :: ⟨562⟩ :: [sel])
      (flowVatIlksCalldataMem I (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem))
      (UInt256.ofNat 6) ByteArray.empty (cA, σ) k' C' := by
  let mem0 := twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem
  have hmem0 : mem0.size = 96 := by
    simpa [mem0] using twoWordHashMem_size_96 (flowIlkWord I) ⟨15⟩ solcFreePtrMem_size
  have hread0 : mem0.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [mem0] using
      twoWordHashMem_read64 (flowIlkWord I) ⟨15⟩ solcFreePtrMem_size solcFreePtrMem_read64
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem0.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem0.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem0]; decide) (by decide) hread0
  have hCallMemSize : (flowVatIlksCalldataMem I mem0).size = 164 :=
    flowVatIlksCalldataMem_size I hmem0
  have hCallRead64 :
      (flowVatIlksCalldataMem I mem0).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    flowVatIlksCalldataMem_read64 I hmem0 hread0
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (flowVatIlksCalldataMem I mem0).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((flowVatIlksCalldataMem I mem0).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hCallMemSize]; decide) (by decide) hCallRead64
  have rd2948 := evm_run rd with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost (by simpa [mem0] using hmload64) (by decide) (by evm_ov),
    raw push4 ⟨0x6cb1c69b⟩ (by native_decide) (by evm_ov),
    push1 ⟨225⟩,
    shl,
    dup2,
    raw mstore 6 (flowVatIlksSelectorMem mem0) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    push1 ⟨4⟩,
    dup2,
    add,
    dup5,
    swap1,
    raw mstore 3 (flowVatIlksCalldataMem I mem0) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost (by simpa [mem0] using hmload64Call) (by decide) (by evm_ov),
    push1 ⟨0⟩,
    swap3,
    push1 ⟨1⟩,
    push1 ⟨1⟩,
    push1 ⟨160⟩,
    shl,
    sub,
    and,
    swap2,
    raw push4 flowVatIlksSelectorWord (by native_decide) (by evm_ov),
    swap2,
    push1 ⟨36⟩,
    dup1,
    dup4,
    add,
    swap3,
    push1 ⟨160⟩,
    swap3,
    swap2,
    swap1,
    dup3,
    swap1,
    sub,
    add,
    dup2,
    dup8,
    dup8,
    dup1]
  exact ⟨_, _, by
    simpa [mem0, flowVatMaskedWord, flowVatWord, endSlotWord, flowVatIlksSelectorShifted,
      flowVatIlksSelectorWord, flowVatIlksSelectorMem, flowVatIlksCalldataMem,
      flowVatIlksOutPtr, flowVatIlksInSize, flowVatIlksOutSize, flowVatIlksEndPtr,
      solcAddrMask, u256_land_comm,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide] using rd2948⟩

theorem RD.endFlowVatIlksNoCode
    {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨2887⟩
      [flowVatWord σ I, flowIlkWord I, ⟨562⟩, sel]
      (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (flowVatMaskedWord σ I) = ⟨0⟩) :
    RDrev endBytecode g s0 := by
  obtain ⟨_, _, rd2948⟩ := RD.endFlowVatIlksExtcodesizeGuard rd
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨2948⟩) (okPc := ⟨2960⟩)
    rd2948 hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem RD.endFlowVatIlksCall
    {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨2887⟩
      [flowVatWord σ I, flowIlkWord I, ⟨562⟩, sel]
      (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (flowVatMaskedWord σ I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g s0 ⟨2963⟩
      (gasWord :: flowVatMaskedWord σ I :: ⟨0⟩ ::
        flowVatIlksOutPtr :: flowVatIlksInSize :: flowVatIlksOutPtr ::
        flowVatIlksOutSize :: flowVatIlksEndPtr :: flowVatIlksSelectorWord ::
        flowVatMaskedWord σ I :: ⟨0⟩ :: flowIlkWord I :: ⟨562⟩ :: [sel])
      (flowVatIlksCalldataMem I (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem))
      (UInt256.ofNat 6) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd2948⟩ := RD.endFlowVatIlksExtcodesizeGuard rd
  obtain ⟨gasWord, k', C', rd2963⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨2948⟩) (okPc := ⟨2960⟩)
      rd2948 hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by evm_ov)
  exact ⟨gasWord, k', C', rd2963⟩

theorem RD.endFlowVatIlksPostCallRaw
    {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨2887⟩
      [flowVatWord σ I, flowIlkWord I, ⟨562⟩, sel]
      (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (flowVatMaskedWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (k' C' : ℕ),
      RD endBytecode I g s0 ⟨2964⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: flowVatIlksEndPtr :: flowVatIlksSelectorWord ::
          flowVatMaskedWord σ I :: ⟨0⟩ :: flowIlkWord I :: ⟨562⟩ :: [sel])
        (flowVatIlksPostCallMem I (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem) out)
        (UInt256.ofNat 9) out (cA', σ') k' C'
    ∧ out.size < UInt256.size := by
  obtain ⟨_, _, _, rd2963⟩ := RD.endFlowVatIlksCall rd hcodeSize
  obtain ⟨cA', σ', z, out, A_in, callGas, k2964, C2964, hΘ, rd2964raw, houtsz⟩ :=
    RD.call rd2963 (by native_decide) hdepth (by evm_ov)
  obtain ⟨_, _, _⟩ := hΘ
  refine ⟨cA', σ', z, out, k2964, C2964, ?_, houtsz⟩
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
        flowVatIlksOutPtr.toNat flowVatIlksInSize.toNat)
        flowVatIlksOutPtr.toNat flowVatIlksOutSize.toNat) = UInt256.ofNat 9 := by
    unfold flowVatIlksOutPtr flowVatIlksInSize flowVatIlksOutSize
    native_decide
  simpa [flowVatIlksPostCallMem] using haw ▸ rd2964raw

theorem RD.endFlowVatIlksPostCall
    {cA gh bl σ σ₀ A I} {g sel : UInt256} {k C : ℕ}
    (rd : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2887⟩
      [flowVatWord σ I, flowIlkWord I, ⟨562⟩, sel]
      (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (flowVatMaskedWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD endBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2964⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: flowVatIlksEndPtr :: flowVatIlksSelectorWord ::
          flowVatMaskedWord σ I :: ⟨0⟩ :: flowIlkWord I :: ⟨562⟩ :: [sel])
        (flowVatIlksPostCallMem I
          (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem) out)
        (UInt256.ofNat 9) out (cA', σ') k' C'
    ∧ typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (flowVatMaskedWord σ I).toNat)) "vatIlks" 0
        [flowIlkValue I]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, out) I.perm
    ∧ out.size < UInt256.size := by
  obtain ⟨_, _, _, rd2963⟩ := RD.endFlowVatIlksCall rd hcodeSize
  obtain ⟨cA', σ', z, out, A_in, callGas, k2964, C2964, hΘ, rd2964raw, houtsz⟩ :=
    RD.call rd2963 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ'⟩ := hΘ
  refine ⟨cA', σ', z, out, A', k2964, C2964, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          flowVatIlksOutPtr.toNat flowVatIlksInSize.toNat)
          flowVatIlksOutPtr.toNat flowVatIlksOutSize.toNat) = UInt256.ofNat 9 := by
      unfold flowVatIlksOutPtr flowVatIlksInSize flowVatIlksOutSize
      native_decide
    simpa [flowVatIlksPostCallMem] using haw ▸ rd2964raw
  · let mem0 := twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem
    have hmem0 : mem0.size = 96 := by
      simpa [mem0] using twoWordHashMem_size_96 (flowIlkWord I) ⟨15⟩ solcFreePtrMem_size
    refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := I.perm) (targetWord := flowVatMaskedWord σ I)
      (mem := flowVatIlksCalldataMem I mem0) (inOff := flowVatIlksOutPtr)
      (inSize := flowVatIlksInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      ?_ (flowVatIlksEncode_eq I hmem0) ?_
    · exact (flowEvmAddress_ofNat_toNat_eq_ofUInt256 (flowVatMaskedWord σ I)).symm
    · simpa [initState, mem0] using hΘ'

theorem RD.endFlowVatIlksDepthLimitReverts
    {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨2887⟩
      [flowVatWord σ I, flowIlkWord I, ⟨562⟩, sel]
      (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (flowVatMaskedWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024) :
    RDrev endBytecode g s0 := by
  obtain ⟨_, _, _, rd2963⟩ := RD.endFlowVatIlksCall rd hcodeSize
  obtain ⟨k2964, C2964, rd2964raw⟩ :=
    RD.callDepthLimit rd2963 (by native_decide) hdepth (by simp)
  have hmin : (min flowVatIlksOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    unfold flowVatIlksOutSize
    rw [← u256_ofNat_toNat (UInt256.ofNat ByteArray.empty.size)]
    exact umin_ofNat_right_toNat_of_ge (by norm_num [UInt256.size]) (Nat.zero_le _)
      (UInt256.ofNat ByteArray.empty.size).val.isLt
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
        flowVatIlksOutPtr.toNat flowVatIlksInSize.toNat)
        flowVatIlksOutPtr.toNat flowVatIlksOutSize.toNat) = UInt256.ofNat 9 := by
    unfold flowVatIlksOutPtr flowVatIlksInSize flowVatIlksOutSize
    native_decide
  have rd2964 : RD endBytecode I g s0 ⟨2964⟩
      (⟨0⟩ :: flowVatIlksEndPtr :: flowVatIlksSelectorWord :: flowVatMaskedWord σ I ::
        ⟨0⟩ :: flowIlkWord I :: ⟨562⟩ :: [sel])
      (flowVatIlksPostCallMem I
        (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem) ByteArray.empty)
      (UInt256.ofNat 9) ByteArray.empty (cA, σ) k2964 C2964 := by
    simpa [flowVatIlksPostCallMem, hmin] using haw ▸ rd2964raw
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨2964⟩) (okPc := ⟨2980⟩) rd2964
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem RD.endFlowVatIlksCallFailure
    {cA σ I} {g : Sat256} {s0 : State} {mem o : ByteArray} {aw : UInt256}
    {k C : ℕ} {rest : List UInt256}
    (rd : RD endBytecode I g s0 ⟨2964⟩
      (⟨0⟩ :: rest) mem aw o (cA, σ) k C)
    (hosz : o.size < UInt256.size)
    (hov : rest.length + 5 ≤ 1024) :
    RDrev endBytecode g s0 := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨2964⟩) (okPc := ⟨2980⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) hosz hov

theorem RD.endFlowVatIlksCallSuccessToDecode
    {cA σ I} {g : Sat256} {s0 : State} {mem o : ByteArray} {aw : UInt256}
    {k C : ℕ} {R : List UInt256}
    (rd : RD endBytecode I g s0 ⟨2964⟩ (⟨1⟩ :: R) mem aw o (cA, σ) k C)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD endBytecode I g s0 ⟨2982⟩ R mem aw o (cA, σ) k' C' := by
  exact RD.uniswapCallSuccessGuardOk (pc := ⟨2964⟩) (okPc := ⟨2980⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide) hov

theorem RD.endFlowVatIlksReturnDecodeShortReverts
    {cA σStack σCall I} {g : Sat256} {s0 : State} {base out : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨2982⟩
      (flowVatIlksEndPtr :: flowVatIlksSelectorWord :: flowVatMaskedWord σStack I ::
        ⟨0⟩ :: flowIlkWord I :: ⟨562⟩ :: [sel])
      (flowVatIlksPostCallMem I base out) (UInt256.ofNat 9) out (cA, σCall) k C)
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hshort : out.size < 160) (hout : out.size < UInt256.size) :
    RDrev endBytecode g s0 := by
  have hmload64 := flowVatIlksPostCallMem_mload64 I base out hbase hread64 hshort hout
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨160⟩ : UInt256) = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide, ulit_toNat' out.size hout]
    exact hshort
  have rd2992 := evm_run rd with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2993raw := RD.lt rd2992 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2993 := by
    simpa [hlt] using rd2993raw
  have rd2997 := evm_run rd2993 with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨3002⟩ (by native_decide) (by evm_ov)]
  have rd2998 := rd2997.jumpiNT (by native_decide) rfl
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact RD.uniswapPush1Dup1Revert0 (pc := ⟨2998⟩) rd2998
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem RD.endFlowVatIlksReturnDecodeOkToRmul
    {cA σStack σCall I} {g : Sat256} {s0 : State} {base out : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨2982⟩
      (flowVatIlksEndPtr :: flowVatIlksSelectorWord :: flowVatMaskedWord σStack I ::
        ⟨0⟩ :: flowIlkWord I :: ⟨562⟩ :: [sel])
      (flowVatIlksPostCallMem I base out) (UInt256.ofNat 9) out (cA, σCall) k C)
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlong : 160 ≤ out.size) (hout : out.size < UInt256.size) :
    ∃ k' C', RD endBytecode I g s0 ⟨10114⟩
      (flowVatIlksRateWord out :: flowArtWord σCall I :: ⟨3041⟩ :: ⟨3061⟩ ::
        ⟨0⟩ :: flowVatIlksRateWord out :: flowIlkWord I :: ⟨562⟩ :: [sel])
      (twoWordHashMem (flowIlkWord I) ⟨14⟩ (flowVatIlksPostCallMem I base out))
      (UInt256.ofNat 9) out (cA, σCall) k' C' := by
  have hmload64 := flowVatIlksPostCallMem_mload64_long I base out hbase hread64 hlong hout
  have hmload160 := flowVatIlksPostCallMem_mload160_long I base out hbase hlong hout
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨160⟩ : UInt256) = ⟨0⟩ := by
    apply ult_zero
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide, ulit_toNat' out.size hout]
    exact hlong
  have hslot :
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC ((twoWordHashMem (flowIlkWord I) ⟨14⟩
              (flowVatIlksPostCallMem I base out)).readWithPadding 0 64))) =
        flowArtStorageSlot I := by
    rw [flow_twoWordHashMem_solcMappingSlot_of_ge64 ⟨14⟩ (flowIlkWord I)
      (by rw [flowVatIlksPostCallMem_size_long I base out hbase hlong hout]; omega)]
    rfl
  have rd2992 := evm_run rd with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2993raw := RD.lt rd2992 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2993 := by
    simpa [hlt] using rd2993raw
  have rd2997 := evm_run rd2993 with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨3002⟩ (by native_decide) (by evm_ov)]
  have rd3002 := rd2997.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3008 := evm_run rd3002 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3009raw := RD.add rd3008 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨k3009, C3009, rd3009⟩ :
      ∃ k3009 C3009, RD endBytecode I g s0 ⟨3009⟩
        (⟨160⟩ :: ⟨32⟩ :: ⟨0⟩ :: flowIlkWord I :: ⟨562⟩ :: [sel])
        (flowVatIlksPostCallMem I base out) (UInt256.ofNat 9) out
        (cA, σCall) k3009 C3009 := by
    exact ⟨_, _, by simpa using rd3009raw⟩
  have rd3023 := evm_run rd3009 with [
    raw mload 0 (flowVatIlksRateWord out) (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload160 (by decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (flowIlkWord I) (flowVatIlksPostCallMem I base out))
      (UInt256.ofNat 9) (by native_decide) mem_cost (by simp [wordAt0Mem])
      (by native_decide) (by evm_ov),
    raw push1 ⟨14⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw mstore 0 (twoWordHashMem (flowIlkWord I) ⟨14⟩
      (flowVatIlksPostCallMem I base out)) (UInt256.ofNat 9)
      (by native_decide) mem_cost
      (by
        simp [twoWordHashMem, wordAt32Mem,
          show (⟨32⟩ : UInt256).toNat = 32 from by native_decide])
      (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have rd3024hash := rd3023.keccak256 0 (flowArtStorageSlot I)
    (UInt256.ofNat 9) (by native_decide) mem_cost hslot (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨k3025, C3025, rd3025raw⟩ := rd3024hash.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3025 : RD endBytecode I g s0 ⟨3025⟩
      (flowArtWord σCall I :: flowVatIlksRateWord out :: ⟨0⟩ :: ⟨0⟩ ::
        flowIlkWord I :: ⟨562⟩ :: [sel])
      (twoWordHashMem (flowIlkWord I) ⟨14⟩ (flowVatIlksPostCallMem I base out))
      (UInt256.ofNat 9) out (cA, σCall) k3025 C3025 := by
    simpa [flowArtWord, endSlotWord, flowArtStorageSlot] using rd3025raw
  have rd10114 := evm_run rd3025 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push2 ⟨3061⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨3041⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw push2 ⟨10114⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by simpa using rd10114⟩

theorem RD.endFlowFirstRmulOk
    {cA σ I} {g : Sat256} {s0 : State} {base out : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (hmul :
      (flowArtWord σ I).toNat * (flowVatIlksRateWord out).toNat < UInt256.size)
    (hrate : flowVatIlksRateWord out ≠ ⟨0⟩)
    (h : RD endBytecode I g s0 ⟨10114⟩
      (flowVatIlksRateWord out :: flowArtWord σ I :: ⟨3041⟩ :: ⟨3061⟩ ::
        ⟨0⟩ :: flowVatIlksRateWord out :: flowIlkWord I :: ⟨562⟩ :: [sel])
      (twoWordHashMem (flowIlkWord I) ⟨14⟩ (flowVatIlksPostCallMem I base out))
      (UInt256.ofNat 9) out (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨3041⟩
      (flowWad0Word σ I out :: ⟨3061⟩ :: ⟨0⟩ ::
        flowVatIlksRateWord out :: flowIlkWord I :: ⟨562⟩ :: [sel])
      (twoWordHashMem (flowIlkWord I) ⟨14⟩ (flowVatIlksPostCallMem I base out))
      (UInt256.ofNat 9) out (cA, σ) k' C' := by
  have rd10138pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov)]
  have rd10130pre := rd10138pre.pushConst flowRayWord
    (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
  have rd10138pre := evm_run rd10130pre with [
    raw push2 ⟨10139⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw push2 ⟨10170⟩ (by native_decide) (by evm_ov)]
  have rd10170 := rd10138pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd10180pre := evm_run rd10170 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨10197⟩ (by native_decide) (by evm_ov)]
  rw [isZero_eq_zero_of_ne hrate] at rd10180pre
  have rd10182pre := evm_run
      (rd10180pre.jumpiNT (by native_decide) rfl (by evm_ov)) with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd10192pre := evm_run rd10182pre with [
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨10194⟩ (by native_decide) (by evm_ov)]
  have rd10194raw := rd10192pre.jumpiT (by native_decide) hrate
    (by jump_dest) (by evm_ov)
  have rd10197pre := evm_run (rd10194raw.jumpdest (by native_decide) (by evm_ov)) with [
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨10108⟩ (by native_decide) (by evm_ov)]
  have hdiv :
      UInt256.div (flowWad0MulWord σ I out) (flowVatIlksRateWord out) =
        flowArtWord σ I := by
    simpa [flowWad0MulWord] using
      flow_mul_div_right_cancel
        (x := flowArtWord σ I) (y := flowVatIlksRateWord out) hmul hrate
  rw [hdiv, u256_eq_refl] at rd10197pre
  have rd10108 := rd10197pre.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)
  have rd10113pre := evm_run (rd10108.jumpdest (by native_decide) (by evm_ov)) with [
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  obtain ⟨k10139, C10139, rd10139⟩ :
      ∃ k10139 C10139, RD endBytecode I g s0 ⟨10139⟩
        (flowWad0MulWord σ I out :: flowRayWord :: ⟨0⟩ :: flowVatIlksRateWord out ::
          flowArtWord σ I :: ⟨3041⟩ :: ⟨3061⟩ :: ⟨0⟩ ::
          flowVatIlksRateWord out :: flowIlkWord I :: ⟨562⟩ :: [sel])
        (twoWordHashMem (flowIlkWord I) ⟨14⟩ (flowVatIlksPostCallMem I base out))
        (UInt256.ofNat 9) out (cA, σ) k10139 C10139 := by
    exact ⟨_, _, by
      simpa [flowWad0MulWord] using
        rd10113pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩
  have rd10145pre := evm_run rd10139 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨10146⟩ (by native_decide) (by evm_ov)]
  have hrayNonzero : flowRayWord ≠ ⟨0⟩ := by native_decide
  have rd10146raw := rd10145pre.jumpiT (by native_decide) hrayNonzero
    (by jump_dest) (by evm_ov)
  have rd10153pre := evm_run (rd10146raw.jumpdest (by native_decide) (by evm_ov)) with [
    raw div (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [flowWad0Word] using
      rd10153pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem flowWad0Word_eq_zero_of_rate_zero (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) (hrate : flowVatIlksRateWord out = ⟨0⟩) :
    flowWad0Word σ I out = ⟨0⟩ := by
  apply u256_inj
  rw [flowWad0Word, flowWad0MulWord, hrate, udiv_toNat, u256_mul_toNat]
  norm_num

theorem RD.endFlowFirstRmulRateZero
    {cA σ I} {g : Sat256} {s0 : State} {base out : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (hrate : flowVatIlksRateWord out = ⟨0⟩)
    (h : RD endBytecode I g s0 ⟨10114⟩
      (flowVatIlksRateWord out :: flowArtWord σ I :: ⟨3041⟩ :: ⟨3061⟩ ::
        ⟨0⟩ :: flowVatIlksRateWord out :: flowIlkWord I :: ⟨562⟩ :: [sel])
      (twoWordHashMem (flowIlkWord I) ⟨14⟩ (flowVatIlksPostCallMem I base out))
      (UInt256.ofNat 9) out (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨3041⟩
      (flowWad0Word σ I out :: ⟨3061⟩ :: ⟨0⟩ ::
        flowVatIlksRateWord out :: flowIlkWord I :: ⟨562⟩ :: [sel])
      (twoWordHashMem (flowIlkWord I) ⟨14⟩ (flowVatIlksPostCallMem I base out))
      (UInt256.ofNat 9) out (cA, σ) k' C' := by
  have rd10138pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov)]
  have rd10130pre := rd10138pre.pushConst flowRayWord
    (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
  have rd10138pre := evm_run rd10130pre with [
    raw push2 ⟨10139⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw push2 ⟨10170⟩ (by native_decide) (by evm_ov)]
  have rd10170 := rd10138pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd10180pre := evm_run rd10170 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨10197⟩ (by native_decide) (by evm_ov)]
  have hiszero : UInt256.isZero (flowVatIlksRateWord out) ≠ ⟨0⟩ := by
    rw [hrate]
    native_decide
  have rd10197raw := rd10180pre.jumpiT (by native_decide) hiszero
    (by jump_dest) (by evm_ov)
  have rd10197pre := evm_run (rd10197raw.jumpdest (by native_decide) (by evm_ov)) with [
    raw push2 ⟨10108⟩ (by native_decide) (by evm_ov)]
  have rd10108 := rd10197pre.jumpiT (by native_decide) hiszero
    (by jump_dest) (by evm_ov)
  have rd10113pre := evm_run (rd10108.jumpdest (by native_decide) (by evm_ov)) with [
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  obtain ⟨k10139, C10139, rd10139⟩ :
      ∃ k10139 C10139, RD endBytecode I g s0 ⟨10139⟩
        (⟨0⟩ :: flowRayWord :: ⟨0⟩ :: flowVatIlksRateWord out ::
          flowArtWord σ I :: ⟨3041⟩ :: ⟨3061⟩ :: ⟨0⟩ ::
          flowVatIlksRateWord out :: flowIlkWord I :: ⟨562⟩ :: [sel])
        (twoWordHashMem (flowIlkWord I) ⟨14⟩ (flowVatIlksPostCallMem I base out))
        (UInt256.ofNat 9) out (cA, σ) k10139 C10139 := by
    exact ⟨_, _, by simpa [hrate] using
      rd10113pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩
  have rd10145pre := evm_run rd10139 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨10146⟩ (by native_decide) (by evm_ov)]
  have hrayNonzero : flowRayWord ≠ ⟨0⟩ := by native_decide
  have rd10146raw := rd10145pre.jumpiT (by native_decide) hrayNonzero
    (by jump_dest) (by evm_ov)
  have rd10153pre := evm_run (rd10146raw.jumpdest (by native_decide) (by evm_ov)) with [
    raw div (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    rw [flowWad0Word_eq_zero_of_rate_zero σ I out hrate]
    simpa [hrate] using
      rd10153pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem RD.endFlowFirstRmulOverflowReverts
    {cA σ I} {g : Sat256} {s0 : State} {base out : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (hdivne :
      UInt256.div (flowWad0MulWord σ I out) (flowVatIlksRateWord out) ≠
        flowArtWord σ I)
    (hrate : flowVatIlksRateWord out ≠ ⟨0⟩)
    (h : RD endBytecode I g s0 ⟨10114⟩
      (flowVatIlksRateWord out :: flowArtWord σ I :: ⟨3041⟩ :: ⟨3061⟩ ::
        ⟨0⟩ :: flowVatIlksRateWord out :: flowIlkWord I :: ⟨562⟩ :: [sel])
      (twoWordHashMem (flowIlkWord I) ⟨14⟩ (flowVatIlksPostCallMem I base out))
      (UInt256.ofNat 9) out (cA, σ) k C) :
    RDrev endBytecode g s0 := by
  have rd10138pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov)]
  have rd10130pre := rd10138pre.pushConst flowRayWord
    (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
  have rd10138pre := evm_run rd10130pre with [
    raw push2 ⟨10139⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw push2 ⟨10170⟩ (by native_decide) (by evm_ov)]
  have rd10170 := rd10138pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd10180pre := evm_run rd10170 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨10197⟩ (by native_decide) (by evm_ov)]
  rw [isZero_eq_zero_of_ne hrate] at rd10180pre
  have rd10182pre := evm_run
      (rd10180pre.jumpiNT (by native_decide) rfl (by evm_ov)) with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd10192pre := evm_run rd10182pre with [
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨10194⟩ (by native_decide) (by evm_ov)]
  have rd10194raw := rd10192pre.jumpiT (by native_decide) hrate
    (by jump_dest) (by evm_ov)
  have rd10197pre := evm_run (rd10194raw.jumpdest (by native_decide) (by evm_ov)) with [
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨10108⟩ (by native_decide) (by evm_ov)]
  have heqZero :
      UInt256.eq
          (UInt256.div (flowWad0MulWord σ I out) (flowVatIlksRateWord out))
          (flowArtWord σ I) = ⟨0⟩ :=
    u256_eq_of_ne hdivne
  rw [heqZero] at rd10197pre
  have rd10202 := rd10197pre.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.uniswapPush1Dup1Revert0 rd10202
    (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

theorem RD.endFlowFirstRmulOutcome
    {cA σ I} {g : Sat256} {s0 : State} {base out : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (h : RD endBytecode I g s0 ⟨10114⟩
      (flowVatIlksRateWord out :: flowArtWord σ I :: ⟨3041⟩ :: ⟨3061⟩ ::
        ⟨0⟩ :: flowVatIlksRateWord out :: flowIlkWord I :: ⟨562⟩ :: [sel])
      (twoWordHashMem (flowIlkWord I) ⟨14⟩ (flowVatIlksPostCallMem I base out))
      (UInt256.ofNat 9) out (cA, σ) k C) :
    (∃ k' C', RD endBytecode I g s0 ⟨3041⟩
      (flowWad0Word σ I out :: ⟨3061⟩ :: ⟨0⟩ ::
        flowVatIlksRateWord out :: flowIlkWord I :: ⟨562⟩ :: [sel])
      (twoWordHashMem (flowIlkWord I) ⟨14⟩ (flowVatIlksPostCallMem I base out))
      (UInt256.ofNat 9) out (cA, σ) k' C') ∨ RDrev endBytecode g s0 := by
  by_cases hrate : flowVatIlksRateWord out = ⟨0⟩
  · exact Or.inl (RD.endFlowFirstRmulRateZero hrate h)
  · by_cases hfit :
        (flowArtWord σ I).toNat * (flowVatIlksRateWord out).toNat < UInt256.size
    · exact Or.inl (RD.endFlowFirstRmulOk hfit hrate h)
    · have hover :
          UInt256.size ≤ (flowArtWord σ I).toNat * (flowVatIlksRateWord out).toNat :=
        Nat.le_of_not_gt hfit
      have hdivne :
          UInt256.div (flowWad0MulWord σ I out) (flowVatIlksRateWord out) ≠
            flowArtWord σ I := by
        simpa [flowWad0MulWord] using
          flow_udiv_mul_wrap_ne_of_overflow
            (a := flowArtWord σ I) (b := flowVatIlksRateWord out) hover
      exact Or.inr (RD.endFlowFirstRmulOverflowReverts hdivne hrate h)

theorem RD.endFlowToSecondRmul
    {cA σ I} {g : Sat256} {s0 : State} {base out : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (hbase : base.size = 96) (hlong : 160 ≤ out.size) (hout : out.size < UInt256.size)
    (h : RD endBytecode I g s0 ⟨3041⟩
      (flowWad0Word σ I out :: ⟨3061⟩ :: ⟨0⟩ ::
        flowVatIlksRateWord out :: flowIlkWord I :: ⟨562⟩ :: [sel])
      (twoWordHashMem (flowIlkWord I) ⟨14⟩ (flowVatIlksPostCallMem I base out))
      (UInt256.ofNat 9) out (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨10114⟩
      (flowTagWord σ I :: flowWad0Word σ I out :: ⟨3061⟩ :: ⟨0⟩ ::
        flowVatIlksRateWord out :: flowIlkWord I :: ⟨562⟩ :: [sel])
      (twoWordHashMem (flowIlkWord I) ⟨12⟩
        (twoWordHashMem (flowIlkWord I) ⟨14⟩ (flowVatIlksPostCallMem I base out)))
      (UInt256.ofNat 9) out (cA, σ) k' C' := by
  have hpostSize : (flowVatIlksPostCallMem I base out).size = 288 :=
    flowVatIlksPostCallMem_size_long I base out hbase hlong hout
  have hmem14Size :
      (twoWordHashMem (flowIlkWord I) ⟨14⟩
        (flowVatIlksPostCallMem I base out)).size = 288 := by
    rw [flow_twoWordHashMem_size_of_ge64]
    · rw [hpostSize]
    · rw [hpostSize]
      omega
  have hslot :
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC ((twoWordHashMem (flowIlkWord I) ⟨12⟩
              (twoWordHashMem (flowIlkWord I) ⟨14⟩
                (flowVatIlksPostCallMem I base out))).readWithPadding 0 64))) =
        flowTagStorageSlot I := by
    rw [flow_twoWordHashMem_solcMappingSlot_of_ge64 ⟨12⟩ (flowIlkWord I)
      (by rw [hmem14Size]; omega)]
    rfl
  have rd3055 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0
      (wordAt0Mem (flowIlkWord I)
        (twoWordHashMem (flowIlkWord I) ⟨14⟩ (flowVatIlksPostCallMem I base out)))
      (UInt256.ofNat 9) (by native_decide) mem_cost (by simp [wordAt0Mem])
      (by native_decide) (by evm_ov),
    raw push1 ⟨12⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0
      (twoWordHashMem (flowIlkWord I) ⟨12⟩
        (twoWordHashMem (flowIlkWord I) ⟨14⟩ (flowVatIlksPostCallMem I base out)))
      (UInt256.ofNat 9) (by native_decide) mem_cost
      (by
        simp [twoWordHashMem, wordAt32Mem,
          show (⟨32⟩ : UInt256).toNat = 32 from by native_decide])
      (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd3055hash := rd3055.keccak256 0 (flowTagStorageSlot I)
    (UInt256.ofNat 9) (by native_decide) mem_cost hslot (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨k3056, C3056, rd3056raw⟩ := rd3055hash.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3057 : RD endBytecode I g s0 ⟨3057⟩
      (flowTagWord σ I :: flowWad0Word σ I out :: ⟨3061⟩ :: ⟨0⟩ ::
        flowVatIlksRateWord out :: flowIlkWord I :: ⟨562⟩ :: [sel])
      (twoWordHashMem (flowIlkWord I) ⟨12⟩
        (twoWordHashMem (flowIlkWord I) ⟨14⟩ (flowVatIlksPostCallMem I base out)))
      (UInt256.ofNat 9) out (cA, σ) k3056 C3056 := by
    simpa [flowTagWord, flowTagStorageSlot, endSlotWord, solcSlotWord] using rd3056raw
  have rd10114 := evm_run rd3057 with [
    raw push2 ⟨10114⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by simpa using rd10114⟩

theorem RD.endFlowSecondRmulOk
    {cA σ I} {g : Sat256} {s0 : State} {out mem : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (hmul : (flowWad0Word σ I out).toNat * (flowTagWord σ I).toNat < UInt256.size)
    (htag : flowTagWord σ I ≠ ⟨0⟩)
    (h : RD endBytecode I g s0 ⟨10114⟩
      (flowTagWord σ I :: flowWad0Word σ I out :: ⟨3061⟩ :: ⟨0⟩ ::
        flowVatIlksRateWord out :: flowIlkWord I :: ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 9) out (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨3061⟩
      (flowWadWord σ I out :: ⟨0⟩ ::
        flowVatIlksRateWord out :: flowIlkWord I :: ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 9) out (cA, σ) k' C' := by
  have rd10138pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov)]
  have rd10130pre := rd10138pre.pushConst flowRayWord
    (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
  have rd10138pre := evm_run rd10130pre with [
    raw push2 ⟨10139⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw push2 ⟨10170⟩ (by native_decide) (by evm_ov)]
  have rd10170 := rd10138pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd10180pre := evm_run rd10170 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨10197⟩ (by native_decide) (by evm_ov)]
  rw [isZero_eq_zero_of_ne htag] at rd10180pre
  have rd10182pre := evm_run
      (rd10180pre.jumpiNT (by native_decide) rfl (by evm_ov)) with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd10192pre := evm_run rd10182pre with [
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨10194⟩ (by native_decide) (by evm_ov)]
  have rd10194raw := rd10192pre.jumpiT (by native_decide) htag
    (by jump_dest) (by evm_ov)
  have rd10197pre := evm_run (rd10194raw.jumpdest (by native_decide) (by evm_ov)) with [
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨10108⟩ (by native_decide) (by evm_ov)]
  have hdiv :
      UInt256.div (flowWadMulWord σ I out) (flowTagWord σ I) =
        flowWad0Word σ I out := by
    simpa [flowWadMulWord] using
      flow_mul_div_right_cancel
        (x := flowWad0Word σ I out) (y := flowTagWord σ I) hmul htag
  rw [hdiv, u256_eq_refl] at rd10197pre
  have rd10108 := rd10197pre.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)
  have rd10113pre := evm_run (rd10108.jumpdest (by native_decide) (by evm_ov)) with [
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  obtain ⟨k10139, C10139, rd10139⟩ :
      ∃ k10139 C10139, RD endBytecode I g s0 ⟨10139⟩
        (flowWadMulWord σ I out :: flowRayWord :: ⟨0⟩ :: flowTagWord σ I ::
          flowWad0Word σ I out :: ⟨3061⟩ :: ⟨0⟩ ::
          flowVatIlksRateWord out :: flowIlkWord I :: ⟨562⟩ :: [sel])
        mem (UInt256.ofNat 9) out (cA, σ) k10139 C10139 := by
    exact ⟨_, _, by
      simpa [flowWadMulWord] using
        rd10113pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩
  have rd10145pre := evm_run rd10139 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨10146⟩ (by native_decide) (by evm_ov)]
  have hrayNonzero : flowRayWord ≠ ⟨0⟩ := by native_decide
  have rd10146raw := rd10145pre.jumpiT (by native_decide) hrayNonzero
    (by jump_dest) (by evm_ov)
  have rd10153pre := evm_run (rd10146raw.jumpdest (by native_decide) (by evm_ov)) with [
    raw div (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [flowWadWord] using
      rd10153pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem flowWadWord_eq_zero_of_tag_zero (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) (htag : flowTagWord σ I = ⟨0⟩) :
    flowWadWord σ I out = ⟨0⟩ := by
  apply u256_inj
  rw [flowWadWord, flowWadMulWord, htag, udiv_toNat, u256_mul_toNat]
  norm_num

theorem RD.endFlowSecondRmulTagZero
    {cA σ I} {g : Sat256} {s0 : State} {out mem : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (htag : flowTagWord σ I = ⟨0⟩)
    (h : RD endBytecode I g s0 ⟨10114⟩
      (flowTagWord σ I :: flowWad0Word σ I out :: ⟨3061⟩ :: ⟨0⟩ ::
        flowVatIlksRateWord out :: flowIlkWord I :: ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 9) out (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨3061⟩
      (flowWadWord σ I out :: ⟨0⟩ ::
        flowVatIlksRateWord out :: flowIlkWord I :: ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 9) out (cA, σ) k' C' := by
  have rd10138pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov)]
  have rd10130pre := rd10138pre.pushConst flowRayWord
    (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
  have rd10138pre := evm_run rd10130pre with [
    raw push2 ⟨10139⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw push2 ⟨10170⟩ (by native_decide) (by evm_ov)]
  have rd10170 := rd10138pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd10180pre := evm_run rd10170 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨10197⟩ (by native_decide) (by evm_ov)]
  have hiszero : UInt256.isZero (flowTagWord σ I) ≠ ⟨0⟩ := by
    rw [htag]
    native_decide
  have rd10197raw := rd10180pre.jumpiT (by native_decide) hiszero
    (by jump_dest) (by evm_ov)
  have rd10197pre := evm_run (rd10197raw.jumpdest (by native_decide) (by evm_ov)) with [
    raw push2 ⟨10108⟩ (by native_decide) (by evm_ov)]
  have rd10108 := rd10197pre.jumpiT (by native_decide) hiszero
    (by jump_dest) (by evm_ov)
  have rd10113pre := evm_run (rd10108.jumpdest (by native_decide) (by evm_ov)) with [
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  obtain ⟨k10139, C10139, rd10139⟩ :
      ∃ k10139 C10139, RD endBytecode I g s0 ⟨10139⟩
        (⟨0⟩ :: flowRayWord :: ⟨0⟩ :: flowTagWord σ I ::
          flowWad0Word σ I out :: ⟨3061⟩ :: ⟨0⟩ ::
          flowVatIlksRateWord out :: flowIlkWord I :: ⟨562⟩ :: [sel])
        mem (UInt256.ofNat 9) out (cA, σ) k10139 C10139 := by
    exact ⟨_, _, by simpa [htag] using
      rd10113pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩
  have rd10145pre := evm_run rd10139 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨10146⟩ (by native_decide) (by evm_ov)]
  have hrayNonzero : flowRayWord ≠ ⟨0⟩ := by native_decide
  have rd10146raw := rd10145pre.jumpiT (by native_decide) hrayNonzero
    (by jump_dest) (by evm_ov)
  have rd10153pre := evm_run (rd10146raw.jumpdest (by native_decide) (by evm_ov)) with [
    raw div (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    rw [flowWadWord_eq_zero_of_tag_zero σ I out htag]
    simpa [htag] using
      rd10153pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem RD.endFlowSecondRmulOverflowReverts
    {cA σ I} {g : Sat256} {s0 : State} {out mem : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (hdivne :
      UInt256.div (flowWadMulWord σ I out) (flowTagWord σ I) ≠
        flowWad0Word σ I out)
    (htag : flowTagWord σ I ≠ ⟨0⟩)
    (h : RD endBytecode I g s0 ⟨10114⟩
      (flowTagWord σ I :: flowWad0Word σ I out :: ⟨3061⟩ :: ⟨0⟩ ::
        flowVatIlksRateWord out :: flowIlkWord I :: ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 9) out (cA, σ) k C) :
    RDrev endBytecode g s0 := by
  have rd10138pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov)]
  have rd10130pre := rd10138pre.pushConst flowRayWord
    (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
  have rd10138pre := evm_run rd10130pre with [
    raw push2 ⟨10139⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw push2 ⟨10170⟩ (by native_decide) (by evm_ov)]
  have rd10170 := rd10138pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd10180pre := evm_run rd10170 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨10197⟩ (by native_decide) (by evm_ov)]
  rw [isZero_eq_zero_of_ne htag] at rd10180pre
  have rd10182pre := evm_run
      (rd10180pre.jumpiNT (by native_decide) rfl (by evm_ov)) with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd10192pre := evm_run rd10182pre with [
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨10194⟩ (by native_decide) (by evm_ov)]
  have rd10194raw := rd10192pre.jumpiT (by native_decide) htag
    (by jump_dest) (by evm_ov)
  have rd10197pre := evm_run (rd10194raw.jumpdest (by native_decide) (by evm_ov)) with [
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨10108⟩ (by native_decide) (by evm_ov)]
  have heqZero :
      UInt256.eq
          (UInt256.div (flowWadMulWord σ I out) (flowTagWord σ I))
          (flowWad0Word σ I out) = ⟨0⟩ :=
    u256_eq_of_ne hdivne
  rw [heqZero] at rd10197pre
  have rd10202 := rd10197pre.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.uniswapPush1Dup1Revert0 rd10202
    (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

theorem RD.endFlowSecondRmulOutcome
    {cA σ I} {g : Sat256} {s0 : State} {out mem : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (h : RD endBytecode I g s0 ⟨10114⟩
      (flowTagWord σ I :: flowWad0Word σ I out :: ⟨3061⟩ :: ⟨0⟩ ::
        flowVatIlksRateWord out :: flowIlkWord I :: ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 9) out (cA, σ) k C) :
    (∃ k' C', RD endBytecode I g s0 ⟨3061⟩
      (flowWadWord σ I out :: ⟨0⟩ ::
        flowVatIlksRateWord out :: flowIlkWord I :: ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 9) out (cA, σ) k' C') ∨ RDrev endBytecode g s0 := by
  by_cases htag : flowTagWord σ I = ⟨0⟩
  · exact Or.inl (RD.endFlowSecondRmulTagZero htag h)
  · by_cases hfit : (flowWad0Word σ I out).toNat * (flowTagWord σ I).toNat < UInt256.size
    · exact Or.inl (RD.endFlowSecondRmulOk hfit htag h)
    · have hover :
          UInt256.size ≤ (flowWad0Word σ I out).toNat * (flowTagWord σ I).toNat :=
        Nat.le_of_not_gt hfit
      have hdivne :
          UInt256.div (flowWadMulWord σ I out) (flowTagWord σ I) ≠
            flowWad0Word σ I out := by
        simpa [flowWadMulWord] using
          flow_udiv_mul_wrap_ne_of_overflow
            (a := flowWad0Word σ I out) (b := flowTagWord σ I) hover
      exact Or.inr (RD.endFlowSecondRmulOverflowReverts hdivne htag h)

theorem RD.endFlowToSub
    {cA σ I} {g : Sat256} {s0 : State} {base out : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (hbase : base.size = 96) (hlong : 160 ≤ out.size) (hout : out.size < UInt256.size)
    (h : RD endBytecode I g s0 ⟨3061⟩
      (flowWadWord σ I out :: ⟨0⟩ ::
        flowVatIlksRateWord out :: flowIlkWord I :: ⟨562⟩ :: [sel])
      (twoWordHashMem (flowIlkWord I) ⟨12⟩
        (twoWordHashMem (flowIlkWord I) ⟨14⟩ (flowVatIlksPostCallMem I base out)))
      (UInt256.ofNat 9) out (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨10154⟩
      (flowGapWord σ I :: flowWadWord σ I out :: ⟨3119⟩ :: ⟨3137⟩ ::
        flowDenWord σ I :: flowWadWord σ I out :: flowVatIlksRateWord out ::
        flowIlkWord I :: ⟨562⟩ :: [sel])
      (twoWordHashMem (flowIlkWord I) ⟨13⟩
        (twoWordHashMem (flowIlkWord I) ⟨12⟩
          (twoWordHashMem (flowIlkWord I) ⟨14⟩ (flowVatIlksPostCallMem I base out))))
      (UInt256.ofNat 9) out (cA, σ) k' C' := by
  have hpostSize : (flowVatIlksPostCallMem I base out).size = 288 :=
    flowVatIlksPostCallMem_size_long I base out hbase hlong hout
  have hmem14Size :
      (twoWordHashMem (flowIlkWord I) ⟨14⟩
        (flowVatIlksPostCallMem I base out)).size = 288 := by
    rw [flow_twoWordHashMem_size_of_ge64]
    · rw [hpostSize]
    · rw [hpostSize]
      omega
  have hmem12Size :
      (twoWordHashMem (flowIlkWord I) ⟨12⟩
        (twoWordHashMem (flowIlkWord I) ⟨14⟩
          (flowVatIlksPostCallMem I base out))).size = 288 := by
    rw [flow_twoWordHashMem_size_of_ge64]
    · rw [hmem14Size]
    · rw [hmem14Size]
      omega
  have hslot :
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC ((twoWordHashMem (flowIlkWord I) ⟨13⟩
              (twoWordHashMem (flowIlkWord I) ⟨12⟩
                (twoWordHashMem (flowIlkWord I) ⟨14⟩
                  (flowVatIlksPostCallMem I base out)))).readWithPadding 0 64))) =
        flowGapStorageSlot I := by
    rw [flow_twoWordHashMem_solcMappingSlot_of_ge64 ⟨13⟩ (flowIlkWord I)
      (by rw [hmem12Size]; omega)]
    rfl
  have rd3084pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd3077pre := rd3084pre.pushConst flowRayWord
    (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
  obtain ⟨k3080, C3080, rd3080raw⟩ := (evm_run rd3077pre with [
    raw push1 ⟨11⟩ (by native_decide) (by evm_ov)]).sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3084pre := evm_run rd3080raw with [
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨3086⟩ (by native_decide) (by evm_ov)]
  have hrayNonzero : flowRayWord ≠ ⟨0⟩ := by native_decide
  have rd3086 := rd3084pre.jumpiT (by native_decide) hrayNonzero
    (by jump_dest) (by evm_ov)
  have rd3099pre := evm_run (rd3086.jumpdest (by native_decide) (by evm_ov)) with [
    raw div (by native_decide) (by evm_ov),
    raw push2 ⟨3137⟩ (by native_decide) (by evm_ov),
    raw push2 ⟨3119⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw push1 ⟨13⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup9 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3113pre := evm_run rd3099pre with [
    raw mstore 0
      (wordAt0Mem (flowIlkWord I)
        (twoWordHashMem (flowIlkWord I) ⟨12⟩
          (twoWordHashMem (flowIlkWord I) ⟨14⟩ (flowVatIlksPostCallMem I base out))))
      (UInt256.ofNat 9) (by native_decide) mem_cost (by simp [wordAt0Mem])
      (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0
      (twoWordHashMem (flowIlkWord I) ⟨13⟩
        (twoWordHashMem (flowIlkWord I) ⟨12⟩
          (twoWordHashMem (flowIlkWord I) ⟨14⟩ (flowVatIlksPostCallMem I base out))))
      (UInt256.ofNat 9) (by native_decide) mem_cost
      (by
        rw [show ((⟨32⟩ : UInt256) + ⟨0⟩).toNat = 32 from by native_decide]
        simp [twoWordHashMem, wordAt32Mem])
      (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov)]
  have rd3113hash := rd3113pre.keccak256 0 (flowGapStorageSlot I)
    (UInt256.ofNat 9) (by native_decide) mem_cost hslot (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨k3115, C3115, rd3115raw⟩ := rd3113hash.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3118 := evm_run rd3115raw with [
    raw push2 ⟨10154⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [flowGapWord, flowGapStorageSlot, flowDenWord, flowDebtWord, endSlotWord,
      solcSlotWord] using rd3118.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem RD.endFlowSubOk
    {cA σ I} {g : Sat256} {s0 : State} {out mem : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (hle : (flowGapWord σ I).toNat ≤ (flowWadWord σ I out).toNat)
    (h : RD endBytecode I g s0 ⟨10154⟩
      (flowGapWord σ I :: flowWadWord σ I out :: ⟨3119⟩ :: ⟨3137⟩ ::
        flowDenWord σ I :: flowWadWord σ I out :: flowVatIlksRateWord out ::
        flowIlkWord I :: ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 9) out (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨3119⟩
      (flowNum0Word σ I out :: ⟨3137⟩ :: flowDenWord σ I ::
        flowWadWord σ I out :: flowVatIlksRateWord out :: flowIlkWord I ::
        ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 9) out (cA, σ) k' C' := by
  have hsubNat :
      (flowNum0Word σ I out).toNat =
        (flowWadWord σ I out).toNat - (flowGapWord σ I).toNat := by
    simpa [flowNum0Word] using
      usub_toNat (a := flowWadWord σ I out) (b := flowGapWord σ I) hle
  have hgt : UInt256.gt (flowNum0Word σ I out) (flowWadWord σ I out) = ⟨0⟩ :=
    ugt_zero (by rw [hsubNat]; omega)
  have rd10165pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov)]
  rw [hgt] at rd10165pre
  have rd10165pre := evm_run rd10165pre with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨10108⟩ (by native_decide) (by evm_ov)]
  have hiszero : UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ := by native_decide
  rw [hiszero] at rd10165pre
  have rd10108 := rd10165pre.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)
  have rd3119 := evm_run (rd10108.jumpdest (by native_decide) (by evm_ov)) with [
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by simpa [flowNum0Word] using rd3119⟩

theorem RD.endFlowSubUnderflowReverts
    {cA σ I} {g : Sat256} {s0 : State} {out mem : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (hlt : (flowWadWord σ I out).toNat < (flowGapWord σ I).toNat)
    (h : RD endBytecode I g s0 ⟨10154⟩
      (flowGapWord σ I :: flowWadWord σ I out :: ⟨3119⟩ :: ⟨3137⟩ ::
        flowDenWord σ I :: flowWadWord σ I out :: flowVatIlksRateWord out ::
        flowIlkWord I :: ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 9) out (cA, σ) k C) :
    RDrev endBytecode g s0 := by
  have hsubNat :
      (flowNum0Word σ I out).toNat =
        UInt256.size + (flowWadWord σ I out).toNat - (flowGapWord σ I).toNat := by
    simpa [flowNum0Word] using
      usub_toNat_underflow (a := flowWadWord σ I out) (b := flowGapWord σ I) hlt
  have hgt : UInt256.gt (flowNum0Word σ I out) (flowWadWord σ I out) = ⟨1⟩ := by
    show UInt256.fromBool (decide (flowNum0Word σ I out > flowWadWord σ I out)) = ⟨1⟩
    rw [decide_eq_true]
    · rfl
    · show (flowNum0Word σ I out).toNat > (flowWadWord σ I out).toNat
      rw [hsubNat]
      have hgap : (flowGapWord σ I).toNat < UInt256.size := (flowGapWord σ I).val.isLt
      omega
  have rd10165pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov)]
  rw [hgt] at rd10165pre
  have rd10165pre := evm_run rd10165pre with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨10108⟩ (by native_decide) (by evm_ov)]
  have hiszero : UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ := by native_decide
  rw [hiszero] at rd10165pre
  have rd10166 := rd10165pre.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.uniswapPush1Dup1Revert0 rd10166
    (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

theorem RD.endFlowSubOutcome
    {cA σ I} {g : Sat256} {s0 : State} {out mem : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (h : RD endBytecode I g s0 ⟨10154⟩
      (flowGapWord σ I :: flowWadWord σ I out :: ⟨3119⟩ :: ⟨3137⟩ ::
        flowDenWord σ I :: flowWadWord σ I out :: flowVatIlksRateWord out ::
        flowIlkWord I :: ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 9) out (cA, σ) k C) :
    (∃ k' C', RD endBytecode I g s0 ⟨3119⟩
      (flowNum0Word σ I out :: ⟨3137⟩ :: flowDenWord σ I ::
        flowWadWord σ I out :: flowVatIlksRateWord out :: flowIlkWord I ::
        ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 9) out (cA, σ) k' C') ∨ RDrev endBytecode g s0 := by
  by_cases hle : (flowGapWord σ I).toNat ≤ (flowWadWord σ I out).toNat
  · exact Or.inl (RD.endFlowSubOk hle h)
  · exact Or.inr (RD.endFlowSubUnderflowReverts (Nat.lt_of_not_ge hle) h)

theorem RD.endFlowMulOk
    {cA σ I} {g : Sat256} {s0 : State} {out mem : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (hmul : (flowNum0Word σ I out).toNat * flowRayWord.toNat < UInt256.size)
    (h : RD endBytecode I g s0 ⟨3119⟩
      (flowNum0Word σ I out :: ⟨3137⟩ :: flowDenWord σ I ::
        flowWadWord σ I out :: flowVatIlksRateWord out :: flowIlkWord I ::
        ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 9) out (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨3137⟩
      (flowNumWord σ I out :: flowDenWord σ I :: flowWadWord σ I out ::
        flowVatIlksRateWord out :: flowIlkWord I :: ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 9) out (cA, σ) k' C' := by
  have rd3136pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov)]
  have rd3133pre := rd3136pre.pushConst flowRayWord
    (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
  have rd10170 := (evm_run rd3133pre with [
    raw push2 ⟨10170⟩ (by native_decide) (by evm_ov)]).jump
    (by native_decide) (by jump_dest) (by evm_ov)
  have rd10180pre := evm_run rd10170 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨10197⟩ (by native_decide) (by evm_ov)]
  have hrayNonzero : flowRayWord ≠ ⟨0⟩ := by native_decide
  rw [isZero_eq_zero_of_ne hrayNonzero] at rd10180pre
  have rd10182pre := evm_run
      (rd10180pre.jumpiNT (by native_decide) rfl (by evm_ov)) with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd10192pre := evm_run rd10182pre with [
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨10194⟩ (by native_decide) (by evm_ov)]
  have rd10194raw := rd10192pre.jumpiT (by native_decide) hrayNonzero
    (by jump_dest) (by evm_ov)
  have rd10197pre := evm_run (rd10194raw.jumpdest (by native_decide) (by evm_ov)) with [
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨10108⟩ (by native_decide) (by evm_ov)]
  have hdiv :
      UInt256.div (flowNumWord σ I out) flowRayWord = flowNum0Word σ I out := by
    simpa [flowNumWord] using
      flow_mul_div_right_cancel (x := flowNum0Word σ I out) (y := flowRayWord)
        hmul hrayNonzero
  rw [hdiv, u256_eq_refl] at rd10197pre
  have rd10108 := rd10197pre.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)
  have rd3137 := evm_run (rd10108.jumpdest (by native_decide) (by evm_ov)) with [
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by simpa [flowNumWord] using rd3137⟩

theorem RD.endFlowMulOverflowReverts
    {cA σ I} {g : Sat256} {s0 : State} {out mem : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (hdivne : UInt256.div (flowNumWord σ I out) flowRayWord ≠ flowNum0Word σ I out)
    (h : RD endBytecode I g s0 ⟨3119⟩
      (flowNum0Word σ I out :: ⟨3137⟩ :: flowDenWord σ I ::
        flowWadWord σ I out :: flowVatIlksRateWord out :: flowIlkWord I ::
        ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 9) out (cA, σ) k C) :
    RDrev endBytecode g s0 := by
  have rd3136pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov)]
  have rd3133pre := rd3136pre.pushConst flowRayWord
    (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
  have rd10170 := (evm_run rd3133pre with [
    raw push2 ⟨10170⟩ (by native_decide) (by evm_ov)]).jump
    (by native_decide) (by jump_dest) (by evm_ov)
  have rd10180pre := evm_run rd10170 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨10197⟩ (by native_decide) (by evm_ov)]
  have hrayNonzero : flowRayWord ≠ ⟨0⟩ := by native_decide
  rw [isZero_eq_zero_of_ne hrayNonzero] at rd10180pre
  have rd10182pre := evm_run
      (rd10180pre.jumpiNT (by native_decide) rfl (by evm_ov)) with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd10192pre := evm_run rd10182pre with [
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨10194⟩ (by native_decide) (by evm_ov)]
  have rd10194raw := rd10192pre.jumpiT (by native_decide) hrayNonzero
    (by jump_dest) (by evm_ov)
  have rd10197pre := evm_run (rd10194raw.jumpdest (by native_decide) (by evm_ov)) with [
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨10108⟩ (by native_decide) (by evm_ov)]
  have heqZero :
      UInt256.eq (UInt256.div (flowNumWord σ I out) flowRayWord)
          (flowNum0Word σ I out) = ⟨0⟩ :=
    u256_eq_of_ne hdivne
  rw [heqZero] at rd10197pre
  have rd10202 := rd10197pre.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.uniswapPush1Dup1Revert0 rd10202
    (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

theorem RD.endFlowMulOutcome
    {cA σ I} {g : Sat256} {s0 : State} {out mem : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (h : RD endBytecode I g s0 ⟨3119⟩
      (flowNum0Word σ I out :: ⟨3137⟩ :: flowDenWord σ I ::
        flowWadWord σ I out :: flowVatIlksRateWord out :: flowIlkWord I ::
        ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 9) out (cA, σ) k C) :
    (∃ k' C', RD endBytecode I g s0 ⟨3137⟩
      (flowNumWord σ I out :: flowDenWord σ I :: flowWadWord σ I out ::
        flowVatIlksRateWord out :: flowIlkWord I :: ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 9) out (cA, σ) k' C') ∨ RDrev endBytecode g s0 := by
  by_cases hfit : (flowNum0Word σ I out).toNat * flowRayWord.toNat < UInt256.size
  · exact Or.inl (RD.endFlowMulOk hfit h)
  · have hover : UInt256.size ≤ (flowNum0Word σ I out).toNat * flowRayWord.toNat :=
      Nat.le_of_not_gt hfit
    have hdivne :
        UInt256.div (flowNumWord σ I out) flowRayWord ≠ flowNum0Word σ I out := by
      simpa [flowNumWord] using
        flow_udiv_mul_wrap_ne_of_overflow (a := flowNum0Word σ I out) (b := flowRayWord) hover
    exact Or.inr (RD.endFlowMulOverflowReverts hdivne h)

theorem RD.endFlowFinishOk
    {cA σ I} {g : Sat256} {s0 : State} {out mem : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (hmem : mem.size = 288)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hden : flowDenWord σ I ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (h : RD endBytecode I g s0 ⟨3137⟩
      (flowNumWord σ I out :: flowDenWord σ I :: flowWadWord σ I out ::
        flowVatIlksRateWord out :: flowIlkWord I :: ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 9) out (cA, σ) k C) :
    RDret endBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ (flowFixStorageSlot I) (flowFixVWord σ I out))
      ByteArray.empty := by
  let fixHashMem := twoWordHashMem (flowIlkWord I) ⟨15⟩ mem
  have hfixHashSize : fixHashMem.size = 288 := by
    simp only [fixHashMem]
    rw [flow_twoWordHashMem_size_of_ge64]
    · exact hmem
    · rw [hmem]
      omega
  have hfixHashRead64 : fixHashMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [fixHashMem] using
      flow_twoWordHashMem_read64_of_ge96 (flowIlkWord I) ⟨15⟩
        (by rw [hmem]; omega) hread64
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (fixHashMem.readWithPadding 0 64))) =
        flowFixStorageSlot I := by
    simp [fixHashMem]
    rw [flow_twoWordHashMem_solcMappingSlot_of_ge64 ⟨15⟩ (flowIlkWord I)
      (by rw [hmem]; omega)]
    exact (flowFixStorageSlot_eq I).symm
  have rd3142pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨3144⟩ (by native_decide) (by evm_ov)]
  have rd3144 := rd3142pre.jumpiT (by native_decide) hden (by jump_dest) (by evm_ov)
  have rd3159pre := evm_run (rd3144.jumpdest (by native_decide) (by evm_ov)) with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (flowIlkWord I) mem) (UInt256.ofNat 9)
      (by native_decide) mem_cost (by simp [wordAt0Mem])
      (by native_decide) (by evm_ov),
    raw push1 ⟨15⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 fixHashMem (UInt256.ofNat 9)
      (by native_decide) mem_cost
      (by
        simp [fixHashMem, twoWordHashMem, wordAt32Mem,
          show (⟨32⟩ : UInt256).toNat = 32 from by native_decide])
      (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have rd3159 := rd3159pre.keccak256 0 (flowFixStorageSlot I)
    (UInt256.ofNat 9) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  have rd3166pre := evm_run rd3159 with [
    raw swap4 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov)]
  obtain ⟨k3167, C3167, rd3167raw⟩ := rd3166pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3168 := RD.mload 0 ⟨128⟩ (UInt256.ofNat 9) rd3167raw
    (by native_decide) mem_cost
    (mloadFreePtrValue (by rw [hfixHashSize]; native_decide) (by native_decide)
      hfixHashRead64)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3169pre := evm_run rd3168 with [
    raw dup5 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rd3203 := rd3169pre.pushConst
    (⟨63827977585573569474348720848380247407041946779543834505461049562835167925584⟩ :
      UInt256)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd3204pre := evm_run rd3203 with [
    raw swap2 (by native_decide) (by evm_ov)]
  have rd3205 := RD.log2
    (a := ⟨128⟩) (b := ⟨0⟩)
    (c := ⟨63827977585573569474348720848380247407041946779543834505461049562835167925584⟩)
    (d := flowIlkWord I)
    (t := [flowWadWord σ I out, flowVatIlksRateWord out, flowIlkWord I, ⟨562⟩, sel])
    0
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat 9).toNat (⟨128⟩ : UInt256).toNat
        (⟨0⟩ : UInt256).toNat))
    (by simpa using rd3204pre)
    (by native_decide) hperm mem_cost (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3208pre := evm_run rd3205 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd563 := rd3208pre.jumpdest (by native_decide) (by evm_ov)
  simpa [flowFixVWord] using RD.stop rd563 (by native_decide) (by evm_ov)

theorem endFlowSourceBodyDebtZeroReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hdebt : flowDebtWord σ I = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (flowStore I) flowTransition.body .reverted := by
  intro evm0
  refine ExecFuncBody.execBlockRevert ?_
  simpa [flowTransition, nonpayable, flowDebtWord, endSlotWord, initState,
    Solm.EVM.storageLoad, State.lookupAccount] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := flowStore I })
      (evm := evm0)
      (guard := .binary .ne (.storage debtRef) (.intLit 0))
      (rest := [ .require (.binary .eq (.storage (fixRef (.var "ilk"))) (.intLit 0)) ] ++
        checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"] "vatIlk" ++
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
          .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
          .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
          .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
          .internalCall "mul" [.var "num0", .intLit RAY] "num",
          .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
          .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
          .assign .storage (fixRef (.var "ilk")) (.var "fixV") ])
      (by simp [evm0, initState]; exact hwv)
      (by
        have hload0 :
            Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩ := by
          simpa [flowDebtWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
            State.lookupAccount] using hdebt
        have hstorage :
            evalExpr? config { contract := contract, locals := flowStore I } evm0
              (.storage debtRef) = .ok (.int 0) := by
          rw [evalExpr_storage_scalar_value
            (cfg := config)
            (solm := { contract := contract, locals := flowStore I })
            (slot := debtRef)
            (er := ({ base := "debt", steps := [] } : EvaledStorageRef))
            (t := .int uint256Int)
            (loc := wordLoc ⟨11⟩)
            (value := .int 0)
            (hbase := by simp [flowStore, debtRef])
            (her := by simp [evalStorageRef, evalStorageRefSteps, debtRef, EvalResult.bind, pure, bind])
            (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
            (hloc := by rfl)
            (hload := by simp [endStorageLocLoad_uint256 evm0 ⟨11⟩, hload0])]
        simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure, evalBinaryOp?]
        native_decide)

theorem endFlowSourceBodyFixNonzeroReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hdebt : flowDebtWord σ I ≠ ⟨0⟩)
    (hfix : flowFixWord σ I ≠ ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (flowStore I) flowTransition.body .reverted := by
  intro evm0
  have hdebtGuard :
      evalExpr? config { contract := contract, locals := flowStore I } evm0
        (.binary .ne (.storage debtRef) (.intLit 0)) = .ok (.bool true) := by
    have hstorage :
        evalExpr? config { contract := contract, locals := flowStore I } evm0
          (.storage debtRef) =
          .ok (.int (Int.ofNat (flowDebtWord σ I).toNat)) := by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := flowStore I })
        (slot := debtRef)
        (er := ({ base := "debt", steps := [] } : EvaledStorageRef))
        (t := .int uint256Int)
        (loc := wordLoc ⟨11⟩)
        (value := .int (Int.ofNat (flowDebtWord σ I).toNat))
        (hbase := by simp [flowStore, debtRef])
        (her := by simp [evalStorageRef, evalStorageRefSteps, debtRef, EvalResult.bind, pure, bind])
        (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
        (hloc := by rfl)
        (hload := by
          simpa [flowDebtWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
            State.lookupAccount] using endStorageLocLoad_uint256 evm0 ⟨11⟩)]
    have hne : (Value.int (Int.ofNat (flowDebtWord σ I).toNat) == Value.int 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro hbad
      rw [Value.int.injEq] at hbad
      exact hdebt (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
    simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure, evalBinaryOp?, hne, Bool.not_false]
  have hfixStorage :
      evalExpr? config { contract := contract, locals := flowStore I } evm0
        (.storage (fixRef (.var "ilk"))) =
        .ok (.int (Int.ofNat (flowFixWord σ I).toNat)) := by
    simpa [flowFixWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_flowFixStorage (evm := evm0) (locals := flowStore I)
        (by simp [flowStore])
        (by
          unfold flowStore flowIlkValue
          rw [Std.HashMap.getElem?_insert]
          have henv : evm0.executionEnv = I := by simp [evm0, initState]
          rw [henv]
          simp)
  have hzero :
      evalExpr? config { contract := contract, locals := flowStore I } evm0 (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hfixGuard :
      evalExpr? config { contract := contract, locals := flowStore I } evm0
        (.binary .eq (.storage (fixRef (.var "ilk"))) (.intLit 0)) = .ok (.bool false) := by
    have hne : (Value.int (Int.ofNat (flowFixWord σ I).toNat) == Value.int 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro hbad
      rw [Value.int.injEq] at hbad
      exact hfix (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
    simp only [evalExpr?, hfixStorage, hzero, EvalResult.bind, bind, evalBinaryOp?, hne]
  have hblock :
      ExecBlock config { contract := contract, locals := flowStore I } evm0 flowTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hdebtGuard) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hfixGuard)
  simpa [ExecTransitionBody, evm0, flowTransition, nonpayable, checkedExternalCallStmts] using
    ExecFuncBody.execBlockRevert hblock

theorem endFlowSourceBodyVatNoCodeReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hdebt : flowDebtWord σ I ≠ ⟨0⟩)
    (hfix : flowFixWord σ I = ⟨0⟩)
    (hvatNoCode :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (flowVatMaskedWord σ I) = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (flowStore I) flowTransition.body .reverted := by
  intro evm0
  have hdebtGuard :
      evalExpr? config { contract := contract, locals := flowStore I } evm0
        (.binary .ne (.storage debtRef) (.intLit 0)) = .ok (.bool true) := by
    have hstorage :
        evalExpr? config { contract := contract, locals := flowStore I } evm0
          (.storage debtRef) =
          .ok (.int (Int.ofNat (flowDebtWord σ I).toNat)) := by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := flowStore I })
        (slot := debtRef)
        (er := ({ base := "debt", steps := [] } : EvaledStorageRef))
        (t := .int uint256Int)
        (loc := wordLoc ⟨11⟩)
        (value := .int (Int.ofNat (flowDebtWord σ I).toNat))
        (hbase := by simp [flowStore, debtRef])
        (her := by simp [evalStorageRef, evalStorageRefSteps, debtRef, EvalResult.bind, pure, bind])
        (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
        (hloc := by rfl)
        (hload := by
          simpa [flowDebtWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
            State.lookupAccount] using endStorageLocLoad_uint256 evm0 ⟨11⟩)]
    have hne : (Value.int (Int.ofNat (flowDebtWord σ I).toNat) == Value.int 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro hbad
      rw [Value.int.injEq] at hbad
      exact hdebt (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
    simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure, evalBinaryOp?, hne, Bool.not_false]
  have hfixStorage :
      evalExpr? config { contract := contract, locals := flowStore I } evm0
        (.storage (fixRef (.var "ilk"))) = .ok (.int 0) := by
    have hstorage :
        evalExpr? config { contract := contract, locals := flowStore I } evm0
          (.storage (fixRef (.var "ilk"))) =
          .ok (.int (Int.ofNat (flowFixWord σ I).toNat)) := by
      simpa [flowFixWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
        State.lookupAccount] using
        evalExpr_flowFixStorage (evm := evm0) (locals := flowStore I)
          (by simp [flowStore])
          (by
            unfold flowStore flowIlkValue
            rw [Std.HashMap.getElem?_insert]
            have henv : evm0.executionEnv = I := by simp [evm0, initState]
            rw [henv]
            simp)
    rw [hfix] at hstorage
    simpa using hstorage
  have hzero :
      evalExpr? config { contract := contract, locals := flowStore I } evm0 (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hfixGuard :
      evalExpr? config { contract := contract, locals := flowStore I } evm0
        (.binary .eq (.storage (fixRef (.var "ilk"))) (.intLit 0)) = .ok (.bool true) := by
    simp only [evalExpr?, hfixStorage, hzero, EvalResult.bind, bind, evalBinaryOp?]
    native_decide
  have hvat :
      evalExpr? config { contract := contract, locals := flowStore I } evm0 (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (flowVatMaskedWord σ I).toNat)) := by
    simpa [flowVatMaskedWord, flowVatWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount, u256_land_comm] using
      evalExpr_flowVatStorage (evm := evm0) (locals := flowStore I) (by simp [flowStore])
  have hvatNoCodeNat :
      (UInt256.ofNat
        ((evm0.lookupAccount (AccountAddress.ofNat (flowVatMaskedWord σ I).toNat)).option 0
          (fun acc => acc.code.size))).toNat = 0 := by
    have hnat := congrArg UInt256.toNat hvatNoCode
    simp [Reasoning.Theory.uniswapExtCodeSizeWord, evm0, initState, State.lookupAccount,
      accountAddress_ofUInt256_eq_ofNat_toNat] at hnat ⊢
    cases hfind : σ.find? (AccountAddress.ofNat (flowVatMaskedWord σ I).toNat)
    · native_decide
    · simp [hfind, Option.option, Function.comp] at hnat ⊢
      exact hnat
  have hguard :
      evalExpr? config { contract := contract, locals := flowStore I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_flowVatCodeGuard_false hvat hvatNoCodeNat
  refine ExecFuncBody.execBlockRevert ?_
  simpa [flowTransition, nonpayable, checkedExternalCallStmts] using
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
      simp [evm0, initState]; exact hwv))) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hdebtGuard) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hfixGuard) <|
          ExecBlock.consRevert (ExecStmt.requireFalse hguard)

theorem endFlowSourceBodyVatIlksCallFailure {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVatIlks : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hdebt : flowDebtWord σ I ≠ ⟨0⟩)
    (hfix : flowFixWord σ I = ⟨0⟩)
    (hvatCode :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat (flowVatMaskedWord σ I).toNat)).option 0
          (fun acc => acc.code.size))).toNat ≠ 0)
    (hcallVatIlks :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (flowVatMaskedWord σ I).toNat)) "vatIlks" 0
        [flowIlkValue I] (false, evmVatIlks, out) true) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (flowStore I) flowTransition.body .reverted := by
  intro evm0
  have hdebtGuard :
      evalExpr? config { contract := contract, locals := flowStore I } evm0
        (.binary .ne (.storage debtRef) (.intLit 0)) = .ok (.bool true) := by
    have hstorage :
        evalExpr? config { contract := contract, locals := flowStore I } evm0
          (.storage debtRef) =
          .ok (.int (Int.ofNat (flowDebtWord σ I).toNat)) := by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := flowStore I })
        (slot := debtRef)
        (er := ({ base := "debt", steps := [] } : EvaledStorageRef))
        (t := .int uint256Int)
        (loc := wordLoc ⟨11⟩)
        (value := .int (Int.ofNat (flowDebtWord σ I).toNat))
        (hbase := by simp [flowStore, debtRef])
        (her := by simp [evalStorageRef, evalStorageRefSteps, debtRef, EvalResult.bind, pure, bind])
        (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
        (hloc := by rfl)
        (hload := by
          simpa [flowDebtWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
            State.lookupAccount] using endStorageLocLoad_uint256 evm0 ⟨11⟩)]
    have hne : (Value.int (Int.ofNat (flowDebtWord σ I).toNat) == Value.int 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro hbad
      rw [Value.int.injEq] at hbad
      exact hdebt (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
    simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure, evalBinaryOp?, hne, Bool.not_false]
  have hfixStorage :
      evalExpr? config { contract := contract, locals := flowStore I } evm0
        (.storage (fixRef (.var "ilk"))) = .ok (.int 0) := by
    have hstorage :
        evalExpr? config { contract := contract, locals := flowStore I } evm0
          (.storage (fixRef (.var "ilk"))) =
          .ok (.int (Int.ofNat (flowFixWord σ I).toNat)) := by
      simpa [flowFixWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
        State.lookupAccount] using
        evalExpr_flowFixStorage (evm := evm0) (locals := flowStore I)
          (by simp [flowStore])
          (by
            unfold flowStore flowIlkValue
            rw [Std.HashMap.getElem?_insert]
            have henv : evm0.executionEnv = I := by simp [evm0, initState]
            rw [henv]
            simp)
    rw [hfix] at hstorage
    simpa using hstorage
  have hzero :
      evalExpr? config { contract := contract, locals := flowStore I } evm0 (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hfixGuard :
      evalExpr? config { contract := contract, locals := flowStore I } evm0
        (.binary .eq (.storage (fixRef (.var "ilk"))) (.intLit 0)) = .ok (.bool true) := by
    simp only [evalExpr?, hfixStorage, hzero, EvalResult.bind, bind, evalBinaryOp?]
    native_decide
  have hvat :
      evalExpr? config { contract := contract, locals := flowStore I } evm0 (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (flowVatMaskedWord σ I).toNat)) := by
    simpa [flowVatMaskedWord, flowVatWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount, u256_land_comm] using
      evalExpr_flowVatStorage (evm := evm0) (locals := flowStore I) (by simp [flowStore])
  have hguard :
      evalExpr? config { contract := contract, locals := flowStore I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_flowVatCodeGuard_true hvat hvatCode
  have hargsVatIlks :
      evalExprs? config { contract := contract, locals := flowStore I } evm0 [.var "ilk"] =
        .ok [flowIlkValue I] := by
    simp [evalExprs?, evalExpr?, flowStore, EvalResult.ofOption, EvalResult.bind, bind, pure]
  have hcallStmt :
      ExecStmt config { contract := contract, locals := flowStore I } evm0
        (.externalCall (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk" (perm := true)) .reverted := by
    exact ExecStmt.externalCallFailure hvat (by simp [evalExpr?, pure]) hargsVatIlks
      hcallVatIlks
  have hblock :
      ExecBlock config { contract := contract, locals := flowStore I } evm0 flowTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hdebtGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hfixGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert hcallStmt
  simpa [ExecTransitionBody, evm0, flowTransition, nonpayable, checkedExternalCallStmts] using
    ExecFuncBody.execBlockRevert hblock

theorem endFlowSourceBodyVatIlksDecodeRevert {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVatIlks : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hdebt : flowDebtWord σ I ≠ ⟨0⟩)
    (hfix : flowFixWord σ I = ⟨0⟩)
    (hvatCode :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat (flowVatMaskedWord σ I).toNat)).option 0
          (fun acc => acc.code.size))).toNat ≠ 0)
    (hcallVatIlks :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (flowVatMaskedWord σ I).toNat)) "vatIlks" 0
        [flowIlkValue I] (true, evmVatIlks, out) true)
    (hdec : config.externalABI.decode? "vatIlks" out = none) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (flowStore I) flowTransition.body .reverted := by
  intro evm0
  have hdebtGuard :
      evalExpr? config { contract := contract, locals := flowStore I } evm0
        (.binary .ne (.storage debtRef) (.intLit 0)) = .ok (.bool true) := by
    have hstorage :
        evalExpr? config { contract := contract, locals := flowStore I } evm0
          (.storage debtRef) =
          .ok (.int (Int.ofNat (flowDebtWord σ I).toNat)) := by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := flowStore I })
        (slot := debtRef)
        (er := ({ base := "debt", steps := [] } : EvaledStorageRef))
        (t := .int uint256Int)
        (loc := wordLoc ⟨11⟩)
        (value := .int (Int.ofNat (flowDebtWord σ I).toNat))
        (hbase := by simp [flowStore, debtRef])
        (her := by simp [evalStorageRef, evalStorageRefSteps, debtRef, EvalResult.bind, pure, bind])
        (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
        (hloc := by rfl)
        (hload := by
          simpa [flowDebtWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
            State.lookupAccount] using endStorageLocLoad_uint256 evm0 ⟨11⟩)]
    have hne : (Value.int (Int.ofNat (flowDebtWord σ I).toNat) == Value.int 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro hbad
      rw [Value.int.injEq] at hbad
      exact hdebt (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
    simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure, evalBinaryOp?, hne, Bool.not_false]
  have hfixStorage :
      evalExpr? config { contract := contract, locals := flowStore I } evm0
        (.storage (fixRef (.var "ilk"))) = .ok (.int 0) := by
    have hstorage :
        evalExpr? config { contract := contract, locals := flowStore I } evm0
          (.storage (fixRef (.var "ilk"))) =
          .ok (.int (Int.ofNat (flowFixWord σ I).toNat)) := by
      simpa [flowFixWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
        State.lookupAccount] using
        evalExpr_flowFixStorage (evm := evm0) (locals := flowStore I)
          (by simp [flowStore])
          (by
            unfold flowStore flowIlkValue
            rw [Std.HashMap.getElem?_insert]
            have henv : evm0.executionEnv = I := by simp [evm0, initState]
            rw [henv]
            simp)
    rw [hfix] at hstorage
    simpa using hstorage
  have hzero :
      evalExpr? config { contract := contract, locals := flowStore I } evm0 (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hfixGuard :
      evalExpr? config { contract := contract, locals := flowStore I } evm0
        (.binary .eq (.storage (fixRef (.var "ilk"))) (.intLit 0)) = .ok (.bool true) := by
    simp only [evalExpr?, hfixStorage, hzero, EvalResult.bind, bind, evalBinaryOp?]
    native_decide
  have hvat :
      evalExpr? config { contract := contract, locals := flowStore I } evm0 (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (flowVatMaskedWord σ I).toNat)) := by
    simpa [flowVatMaskedWord, flowVatWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount, u256_land_comm] using
      evalExpr_flowVatStorage (evm := evm0) (locals := flowStore I) (by simp [flowStore])
  have hguard :
      evalExpr? config { contract := contract, locals := flowStore I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_flowVatCodeGuard_true hvat hvatCode
  have hargsVatIlks :
      evalExprs? config { contract := contract, locals := flowStore I } evm0 [.var "ilk"] =
        .ok [flowIlkValue I] := by
    simp [evalExprs?, evalExpr?, flowStore, EvalResult.ofOption, EvalResult.bind, bind, pure]
  have hcallStmt :
      ExecStmt config { contract := contract, locals := flowStore I } evm0
        (.externalCall (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk" (perm := true)) .reverted := by
    exact ExecStmt.externalCallReturnDecodeRevert hvat (by simp [evalExpr?, pure])
      hargsVatIlks hcallVatIlks hdec
  have hblock :
      ExecBlock config { contract := contract, locals := flowStore I } evm0 flowTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hdebtGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hfixGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert hcallStmt
  simpa [ExecTransitionBody, evm0, flowTransition, nonpayable, checkedExternalCallStmts] using
    ExecFuncBody.execBlockRevert hblock

theorem endFlowBodyCore : endBodyObligation 29 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (endSelBytes 29) rfl hsel
  have hdispatch := endDispatchFlowLocal hsel
  have hreach :=
    endReachFlowBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode := endDecode_flow_ok (I := I) hsz36
    obtain ⟨kRoutine, CRoutine, hroutineRD⟩ :=
      endFlowX_decoded (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := endSelWord I)
        hsz36 hsize hreach
    by_cases hdebt : flowDebtWord σ_evm I = ⟨0⟩
    · have hdebtSolm : flowDebtWord σ_solm I = ⟨0⟩ := by
        have hword : flowDebtWord σ_evm I = flowDebtWord σ_solm I :=
          accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨11⟩ ⟨0⟩
        rw [← hword]
        exact hdebt
      have hbody :
          ExecTransitionBody config contract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (flowStore I)
            flowTransition.body .reverted := by
        simpa using
          endFlowSourceBodyDebtZeroReverts (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hdebtSolm
      exact (endFlowX_debtZero (g := Sat256.ofUInt256 g) hdebt hroutineRD)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · obtain ⟨kFixGuard, CFixGuard, hfixGuardRD⟩ :=
        endFlowX_toFixGuard (g := Sat256.ofUInt256 g) hdebt hroutineRD
      by_cases hfix : flowFixWord σ_evm I = ⟨0⟩
      · obtain ⟨kVat, CVat, hvatRD⟩ :=
          endFlowX_fixZero_toVat (g := Sat256.ofUInt256 g) hfix hfixGuardRD
        by_cases hvatNoCode :
            Reasoning.Theory.uniswapExtCodeSizeWord σ_evm (flowVatMaskedWord σ_evm I) = ⟨0⟩
        · have hdebtSolm : flowDebtWord σ_solm I ≠ ⟨0⟩ := by
            have hword : flowDebtWord σ_evm I = flowDebtWord σ_solm I :=
              accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨11⟩ ⟨0⟩
            intro hzero
            exact hdebt (by rw [hword, hzero])
          have hfixSolm : flowFixWord σ_solm I = ⟨0⟩ := by
            have hword : flowFixWord σ_evm I = flowFixWord σ_solm I :=
              accountMapEquiv_storage_findD hAccounts I.codeOwner (flowFixStorageSlot I) ⟨0⟩
            rw [← hword]
            exact hfix
          have hvatMasked :
              flowVatMaskedWord σ_evm I = flowVatMaskedWord σ_solm I := by
            have hvatWord : flowVatWord σ_evm I = flowVatWord σ_solm I :=
              accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
            change UInt256.land (flowVatWord σ_evm I) solcAddrMask =
              UInt256.land (flowVatWord σ_solm I) solcAddrMask
            rw [hvatWord]
          have hvatNoCodeSolm :
              Reasoning.Theory.uniswapExtCodeSizeWord σ_solm (flowVatMaskedWord σ_solm I) =
                ⟨0⟩ := by
            have hcodeEq :
                Reasoning.Theory.uniswapExtCodeSizeWord σ_evm (flowVatMaskedWord σ_evm I) =
                  Reasoning.Theory.uniswapExtCodeSizeWord σ_solm (flowVatMaskedWord σ_evm I) :=
              uniswapExtCodeSizeWord_accountMapEquiv hAccounts (flowVatMaskedWord σ_evm I)
            rw [← hvatMasked, ← hcodeEq]
            exact hvatNoCode
          have hbody :
              ExecTransitionBody config contract
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (flowStore I)
                flowTransition.body .reverted := by
            exact endFlowSourceBodyVatNoCodeReverts (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hwv hdebtSolm hfixSolm hvatNoCodeSolm
          have hrev := RD.endFlowVatIlksNoCode (g := Sat256.ofUInt256 g) hvatRD hvatNoCode
          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hdebtSolm : flowDebtWord σ_solm I ≠ ⟨0⟩ := by
            have hword : flowDebtWord σ_evm I = flowDebtWord σ_solm I :=
              accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨11⟩ ⟨0⟩
            intro hzero
            exact hdebt (by rw [hword, hzero])
          have hfixSolm : flowFixWord σ_solm I = ⟨0⟩ := by
            have hword : flowFixWord σ_evm I = flowFixWord σ_solm I :=
              accountMapEquiv_storage_findD hAccounts I.codeOwner (flowFixStorageSlot I) ⟨0⟩
            rw [← hword]
            exact hfix
          have hvatMasked :
              flowVatMaskedWord σ_evm I = flowVatMaskedWord σ_solm I := by
            have hvatWord : flowVatWord σ_evm I = flowVatWord σ_solm I :=
              accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
            change UInt256.land (flowVatWord σ_evm I) solcAddrMask =
              UInt256.land (flowVatWord σ_solm I) solcAddrMask
            rw [hvatWord]
          have hvatCodeSolm :
              Reasoning.Theory.uniswapExtCodeSizeWord σ_solm (flowVatMaskedWord σ_solm I) ≠
                ⟨0⟩ := by
            intro hzero
            apply hvatNoCode
            rw [← hvatMasked] at hzero
            rw [← uniswapExtCodeSizeWord_accountMapEquiv hAccounts
              (flowVatMaskedWord σ_evm I)] at hzero
            exact hzero
          have hvatCodeNatSolm :
              (UInt256.ofNat
                (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
                  (AccountAddress.ofNat (flowVatMaskedWord σ_solm I).toNat)).option 0
                  (fun acc => acc.code.size))).toNat ≠ 0 := by
            intro hnat
            apply hvatCodeSolm
            simp [Reasoning.Theory.uniswapExtCodeSizeWord, initState, State.lookupAccount,
              accountAddress_ofUInt256_eq_ofNat_toNat] at hnat ⊢
            cases hfind : σ_solm.find? (AccountAddress.ofNat (flowVatMaskedWord σ_solm I).toNat)
            · native_decide
            · simp [hfind, Option.option, Function.comp] at hnat ⊢
              exact uint256_toNat_eq_zero hnat
          by_cases hdepthMax : I.depth = (1024 : Fin 1025)
          · have hrev :=
              RD.endFlowVatIlksDepthLimitReverts
                (g := Sat256.ofUInt256 g) hvatRD hvatNoCode hdepthMax
            let target :=
              EVM.address (AccountAddress.ofNat (flowVatMaskedWord σ_solm I).toNat)
            have hcallVatIlks :
                typedCallViaEVM config
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  target "vatIlks" 0 [flowIlkValue I]
                  (false,
                    { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                      substate :=
                        ((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).addAccessedAccount
                          target).substate },
                    ByteArray.empty) true := by
              exact callNotMade_depthLimit
                (cfg := config)
                (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (tgt := target)
                (name := "vatIlks")
                (args := [flowIlkValue I])
                (calldata := ilksSelector ++ (flowIlkWord I).toByteArray)
                (callPerm := true)
                (flowVatIlksEncodeWords I)
                (by simpa [initState] using hdepthMax)
            have hbody :
                ExecTransitionBody config contract
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (flowStore I)
                  flowTransition.body .reverted := by
              exact endFlowSourceBodyVatIlksCallFailure (cA := cA) (gh := gh) (bl := bl)
                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hwv hdebtSolm hfixSolm hvatCodeNatSolm hcallVatIlks
            exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · have hdepthLt : I.depth.val < 1024 := by
              have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
              have hne : I.depth.val ≠ 1024 := by
                intro hval
                apply hdepthMax
                apply Fin.ext
                exact hval
              omega
            obtain ⟨cA', σ', z, out, A', kCall, CCall, hcallRD, hcallEvm, houtsz⟩ :=
              RD.endFlowVatIlksPostCall
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                (A := A) (I := I) (g := g) hvatRD hvatNoCode hdepthLt
            cases z
            · have hrev :=
                RD.endFlowVatIlksCallFailure hcallRD houtsz
                  (by simp only [List.length_cons, List.length_nil]; omega)
              obtain ⟨σ'_solm, A'_solm, hcallSolm, hStateVatIlks⟩ :=
                typedCallViaEVM_initState_EVMStateEquiv hcallEvm (by simp [initState])
                  hAccounts
              have hcallVatIlks :
                  typedCallViaEVM config
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    (EVM.address (AccountAddress.ofNat (flowVatMaskedWord σ_solm I).toNat))
                    "vatIlks" 0 [flowIlkValue I]
                    (false,
                      { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                        accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' },
                      out) true := by
                simpa [hvatMasked, hperm] using hcallSolm
              have hbody :
                  ExecTransitionBody config contract
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (flowStore I)
                    flowTransition.body .reverted := by
                exact endFlowSourceBodyVatIlksCallFailure (cA := cA) (gh := gh) (bl := bl)
                  (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  hwv hdebtSolm hfixSolm hvatCodeNatSolm hcallVatIlks
              exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · obtain ⟨kDecode, CDecode, hdecodeRD⟩ :=
                RD.endFlowVatIlksCallSuccessToDecode hcallRD
                  (by simp only [List.length_cons, List.length_nil]; omega)
              by_cases houtShort : out.size < 160
              · have hbase :
                    (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem).size = 96 :=
                  twoWordHashMem_size_96 (flowIlkWord I) ⟨15⟩ solcFreePtrMem_size
                have hread64 :
                    (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem).readWithPadding 64 32 =
                      UInt256.toByteArray ⟨128⟩ :=
                  twoWordHashMem_read64 (flowIlkWord I) ⟨15⟩ solcFreePtrMem_size
                    solcFreePtrMem_read64
                have hrev :=
                  RD.endFlowVatIlksReturnDecodeShortReverts hdecodeRD hbase hread64
                    houtShort houtsz
                obtain ⟨σ'_solm, A'_solm, hcallSolm, hStateVatIlks⟩ :=
                  typedCallViaEVM_initState_EVMStateEquiv hcallEvm (by simp [initState])
                    hAccounts
                have hcallVatIlks :
                    typedCallViaEVM config
                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                      (EVM.address (AccountAddress.ofNat (flowVatMaskedWord σ_solm I).toNat))
                      "vatIlks" 0 [flowIlkValue I]
                      (true,
                        { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                          accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' },
                        out) true := by
                  simpa [hvatMasked, hperm] using hcallSolm
                have hbody :
                    ExecTransitionBody config contract
                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (flowStore I)
                      flowTransition.body .reverted := by
                  exact endFlowSourceBodyVatIlksDecodeRevert (cA := cA) (gh := gh)
                    (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    hwv hdebtSolm hfixSolm hvatCodeNatSolm hcallVatIlks
                    (flowVatIlksDecode_none_short houtShort)
                exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · have houtLong : 160 ≤ out.size := by omega
                have hbase :
                    (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem).size = 96 :=
                  twoWordHashMem_size_96 (flowIlkWord I) ⟨15⟩ solcFreePtrMem_size
                have hread64 :
                    (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem).readWithPadding 64 32 =
                      UInt256.toByteArray ⟨128⟩ :=
                  twoWordHashMem_read64 (flowIlkWord I) ⟨15⟩ solcFreePtrMem_size
                    solcFreePtrMem_read64
                have hdecVatIlks :
                    config.externalABI.decode? "vatIlks" out =
                      some (flowVatIlksReturnValues out) :=
                  flowVatIlksDecode_ok houtLong
                obtain ⟨kRmul0, CRmul0, hRmul0⟩ :=
                  RD.endFlowVatIlksReturnDecodeOkToRmul hdecodeRD hbase hread64
                    houtLong houtsz
                have hSecondOutcome :
                    (∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨10114⟩
                      (flowTagWord σ' I :: flowWad0Word σ' I out :: ⟨3061⟩ :: ⟨0⟩ ::
                        flowVatIlksRateWord out :: flowIlkWord I :: ⟨562⟩ :: [endSelWord I])
                      (twoWordHashMem (flowIlkWord I) ⟨12⟩
                        (twoWordHashMem (flowIlkWord I) ⟨14⟩
                          (flowVatIlksPostCallMem I
                            (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem) out)))
                      (UInt256.ofNat 9) out (cA', σ') k' C') ∨
                    RDrev endBytecode (Sat256.ofUInt256 g)
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
                  rcases RD.endFlowFirstRmulOutcome hRmul0 with hFirstRmulOk | hFirstRmulRev
                  · obtain ⟨kSecond, CSecond, hSecondRmul⟩ := hFirstRmulOk
                    exact Or.inl (RD.endFlowToSecondRmul hbase houtLong houtsz hSecondRmul)
                  · exact Or.inr hFirstRmulRev
                have hAfterSecondOutcome :
                    (∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3061⟩
                      (flowWadWord σ' I out :: ⟨0⟩ ::
                        flowVatIlksRateWord out :: flowIlkWord I :: ⟨562⟩ ::
                          [endSelWord I])
                      (twoWordHashMem (flowIlkWord I) ⟨12⟩
                        (twoWordHashMem (flowIlkWord I) ⟨14⟩
                          (flowVatIlksPostCallMem I
                            (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem) out)))
                      (UInt256.ofNat 9) out (cA', σ') k' C') ∨
                    RDrev endBytecode (Sat256.ofUInt256 g)
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
                  rcases hSecondOutcome with hSecondRmulOk | hSecondRmulRev
                  · obtain ⟨kSecond, CSecond, hSecondRmul⟩ := hSecondRmulOk
                    exact RD.endFlowSecondRmulOutcome hSecondRmul
                  · exact Or.inr hSecondRmulRev
                have hSubOutcome :
                    (∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨10154⟩
                      (flowGapWord σ' I :: flowWadWord σ' I out :: ⟨3119⟩ ::
                        ⟨3137⟩ :: flowDenWord σ' I :: flowWadWord σ' I out ::
                        flowVatIlksRateWord out :: flowIlkWord I :: ⟨562⟩ ::
                          [endSelWord I])
                      (twoWordHashMem (flowIlkWord I) ⟨13⟩
                        (twoWordHashMem (flowIlkWord I) ⟨12⟩
                          (twoWordHashMem (flowIlkWord I) ⟨14⟩
                            (flowVatIlksPostCallMem I
                              (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem) out))))
                      (UInt256.ofNat 9) out (cA', σ') k' C') ∨
                    RDrev endBytecode (Sat256.ofUInt256 g)
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
                  rcases hAfterSecondOutcome with hAfterSecondOk | hAfterSecondRev
                  · obtain ⟨kAfterSecond, CAfterSecond, hAfterSecond⟩ := hAfterSecondOk
                    exact Or.inl (RD.endFlowToSub hbase houtLong houtsz hAfterSecond)
                  · exact Or.inr hAfterSecondRev
                have hAfterSubOutcome :
                    (∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3119⟩
                      (flowNum0Word σ' I out :: ⟨3137⟩ :: flowDenWord σ' I ::
                        flowWadWord σ' I out :: flowVatIlksRateWord out ::
                        flowIlkWord I :: ⟨562⟩ :: [endSelWord I])
                      (twoWordHashMem (flowIlkWord I) ⟨13⟩
                        (twoWordHashMem (flowIlkWord I) ⟨12⟩
                          (twoWordHashMem (flowIlkWord I) ⟨14⟩
                            (flowVatIlksPostCallMem I
                              (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem) out))))
                      (UInt256.ofNat 9) out (cA', σ') k' C') ∨
                    RDrev endBytecode (Sat256.ofUInt256 g)
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
                  rcases hSubOutcome with hSubOk | hSubRev
                  · obtain ⟨kSub, CSub, hSub⟩ := hSubOk
                    exact RD.endFlowSubOutcome hSub
                  · exact Or.inr hSubRev
                have hAfterMulOutcome :
                    (∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3137⟩
                      (flowNumWord σ' I out :: flowDenWord σ' I ::
                        flowWadWord σ' I out :: flowVatIlksRateWord out ::
                        flowIlkWord I :: ⟨562⟩ :: [endSelWord I])
                      (twoWordHashMem (flowIlkWord I) ⟨13⟩
                        (twoWordHashMem (flowIlkWord I) ⟨12⟩
                          (twoWordHashMem (flowIlkWord I) ⟨14⟩
                            (flowVatIlksPostCallMem I
                              (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem) out))))
                      (UInt256.ofNat 9) out (cA', σ') k' C') ∨
                    RDrev endBytecode (Sat256.ofUInt256 g)
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
                  rcases hAfterSubOutcome with hAfterSubOk | hAfterSubRev
                  · obtain ⟨kAfterSub, CAfterSub, hAfterSub⟩ := hAfterSubOk
                    exact RD.endFlowMulOutcome hAfterSub
                  · exact Or.inr hAfterSubRev
                let memFinal :=
                  twoWordHashMem (flowIlkWord I) ⟨13⟩
                    (twoWordHashMem (flowIlkWord I) ⟨12⟩
                      (twoWordHashMem (flowIlkWord I) ⟨14⟩
                        (flowVatIlksPostCallMem I
                          (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem) out)))
                have hpostSize :
                    (flowVatIlksPostCallMem I
                      (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem) out).size = 288 :=
                  flowVatIlksPostCallMem_size_long I
                    (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem) out
                    hbase houtLong houtsz
                have hpostRead64 :
                    ((flowVatIlksPostCallMem I
                      (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem) out)
                        ).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
                  flowVatIlksPostCallMem_read64_long I
                    (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem) out
                    hbase hread64 houtLong houtsz
                have hmem14Size :
                    (twoWordHashMem (flowIlkWord I) ⟨14⟩
                      (flowVatIlksPostCallMem I
                        (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem) out)).size = 288 := by
                  rw [flow_twoWordHashMem_size_of_ge64]
                  · exact hpostSize
                  · rw [hpostSize]; omega
                have hmem14Read64 :
                    ((twoWordHashMem (flowIlkWord I) ⟨14⟩
                      (flowVatIlksPostCallMem I
                        (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem) out))
                        ).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
                  flow_twoWordHashMem_read64_of_ge96 (flowIlkWord I) ⟨14⟩
                    (by rw [hpostSize]; omega) hpostRead64
                have hmem12Size :
                    (twoWordHashMem (flowIlkWord I) ⟨12⟩
                      (twoWordHashMem (flowIlkWord I) ⟨14⟩
                        (flowVatIlksPostCallMem I
                          (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem) out))).size = 288 := by
                  rw [flow_twoWordHashMem_size_of_ge64]
                  · exact hmem14Size
                  · rw [hmem14Size]; omega
                have hmem12Read64 :
                    ((twoWordHashMem (flowIlkWord I) ⟨12⟩
                      (twoWordHashMem (flowIlkWord I) ⟨14⟩
                        (flowVatIlksPostCallMem I
                          (twoWordHashMem (flowIlkWord I) ⟨15⟩ solcFreePtrMem) out)))
                        ).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
                  flow_twoWordHashMem_read64_of_ge96 (flowIlkWord I) ⟨12⟩
                    (by rw [hmem14Size]; omega) hmem14Read64
                have hmemFinalSize : memFinal.size = 288 := by
                  simp only [memFinal]
                  rw [flow_twoWordHashMem_size_of_ge64]
                  · exact hmem12Size
                  · rw [hmem12Size]; omega
                have hmemFinalRead64 :
                    memFinal.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
                  simpa [memFinal] using
                    flow_twoWordHashMem_read64_of_ge96 (flowIlkWord I) ⟨13⟩
                      (by rw [hmem12Size]; omega) hmem12Read64
                have hFinishOk_of_den
                    (hden : flowDenWord σ' I ≠ ⟨0⟩)
                    (hAfterMulOk :
                      ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
                        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3137⟩
                        (flowNumWord σ' I out :: flowDenWord σ' I ::
                          flowWadWord σ' I out :: flowVatIlksRateWord out ::
                          flowIlkWord I :: ⟨562⟩ :: [endSelWord I])
                        memFinal (UInt256.ofNat 9) out (cA', σ') k' C') :
                    RDret endBytecode (Sat256.ofUInt256 g)
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                      (cA', sstoreAccountMap I.codeOwner σ'
                        (flowFixStorageSlot I) (flowFixVWord σ' I out))
                      ByteArray.empty := by
                  obtain ⟨kAfterMul, CAfterMul, hAfterMul⟩ := hAfterMulOk
                  exact RD.endFlowFinishOk hmemFinalSize hmemFinalRead64 hden hperm hAfterMul
                sorry
      · have hdebtSolm : flowDebtWord σ_solm I ≠ ⟨0⟩ := by
          have hword : flowDebtWord σ_evm I = flowDebtWord σ_solm I :=
            accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨11⟩ ⟨0⟩
          intro hzero
          exact hdebt (by rw [hword, hzero])
        have hfixSolm : flowFixWord σ_solm I ≠ ⟨0⟩ := by
          have hword : flowFixWord σ_evm I = flowFixWord σ_solm I :=
            accountMapEquiv_storage_findD hAccounts I.codeOwner (flowFixStorageSlot I) ⟨0⟩
          intro hzero
          exact hfix (by rw [hword, hzero])
        have hbody :
            ExecTransitionBody config contract
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (flowStore I)
              flowTransition.body .reverted := by
          simpa using
            endFlowSourceBodyFixNonzeroReverts (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hdebtSolm hfixSolm
        exact (endFlowX_fixNonzero (g := Sat256.ofUInt256 g) hfix hfixGuardRD)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hshort : I.calldata.size < 36 := by omega
    have hrev :=
      endFlowX_shortarg (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := endSelWord I)
        hsz4 hsize hshort hreach
    exact hrev.reEquivDecodingFailed hcode hdispatch
      (endDecode_flow_none_short hsz4 hshort)

end Benchmarks.Dss.End
