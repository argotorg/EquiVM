import Benchmarks.Dss.End.Flow
import Benchmarks.Dss.End.Free

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `skim(bytes32,address)` transition -/

abbrev endSkimConcreteSelector : ByteArray := selectorBytes 0x89 0xea 0x45 0xd3

abbrev endSkimIlkWord (I : ExecutionEnv) : UInt256 := endBytes32ArgWord I

abbrev endSkimIlkBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev endSkimUrnWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev endSkimUrnKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (endSkimUrnWord I)

abbrev endSkimUrnAddr (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (endSkimUrnWord I).toNat

abbrev endSkimStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "ilk" (.fixedBytes bytes32Width (endSkimIlkBytes I))).insert
    "urn" (.address (endSkimUrnAddr I))

theorem endSkimStore_get_ilk (I : ExecutionEnv) :
    (endSkimStore I).get? "ilk" = some (.fixedBytes bytes32Width (endSkimIlkBytes I)) := by
  rw [endSkimStore, store_get_ne _ _ (by native_decide), store_get_self]

abbrev endSkimIlkKey (I : ExecutionEnv) : KeyValue := endBytes32ArgKey I

abbrev endSkimTagEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "tag", steps := [.mindex (endSkimIlkKey I)] }

abbrev endSkimTagSlot (I : ExecutionEnv) : UInt256 := tagSlot (endSkimIlkKey I)

abbrev endSkimTagWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (endSkimTagSlot I) σ I

abbrev endSkimEntryPc : UInt256 := ⟨851⟩
abbrev endSkimReturnPc : UInt256 := ⟨562⟩
abbrev endSkimDecodedPc : UInt256 := ⟨873⟩
abbrev endSkimBodyPc : UInt256 := ⟨6705⟩

noncomputable def endSkimVatIlksBaseMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (endSkimIlkWord I) ⟨12⟩ solcFreePtrMem

noncomputable def endSkimVatIlksCalldataMem (I : ExecutionEnv) : ByteArray :=
  endFlowVatIlksCalldataMem I (endSkimVatIlksBaseMem I)

noncomputable def endSkimVatIlksPostCallMem (I : ExecutionEnv) (out : ByteArray) :
    ByteArray :=
  out.write 0 (endSkimVatIlksCalldataMem I) endFlowVatIlksOutPtr.toNat
    (min endFlowVatIlksOutSize.toNat out.size)

abbrev endSkimStoreVatIlk (I : ExecutionEnv) (out : ByteArray) : Store :=
  (endSkimStore I).insert "vatIlk"
    (.tuple [.int (Int.ofNat (endFlowVatIlkArtWord out).toNat),
      .int (Int.ofNat (endFlowVatIlkRateWord out).toNat),
      .int (Int.ofNat (endFlowVatIlkSpotWord out).toNat),
      .int (Int.ofNat (endFlowVatIlkLineWord out).toNat),
      .int (Int.ofNat (endFlowVatIlkDustWord out).toNat)])

abbrev endSkimStoreRate (I : ExecutionEnv) (out : ByteArray) : Store :=
  (endSkimStoreVatIlk I out).insert "rate"
    (.int (Int.ofNat (endFlowVatIlkRateWord out).toNat))

noncomputable def endSkimUrnsSelectorMem (I : ExecutionEnv) (vatOut : ByteArray) :
    ByteArray :=
  endFreeUrnsSelectorShifted.toByteArray.write 0 (endSkimVatIlksPostCallMem I vatOut)
    endFreeUrnsOutPtr.toNat 32

noncomputable def endSkimUrnsArg0Mem (I : ExecutionEnv) (vatOut : ByteArray) :
    ByteArray :=
  (endSkimIlkWord I).toByteArray.write 0 (endSkimUrnsSelectorMem I vatOut)
    (endFreeUrnsOutPtr + ⟨4⟩).toNat 32

noncomputable def endSkimUrnsCalldataMem (I : ExecutionEnv) (vatOut : ByteArray) :
    ByteArray :=
  (endSkimUrnKey I).toByteArray.write 0 (endSkimUrnsArg0Mem I vatOut)
    (endFreeUrnsOutPtr + ⟨36⟩).toNat 32

noncomputable def endSkimUrnsPostCallMem (I : ExecutionEnv) (vatOut urnOut : ByteArray) :
    ByteArray :=
  urnOut.write 0 (endSkimUrnsCalldataMem I vatOut) endFreeUrnsOutPtr.toNat
    (min endFreeUrnsOutSize.toNat urnOut.size)

noncomputable def endSkimTagHashMem (I : ExecutionEnv) (vatOut urnOut : ByteArray) :
    ByteArray :=
  twoWordHashMem (endSkimIlkWord I) ⟨12⟩ (endSkimUrnsPostCallMem I vatOut urnOut)

noncomputable def endSkimGapHashMem (I : ExecutionEnv) (vatOut urnOut : ByteArray) :
    ByteArray :=
  twoWordHashMem (endSkimIlkWord I) ⟨13⟩ (endSkimTagHashMem I vatOut urnOut)

noncomputable def endSkimGapStoreHashMem (I : ExecutionEnv) (vatOut urnOut : ByteArray) :
    ByteArray :=
  twoWordHashMem (endSkimIlkWord I) ⟨13⟩ (endSkimGapHashMem I vatOut urnOut)

abbrev endSkimStoreVatUrn (I : ExecutionEnv) (vatOut urnOut : ByteArray) : Store :=
  (endSkimStoreRate I vatOut).insert "vatUrn"
    (.tuple [.int (Int.ofNat (endFreeUrnInkWord urnOut).toNat),
      .int (Int.ofNat (endFreeUrnArtWord urnOut).toNat)])

abbrev endSkimStoreInk (I : ExecutionEnv) (vatOut urnOut : ByteArray) : Store :=
  (endSkimStoreVatUrn I vatOut urnOut).insert "ink"
    (.int (Int.ofNat (endFreeUrnInkWord urnOut).toNat))

abbrev endSkimStoreArt (I : ExecutionEnv) (vatOut urnOut : ByteArray) : Store :=
  (endSkimStoreInk I vatOut urnOut).insert "art"
    (.int (Int.ofNat (endFreeUrnArtWord urnOut).toNat))

abbrev endSkimOwe0Word (vatOut urnOut : ByteArray) : UInt256 :=
  UInt256.div (endFreeUrnArtWord urnOut * endFlowVatIlkRateWord vatOut) endRayWord

abbrev endSkimStoreOwe0 (I : ExecutionEnv) (vatOut urnOut : ByteArray) : Store :=
  (endSkimStoreArt I vatOut urnOut).insert "owe0"
    (.int (Int.ofNat (endSkimOwe0Word vatOut urnOut).toNat))

abbrev endSkimOweWord (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) : UInt256 :=
  UInt256.div (endSkimOwe0Word vatOut urnOut * endSkimTagWord σ I) endRayWord

abbrev endSkimStoreOwe (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) : Store :=
  (endSkimStoreOwe0 I vatOut urnOut).insert "owe"
    (.int (Int.ofNat (endSkimOweWord σ I vatOut urnOut).toNat))

abbrev endSkimWadWord (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) : UInt256 :=
  if (endFreeUrnInkWord urnOut).toNat ≤ (endSkimOweWord σ I vatOut urnOut).toNat then
    endFreeUrnInkWord urnOut
  else
    endSkimOweWord σ I vatOut urnOut

abbrev endSkimStoreWad (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) : Store :=
  (endSkimStoreOwe σ I vatOut urnOut).insert "wad"
    (.int (Int.ofNat (endSkimWadWord σ I vatOut urnOut).toNat))

abbrev endSkimDiffWord (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) : UInt256 :=
  UInt256.sub (endSkimOweWord σ I vatOut urnOut)
    (endSkimWadWord σ I vatOut urnOut)

abbrev endSkimStoreDiff (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) : Store :=
  (endSkimStoreWad σ I vatOut urnOut).insert "diff"
    (.int (Int.ofNat (endSkimDiffWord σ I vatOut urnOut).toNat))

abbrev endSkimGapEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "gap", steps := [.mindex (endSkimIlkKey I)] }

abbrev endSkimGapSlot (I : ExecutionEnv) : UInt256 := gapSlot (endSkimIlkKey I)

abbrev endSkimGapWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (endSkimGapSlot I) σ I

abbrev endSkimGapNewWord (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) : UInt256 :=
  endSkimGapWord σ I + endSkimDiffWord σ I vatOut urnOut

abbrev endSkimStoreGapNew (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) : Store :=
  (endSkimStoreDiff σ I vatOut urnOut).insert "gapNew"
    (.int (Int.ofNat (endSkimGapNewWord σ I vatOut urnOut).toNat))

abbrev endSkimPostGapState (evm : EVM.State) (I : ExecutionEnv)
    (gapNew : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (endSkimGapSlot I) gapNew

def endSkimPostGapAccountMap (σ : AccountMap) (I : ExecutionEnv) (gapNew : UInt256) :
    AccountMap :=
  sstoreAccountMap I.codeOwner σ (endSkimGapSlot I) gapNew

theorem endSkim_storageStore_blocks (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).blocks = evm.blocks := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount, Account.updateStorage]

theorem endSkim_storageStore_genesisBlockHeader (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).genesisBlockHeader = evm.genesisBlockHeader := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount, Account.updateStorage]

theorem endSkim_storageStore_σ₀ (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).σ₀ = evm.σ₀ := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount, Account.updateStorage]

abbrev endSkimStoreGrab (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) : Store :=
  (endSkimStoreGapNew σ I vatOut urnOut).insert "_grab" (collapseReturns [])

abbrev endSkimThisWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.codeOwner.val

abbrev endSkimGrabDinkWord (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) : UInt256 :=
  UInt256.sub ⟨0⟩ (endSkimWadWord σ I vatOut urnOut)

abbrev endSkimGrabDartWord (urnOut : ByteArray) : UInt256 :=
  UInt256.sub ⟨0⟩ (endFreeUrnArtWord urnOut)

def endSkimGrabWrites (σ : AccountMap) (I : ExecutionEnv) (vatOut urnOut : ByteArray) :
    List (Nat × UInt256) :=
  [ (128, endFreeGrabSelectorShifted),
    (132, endSkimIlkWord I),
    (164, endSkimUrnKey I),
    (196, endSkimThisWord I),
    (228, endPackVowWord σ I),
    (260, endSkimGrabDinkWord σ I vatOut urnOut),
    (292, endSkimGrabDartWord urnOut) ]

noncomputable def endSkimGrabCalldataMem (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) : ByteArray :=
  writeCascade (endSkimGapStoreHashMem I vatOut urnOut)
    (endSkimGrabWrites σ I vatOut urnOut)

noncomputable def endSkimGrabMem1 (I : ExecutionEnv) (vatOut urnOut : ByteArray) :
    ByteArray :=
  writeWord (endSkimGapStoreHashMem I vatOut urnOut) 128 endFreeGrabSelectorShifted

noncomputable def endSkimGrabMem2 (I : ExecutionEnv) (vatOut urnOut : ByteArray) :
    ByteArray :=
  writeWord (endSkimGrabMem1 I vatOut urnOut) 132 (endSkimIlkWord I)

noncomputable def endSkimGrabMem3 (I : ExecutionEnv) (vatOut urnOut : ByteArray) :
    ByteArray :=
  writeWord (endSkimGrabMem2 I vatOut urnOut) 164 (endSkimUrnKey I)

noncomputable def endSkimGrabMem4 (I : ExecutionEnv) (vatOut urnOut : ByteArray) :
    ByteArray :=
  writeWord (endSkimGrabMem3 I vatOut urnOut) 196 (endSkimThisWord I)

noncomputable def endSkimGrabMem5 (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) : ByteArray :=
  writeWord (endSkimGrabMem4 I vatOut urnOut) 228 (endPackVowWord σ I)

noncomputable def endSkimGrabMem6 (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) : ByteArray :=
  writeWord (endSkimGrabMem5 σ I vatOut urnOut) 260
    (endSkimGrabDinkWord σ I vatOut urnOut)

noncomputable def endSkimGrabMem7 (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) : ByteArray :=
  writeWord (endSkimGrabMem6 σ I vatOut urnOut) 292
    (endSkimGrabDartWord urnOut)

noncomputable def endSkimGrabPostCallMem (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut ret : ByteArray) : ByteArray :=
  ret.write 0 (endSkimGrabCalldataMem σ I vatOut urnOut)
    endFreeGrabOutPtr.toNat (min endFreeGrabOutSize (UInt256.ofNat ret.size)).toNat

noncomputable def endSkimLogDataMem (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut ret : ByteArray) : ByteArray :=
  (endSkimWadWord σ I vatOut urnOut).toByteArray.write 0
    (endSkimGrabPostCallMem σ I vatOut urnOut ret) 128 32

def endSkimGrabWritesFor (σCall σLoc : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) : List (Nat × UInt256) :=
  [ (128, endFreeGrabSelectorShifted),
    (132, endSkimIlkWord I),
    (164, endSkimUrnKey I),
    (196, endSkimThisWord I),
    (228, endPackVowWord σCall I),
    (260, endSkimGrabDinkWord σLoc I vatOut urnOut),
    (292, endSkimGrabDartWord urnOut) ]

noncomputable def endSkimGrabCalldataMemFor (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (vatOut urnOut : ByteArray) : ByteArray :=
  writeCascade (endSkimGapStoreHashMem I vatOut urnOut)
    (endSkimGrabWritesFor σCall σLoc I vatOut urnOut)

noncomputable def endSkimGrabMem5For (σCall : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) : ByteArray :=
  writeWord (endSkimGrabMem4 I vatOut urnOut) 228 (endPackVowWord σCall I)

noncomputable def endSkimGrabMem6For (σCall σLoc : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) : ByteArray :=
  writeWord (endSkimGrabMem5For σCall I vatOut urnOut) 260
    (endSkimGrabDinkWord σLoc I vatOut urnOut)

noncomputable def endSkimGrabMem7For (σCall σLoc : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) : ByteArray :=
  writeWord (endSkimGrabMem6For σCall σLoc I vatOut urnOut) 292
    (endSkimGrabDartWord urnOut)

noncomputable def endSkimGrabPostCallMemFor (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (vatOut urnOut ret : ByteArray) : ByteArray :=
  ret.write 0 (endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut)
    endFreeGrabOutPtr.toNat (min endFreeGrabOutSize (UInt256.ofNat ret.size)).toNat

noncomputable def endSkimLogDataMemFor (σCall σLoc : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut ret : ByteArray) : ByteArray :=
  (endSkimWadWord σLoc I vatOut urnOut).toByteArray.write 0
    (endSkimGrabPostCallMemFor σCall σLoc I vatOut urnOut ret) 128 32

theorem endSkimTagSlot_eq {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    endSkimTagSlot I = solcMappingSlot ⟨12⟩ (endSkimIlkWord I) := by
  unfold endSkimTagSlot endSkimIlkKey tagSlot mapSlot solcMappingSlot
  rw [endKeyValueToWord_bytes32ArgKey (by omega)]

theorem endSkimGapSlot_eq {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    endSkimGapSlot I = solcMappingSlot ⟨13⟩ (endSkimIlkWord I) := by
  unfold endSkimGapSlot endSkimIlkKey gapSlot mapSlot solcMappingSlot
  rw [endKeyValueToWord_bytes32ArgKey (by omega)]

theorem endSkimVatIlksBaseMem_size (I : ExecutionEnv) :
    (endSkimVatIlksBaseMem I).size = 96 := by
  exact twoWordHashMem_size_96 (endSkimIlkWord I) ⟨12⟩ solcFreePtrMem_size

theorem endSkimVatIlksBaseMem_read64 (I : ExecutionEnv) :
    (endSkimVatIlksBaseMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 (endSkimIlkWord I) ⟨12⟩ solcFreePtrMem_size
    solcFreePtrMem_read64

theorem endSkimVatIlksCalldataMem_size (I : ExecutionEnv) :
    (endSkimVatIlksCalldataMem I).size = 164 := by
  unfold endSkimVatIlksCalldataMem
  exact endFlowVatIlksCalldataMem_size I (endSkimVatIlksBaseMem_size I)

theorem endSkimVatIlksCalldataMem_read64 (I : ExecutionEnv) :
    (endSkimVatIlksCalldataMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSkimVatIlksCalldataMem
  exact endFlowVatIlksCalldataMem_read64 I (endSkimVatIlksBaseMem_size I)
    (endSkimVatIlksBaseMem_read64 I)

theorem endSkimVatIlksEncode_eq (I : ExecutionEnv) (hsz68 : 68 ≤ I.calldata.size) :
    config.externalABI.encode? "vatIlks" [.fixedBytes bytes32Width (endBytes32ArgBytes I)] =
      some ((endSkimVatIlksCalldataMem I).readWithPadding
        endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat) := by
  unfold endSkimVatIlksCalldataMem
  exact endFlowVatIlksEncode_eq I (by omega) (endSkimVatIlksBaseMem_size I)

theorem endSkimVatIlksWriteLen_eq {out : ByteArray} (hout : out.size < UInt256.size) :
    (min endFlowVatIlksOutSize (UInt256.ofNat out.size)).toNat = min 160 out.size := by
  simpa [endFlowVatIlksOutSize] using endFlowVatIlksWriteLen_eq (out := out) hout

theorem endSkimVatIlksPostCallMem_size_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 160 ≤ out.size) :
    (endSkimVatIlksPostCallMem I out).size = 288 := by
  unfold endSkimVatIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    show endFlowVatIlksOutSize.toNat = 160 by native_decide]
  rw [Nat.min_eq_left hlo]
  change (out.write 0 (endSkimVatIlksCalldataMem I) 128 160).size = 288
  rw [write_eq_gen_extend out (endSkimVatIlksCalldataMem I) 128 160
    (by omega) (by omega)
    (by rw [endSkimVatIlksCalldataMem_size I]; omega)
    (by rw [endSkimVatIlksCalldataMem_size I]; omega)]
  rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
  rw [endSkimVatIlksCalldataMem_size I]
  omega

theorem endSkimVatIlksPostCallMem_read64_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 160 ≤ out.size) :
    (endSkimVatIlksPostCallMem I out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSkimVatIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    show endFlowVatIlksOutSize.toNat = 160 by native_decide]
  rw [Nat.min_eq_left hlo]
  change ByteArray.readWithPadding
      (out.write 0 (endSkimVatIlksCalldataMem I) 128 160) 64 32 =
    UInt256.toByteArray ⟨128⟩
  rw [write_read_below_gen_extend out (endSkimVatIlksCalldataMem I) 128 160 64
    (by omega) (by omega)
    (by rw [endSkimVatIlksCalldataMem_size I]; omega)
    (by omega)]
  exact endSkimVatIlksCalldataMem_read64 I

theorem endSkimVatIlksPostCallMem_size_gt64 (I : ExecutionEnv) (out : ByteArray) :
    64 < (endSkimVatIlksPostCallMem I out).size := by
  unfold endSkimVatIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    show endFlowVatIlksOutSize.toNat = 160 by native_decide]
  by_cases hlen0 : min 160 out.size = 0
  · rw [hlen0, byteArray_write_len_zero]
    rw [endSkimVatIlksCalldataMem_size I]
    omega
  · by_cases hext : (endSkimVatIlksCalldataMem I).size < 128 + min 160 out.size
    · rw [write_eq_gen_extend out (endSkimVatIlksCalldataMem I)
        128 (min 160 out.size) hlen0 (Nat.min_le_right _ _)
        (by rw [endSkimVatIlksCalldataMem_size I]; omega) hext]
      have hbaseSize : (endSkimVatIlksCalldataMem I).size = 164 :=
        endSkimVatIlksCalldataMem_size I
      have hprefix :
          ((endSkimVatIlksCalldataMem I).extract 0 128).size = 128 := by
        rw [ByteArray.size_extract, hbaseSize]
        omega
      have hsrc : (out.extract 0 (min 160 out.size)).size = min 160 out.size := by
        rw [ByteArray.size_extract]
        omega
      rw [ByteArray.size_append, hprefix, hsrc]
      have hleout : min 160 out.size ≤ out.size := Nat.min_le_right _ _
      omega
    · have hin : 128 + min 160 out.size ≤ (endSkimVatIlksCalldataMem I).size := by
        omega
      rw [write_eq_gen out (endSkimVatIlksCalldataMem I)
        128 (min 160 out.size) hlen0 (Nat.min_le_right _ _) hin]
      have hbaseSize : (endSkimVatIlksCalldataMem I).size = 164 :=
        endSkimVatIlksCalldataMem_size I
      have hprefix :
          ((endSkimVatIlksCalldataMem I).extract 0 128).size = 128 := by
        rw [ByteArray.size_extract, hbaseSize]
        omega
      have hsrc : (out.extract 0 (min 160 out.size)).size = min 160 out.size := by
        rw [ByteArray.size_extract]
        omega
      have htail :
          ((endSkimVatIlksCalldataMem I).extract
            (128 + min 160 out.size) (endSkimVatIlksCalldataMem I).size).size =
              164 - (128 + min 160 out.size) := by
        rw [ByteArray.size_extract, hbaseSize]
        omega
      rw [ByteArray.size_append, ByteArray.size_append, hprefix, hsrc, htail]
      have hleout : min 160 out.size ≤ out.size := Nat.min_le_right _ _
      omega

theorem endSkimVatIlksPostCallMem_read64 (I : ExecutionEnv) (out : ByteArray) :
    (endSkimVatIlksPostCallMem I out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSkimVatIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    show endFlowVatIlksOutSize.toNat = 160 by native_decide]
  by_cases hlen0 : min 160 out.size = 0
  · rw [hlen0, byteArray_write_len_zero]
    exact endSkimVatIlksCalldataMem_read64 I
  · rw [write_read_below_gen_extend out (endSkimVatIlksCalldataMem I)
      128 (min 160 out.size) 64 hlen0 (Nat.min_le_right _ _)
      (by rw [endSkimVatIlksCalldataMem_size I]; omega)
      (by native_decide)]
    exact endSkimVatIlksCalldataMem_read64 I

theorem endSkimVatIlksPostCallMem_mload64 (I : ExecutionEnv) (out : ByteArray) :
    (if (⟨64⟩ : UInt256).toNat ≥ (endSkimVatIlksPostCallMem I out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((endSkimVatIlksPostCallMem I out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by exact endSkimVatIlksPostCallMem_size_gt64 I out)
    (by decide)
    (endSkimVatIlksPostCallMem_read64 I out)

theorem endSkimVatIlksPostCallMem_mload64_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 160 ≤ out.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (endSkimVatIlksPostCallMem I out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((endSkimVatIlksPostCallMem I out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [endSkimVatIlksPostCallMem_size_long I out hlo]; decide)
    (by decide)
    (endSkimVatIlksPostCallMem_read64_long I out hlo)

theorem endSkimVatIlksPostCallMem_read160_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 160 ≤ out.size) :
    (endSkimVatIlksPostCallMem I out).readWithPadding 160 32 = out.extract 32 64 := by
  unfold endSkimVatIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    show endFlowVatIlksOutSize.toNat = 160 by native_decide]
  rw [Nat.min_eq_left hlo]
  rw [write_eq_gen_extend out (endSkimVatIlksCalldataMem I) 128 160
    (by omega) (by omega)
    (by rw [endSkimVatIlksCalldataMem_size I]; omega)
    (by rw [endSkimVatIlksCalldataMem_size I]; omega)]
  have hprefix : ((endSkimVatIlksCalldataMem I).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract]
    rw [endSkimVatIlksCalldataMem_size I]
    omega
  have hsrc : (out.extract 0 160).size = 160 := by
    rw [ByteArray.size_extract]
    omega
  have hmemSize :
      ((endSkimVatIlksCalldataMem I).extract 0 128 ++ out.extract 0 160).size = 288 := by
    rw [ByteArray.size_append, hprefix, hsrc]
  have hreadIn :
      160 + 32 ≤ ((endSkimVatIlksCalldataMem I).extract 0 128 ++
          out.extract 0 160).size := by
    rw [hmemSize]
    norm_num
  rw [readWithPadding_eq_extract _ 160 hreadIn]
  rw [show 160 + 32 = 192 by omega]
  rw [extract_append_right_window _ _ 160 192 (by rw [hprefix]; omega), hprefix]
  rw [show 160 - 128 = 32 by omega, show 192 - 128 = 64 by omega]
  rw [extract_extract_BA]
  norm_num

theorem endSkimVatIlksPostCallMem_mload160_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 160 ≤ out.size) :
    (if (⟨160⟩ : UInt256).toNat ≥ (endSkimVatIlksPostCallMem I out).size
        ∨ (⟨160⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((endSkimVatIlksPostCallMem I out).readWithPadding (⟨160⟩ : UInt256).toNat 32))) =
      endFlowVatIlkRateWord out := by
  unfold endFlowVatIlkRateWord
  rw [if_neg]
  · change UInt256.ofNat
      (fromByteArrayBigEndian ((endSkimVatIlksPostCallMem I out).readWithPadding 160 32)) =
        UInt256.ofNat (fromByteArrayBigEndian (out.extract 32 64))
    rw [endSkimVatIlksPostCallMem_read160_long I out hlo]
  · exact not_or.mpr
      ⟨by rw [endSkimVatIlksPostCallMem_size_long I out hlo]; decide, by native_decide⟩

theorem endSkimUrnAddr_word (I : ExecutionEnv) :
    EVM.word ↑(endSkimUrnAddr I) = endSkimUrnKey I := by
  apply u256_inj
  unfold endSkimUrnAddr endSkimUrnKey endSkimUrnWord AccountAddress.ofNat EVM.word
  simp only [Fin.val_ofNat]
  change ((calldataWord I.calldata 36).val.val % AccountAddress.size) % UInt256.size =
    (UInt256.land solcAddrMask (calldataWord I.calldata 36)).toNat
  rw [uland_toNat]
  change ((calldataWord I.calldata 36).val.val % AccountAddress.size) % UInt256.size =
    Nat.land solcAddrMask.toNat (calldataWord I.calldata 36).val.val
  rw [show solcAddrMask.toNat = 2 ^ 160 - 1 by decide]
  rw [nat_land_comm]
  rw [nat_land_mask_eq_mod]
  rw [show AccountAddress.size = 2 ^ 160 by rfl]
  rw [Nat.mod_eq_of_lt]
  exact Nat.lt_trans (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 160)) (by native_decide)

theorem endSkimUrnsSelectorMem_size (I : ExecutionEnv) (vatOut : ByteArray)
    (hlo : 160 ≤ vatOut.size) :
    (endSkimUrnsSelectorMem I vatOut).size = 288 := by
  unfold endSkimUrnsSelectorMem
  exact toByteArray_write32_size_of_le (endSkimVatIlksPostCallMem I vatOut)
    endFreeUrnsSelectorShifted endFreeUrnsOutPtr.toNat 288 288
    (endSkimVatIlksPostCallMem_size_long I vatOut hlo)
    (by rw [endSkimVatIlksPostCallMem_size_long I vatOut hlo]; native_decide)
    (by native_decide)

theorem endSkimUrnsSelectorMem_read64 (I : ExecutionEnv) (vatOut : ByteArray)
    (hlo : 160 ≤ vatOut.size) :
    (endSkimUrnsSelectorMem I vatOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSkimUrnsSelectorMem
  rw [write32_read_below _ _ endFreeUrnsOutPtr.toNat 64
    (by rw [toByteArray_size])
    (by rw [endSkimVatIlksPostCallMem_size_long I vatOut hlo]; native_decide)
    (by native_decide)]
  exact endSkimVatIlksPostCallMem_read64_long I vatOut hlo

theorem endSkimUrnsArg0Mem_size (I : ExecutionEnv) (vatOut : ByteArray)
    (hlo : 160 ≤ vatOut.size) :
    (endSkimUrnsArg0Mem I vatOut).size = 288 := by
  unfold endSkimUrnsArg0Mem
  change ((endSkimIlkWord I).toByteArray.write 0 (endSkimUrnsSelectorMem I vatOut)
    132 32).size = 288
  exact toByteArray_write32_size_of_le (endSkimUrnsSelectorMem I vatOut)
    (endSkimIlkWord I) 132 288 288
    (endSkimUrnsSelectorMem_size I vatOut hlo)
    (by rw [endSkimUrnsSelectorMem_size I vatOut hlo]; native_decide)
    (by native_decide)

theorem endSkimUrnsArg0Mem_read64 (I : ExecutionEnv) (vatOut : ByteArray)
    (hlo : 160 ≤ vatOut.size) :
    (endSkimUrnsArg0Mem I vatOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSkimUrnsArg0Mem
  change ((endSkimIlkWord I).toByteArray.write 0 (endSkimUrnsSelectorMem I vatOut)
    132 32).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩
  rw [write32_read_below _ _ 132 64
    (by rw [toByteArray_size])
    (by rw [endSkimUrnsSelectorMem_size I vatOut hlo]; native_decide)
    (by native_decide)]
  exact endSkimUrnsSelectorMem_read64 I vatOut hlo

theorem endSkimUrnsCalldataMem_size (I : ExecutionEnv) (vatOut : ByteArray)
    (hlo : 160 ≤ vatOut.size) :
    (endSkimUrnsCalldataMem I vatOut).size = 288 := by
  unfold endSkimUrnsCalldataMem
  change ((endSkimUrnKey I).toByteArray.write 0 (endSkimUrnsArg0Mem I vatOut)
    164 32).size = 288
  exact toByteArray_write32_size_of_le (endSkimUrnsArg0Mem I vatOut)
    (endSkimUrnKey I) 164 288 288
    (endSkimUrnsArg0Mem_size I vatOut hlo)
    (by rw [endSkimUrnsArg0Mem_size I vatOut hlo]; native_decide)
    (by native_decide)

theorem endSkimUrnsCalldataMem_read64 (I : ExecutionEnv) (vatOut : ByteArray)
    (hlo : 160 ≤ vatOut.size) :
    (endSkimUrnsCalldataMem I vatOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSkimUrnsCalldataMem
  change ((endSkimUrnKey I).toByteArray.write 0 (endSkimUrnsArg0Mem I vatOut)
    164 32).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩
  rw [write32_read_below _ _ 164 64
    (by rw [toByteArray_size])
    (by rw [endSkimUrnsArg0Mem_size I vatOut hlo]; native_decide)
    (by native_decide)]
  exact endSkimUrnsArg0Mem_read64 I vatOut hlo

theorem endSkimUrnsCalldataMem_read128_4 (I : ExecutionEnv) (vatOut : ByteArray)
    (hlo : 160 ≤ vatOut.size) :
    (endSkimUrnsCalldataMem I vatOut).readWithPadding 128 4 = urnsSelector := by
  unfold endSkimUrnsCalldataMem
  rw [show (endFreeUrnsOutPtr + ⟨36⟩).toNat = 164 by native_decide]
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (by rw [endSkimUrnsArg0Mem_size I vatOut hlo]; native_decide)
    (by omega)
    (by rw [endSkimUrnsArg0Mem_size I vatOut hlo]; omega) (by omega) (by norm_num)]
  unfold endSkimUrnsArg0Mem
  rw [show (endFreeUrnsOutPtr + ⟨4⟩).toNat = 132 by native_decide]
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by rw [endSkimUrnsSelectorMem_size I vatOut hlo]; native_decide)
    (by omega)
    (by rw [endSkimUrnsSelectorMem_size I vatOut hlo]; omega) (by omega) (by norm_num)]
  unfold endSkimUrnsSelectorMem endFreeUrnsOutPtr
  change
    (endFreeUrnsSelectorShifted.toByteArray.write 0
      (endSkimVatIlksPostCallMem I vatOut) 128 32).readWithPadding 128 4 =
      urnsSelector
  rw [toByteArray_write_read_window_of_gap endFreeUrnsSelectorShifted
    (endSkimVatIlksPostCallMem I vatOut) 128 0 4
    (by omega) (by omega) (by omega)
    (by rw [endSkimVatIlksPostCallMem_size_long I vatOut hlo]; native_decide)]
  unfold endFreeUrnsSelectorShifted urnsSelector selectorBytes
  native_decide

theorem endSkimUrnsCalldataMem_read132_32 (I : ExecutionEnv) (vatOut : ByteArray)
    (hlo : 160 ≤ vatOut.size) :
    (endSkimUrnsCalldataMem I vatOut).readWithPadding 132 32 =
      (endSkimIlkWord I).toByteArray := by
  unfold endSkimUrnsCalldataMem
  rw [show (endFreeUrnsOutPtr + ⟨36⟩).toNat = 164 by native_decide]
  rw [write32_read_below_len _ _ 164 132 32 (by rw [toByteArray_size])
    (by rw [endSkimUrnsArg0Mem_size I vatOut hlo]; native_decide)
    (by omega)
    (by rw [endSkimUrnsArg0Mem_size I vatOut hlo]; omega) (by omega) (by norm_num)]
  unfold endSkimUrnsArg0Mem
  rw [show (endFreeUrnsOutPtr + ⟨4⟩).toNat = 132 by native_decide]
  rw [write32_read_prefix_len _ _ 132 32 (by rw [toByteArray_size])
    (by rw [endSkimUrnsSelectorMem_size I vatOut hlo]; native_decide)
    (by omega) (by omega) (by norm_num)]
  rw [toByteArray_extract_all]

theorem endSkimUrnsCalldataMem_read164_32 (I : ExecutionEnv) (vatOut : ByteArray)
    (hlo : 160 ≤ vatOut.size) :
    (endSkimUrnsCalldataMem I vatOut).readWithPadding 164 32 =
      (endSkimUrnKey I).toByteArray := by
  unfold endSkimUrnsCalldataMem
  rw [show (endFreeUrnsOutPtr + ⟨36⟩).toNat = 164 by native_decide]
  rw [write32_read_back _ _ 164 (by rw [toByteArray_size])
    (by rw [endSkimUrnsArg0Mem_size I vatOut hlo]; native_decide)]
  rw [toByteArray_extract_all]

theorem endSkimUrnsCalldataMem_read128_68 (I : ExecutionEnv) (vatOut : ByteArray)
    (hlo : 160 ≤ vatOut.size) :
    (endSkimUrnsCalldataMem I vatOut).readWithPadding 128 68 =
      urnsSelector ++ (endSkimIlkWord I).toByteArray ++ (endSkimUrnKey I).toByteArray := by
  have hsize : (endSkimUrnsCalldataMem I vatOut).size = 288 :=
    endSkimUrnsCalldataMem_size I vatOut hlo
  rw [show 68 = 4 + 64 from rfl,
    byteArray_readWithPadding_split (endSkimUrnsCalldataMem I vatOut) 128 4 64
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize]; omega)]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (endSkimUrnsCalldataMem I vatOut) 132 32 32
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize]; omega)]
  rw [endSkimUrnsCalldataMem_read128_4 I vatOut hlo,
    endSkimUrnsCalldataMem_read132_32 I vatOut hlo,
    endSkimUrnsCalldataMem_read164_32 I vatOut hlo]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem endSkimUrnsEncode_eq (I : ExecutionEnv) (vatOut : ByteArray)
    (hsz68 : 68 ≤ I.calldata.size) (hlo : 160 ≤ vatOut.size) :
    config.externalABI.encode? "urns"
        [.fixedBytes bytes32Width (endBytes32ArgBytes I), .address (endSkimUrnAddr I)] =
      some ((endSkimUrnsCalldataMem I vatOut).readWithPadding
        endFreeUrnsOutPtr.toNat endFreeUrnsInSize.toNat) := by
  change config.externalABI.encode? "urns"
      [.fixedBytes bytes32Width (endBytes32ArgBytes I), .address (endSkimUrnAddr I)] =
    some ((endSkimUrnsCalldataMem I vatOut).readWithPadding 128 68)
  rw [endSkimUrnsCalldataMem_read128_68 I vatOut hlo]
  have hbytes : endBytes32ArgBytes I = EVM.Word.toBytesBE (endSkimIlkWord I) := by
    have hlen32 : (endBytes32ArgBytes I).length = 32 :=
      endBytes32ArgBytes_len32 (I := I) (by omega)
    have hword : ABI.bytesToWord (endBytes32ArgBytes I) = endSkimIlkWord I := by
      simpa [endBytes32ArgBytes, endSkimIlkWord, endBytes32ArgWord] using
        (decode_word_at_eq_any I.calldata 4 (by omega))
    have hto := toBytesBE_bytesToWord_of_length (bs := endBytes32ArgBytes I) hlen32
    rw [hword] at hto
    exact hto.symm
  have hurnWord : EVM.word ↑(endSkimUrnAddr I) = endSkimUrnKey I :=
    endSkimUrnAddr_word I
  have hbytesLen : (EVM.Word.toBytesBE (endSkimIlkWord I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (endSkimIlkWord I)
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, bytes32, bytes32Width, addr, urnsSelector,
    selectorBytes, hbytes, hbytesLen, hurnWord, zeroBytes,
    word_toBytesBE_toByteArray_eq_toByteArray, ByteArray.append_assoc]

theorem endSkimUrnsWriteLen_eq {out : ByteArray} (hout : out.size < UInt256.size) :
    (min endFreeUrnsOutSize (UInt256.ofNat out.size)).toNat = min 64 out.size := by
  simpa [endFreeUrnsOutSize] using endFreeUrnsWriteLen_eq (out := out) hout

theorem endSkimUrnsPostCallMem_size (I : ExecutionEnv) (vatOut urnOut : ByteArray)
    (hlo : 160 ≤ vatOut.size) :
    (endSkimUrnsPostCallMem I vatOut urnOut).size = 288 := by
  unfold endSkimUrnsPostCallMem
  rw [show endFreeUrnsOutPtr.toNat = 128 by native_decide,
    show endFreeUrnsOutSize.toNat = 64 by native_decide]
  by_cases hlen0 : min 64 urnOut.size = 0
  · rw [hlen0, byteArray_write_len_zero, endSkimUrnsCalldataMem_size I vatOut hlo]
  · rw [write_eq_gen urnOut (endSkimUrnsCalldataMem I vatOut)
      128 (min 64 urnOut.size) hlen0 (Nat.min_le_right _ _)
      (by
        rw [endSkimUrnsCalldataMem_size I vatOut hlo]
        have hle64 : min 64 urnOut.size ≤ 64 := Nat.min_le_left _ _
        omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract,
      endSkimUrnsCalldataMem_size I vatOut hlo]
    have hle64 : min 64 urnOut.size ≤ 64 := Nat.min_le_left _ _
    have hleout : min 64 urnOut.size ≤ urnOut.size := Nat.min_le_right _ _
    omega

theorem endSkimUrnsPostCallMem_read64 (I : ExecutionEnv) (vatOut urnOut : ByteArray)
    (hlo : 160 ≤ vatOut.size) :
    (endSkimUrnsPostCallMem I vatOut urnOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSkimUrnsPostCallMem
  rw [show endFreeUrnsOutPtr.toNat = 128 by native_decide,
    show endFreeUrnsOutSize.toNat = 64 by native_decide]
  by_cases hlen0 : min 64 urnOut.size = 0
  · rw [hlen0, byteArray_write_len_zero]
    exact endSkimUrnsCalldataMem_read64 I vatOut hlo
  · rw [write_read_below_gen urnOut (endSkimUrnsCalldataMem I vatOut)
      128 (min 64 urnOut.size) 64 hlen0
      (Nat.min_le_right _ _)
      (by
        rw [endSkimUrnsCalldataMem_size I vatOut hlo]
        have hle64 : min 64 urnOut.size ≤ 64 := Nat.min_le_left _ _
        omega)
      (by native_decide)]
    exact endSkimUrnsCalldataMem_read64 I vatOut hlo

theorem endSkimUrnsPostCallMem_read128_32 (I : ExecutionEnv) (vatOut urnOut : ByteArray)
    (hloVat : 160 ≤ vatOut.size) (hloUrn : 64 ≤ urnOut.size) :
    (endSkimUrnsPostCallMem I vatOut urnOut).readWithPadding 128 32 =
      urnOut.extract 0 32 := by
  unfold endSkimUrnsPostCallMem
  rw [show endFreeUrnsOutPtr.toNat = 128 by native_decide,
    show endFreeUrnsOutSize.toNat = 64 by native_decide]
  rw [Nat.min_eq_left hloUrn]
  rw [write_eq_gen urnOut (endSkimUrnsCalldataMem I vatOut) 128 64
    (by omega) (by omega)
    (by rw [endSkimUrnsCalldataMem_size I vatOut hloVat]; omega)]
  have hprefix : ((endSkimUrnsCalldataMem I vatOut).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, endSkimUrnsCalldataMem_size I vatOut hloVat]
    omega
  have hsrc : (urnOut.extract 0 64).size = 64 := by
    rw [ByteArray.size_extract]
    omega
  have hreadIn :
      128 + 32 ≤ ((endSkimUrnsCalldataMem I vatOut).extract 0 128 ++
          urnOut.extract 0 64 ++
          (endSkimUrnsCalldataMem I vatOut).extract 192
            (endSkimUrnsCalldataMem I vatOut).size).size := by
    rw [ByteArray.size_append, ByteArray.size_append, hprefix, hsrc]
    rw [ByteArray.size_extract, endSkimUrnsCalldataMem_size I vatOut hloVat]
    omega
  rw [readWithPadding_eq_extract _ 128 hreadIn]
  rw [show 128 + 32 = 160 by omega]
  rw [extract_append_left _ _ 128 160
    (by rw [ByteArray.size_append, hprefix, hsrc]; omega)]
  rw [extract_append_right_window _ _ 128 160 (by rw [hprefix]), hprefix]
  rw [show 128 - 128 = 0 by omega, show 160 - 128 = 32 by omega]
  rw [extract_extract_BA]
  norm_num

theorem endSkimUrnsPostCallMem_read160_32 (I : ExecutionEnv) (vatOut urnOut : ByteArray)
    (hloVat : 160 ≤ vatOut.size) (hloUrn : 64 ≤ urnOut.size) :
    (endSkimUrnsPostCallMem I vatOut urnOut).readWithPadding 160 32 =
      urnOut.extract 32 64 := by
  unfold endSkimUrnsPostCallMem
  rw [show endFreeUrnsOutPtr.toNat = 128 by native_decide,
    show endFreeUrnsOutSize.toNat = 64 by native_decide]
  rw [Nat.min_eq_left hloUrn]
  rw [write_eq_gen urnOut (endSkimUrnsCalldataMem I vatOut) 128 64
    (by omega) (by omega)
    (by rw [endSkimUrnsCalldataMem_size I vatOut hloVat]; omega)]
  have hprefix : ((endSkimUrnsCalldataMem I vatOut).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, endSkimUrnsCalldataMem_size I vatOut hloVat]
    omega
  have hsrc : (urnOut.extract 0 64).size = 64 := by
    rw [ByteArray.size_extract]
    omega
  have hreadIn :
      160 + 32 ≤ ((endSkimUrnsCalldataMem I vatOut).extract 0 128 ++
          urnOut.extract 0 64 ++
          (endSkimUrnsCalldataMem I vatOut).extract 192
            (endSkimUrnsCalldataMem I vatOut).size).size := by
    rw [ByteArray.size_append, ByteArray.size_append, hprefix, hsrc]
    rw [ByteArray.size_extract, endSkimUrnsCalldataMem_size I vatOut hloVat]
    omega
  rw [readWithPadding_eq_extract _ 160 hreadIn]
  rw [show 160 + 32 = 192 by omega]
  rw [extract_append_left _ _ 160 192
    (by rw [ByteArray.size_append, hprefix, hsrc])]
  rw [extract_append_right_window _ _ 160 192 (by rw [hprefix]; omega), hprefix]
  rw [show 160 - 128 = 32 by omega, show 192 - 128 = 64 by omega]
  rw [extract_extract_BA]
  norm_num

theorem endSkimUrnsPostCallMem_mload64 (I : ExecutionEnv) (vatOut urnOut : ByteArray)
    (hlo : 160 ≤ vatOut.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (endSkimUrnsPostCallMem I vatOut urnOut).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((endSkimUrnsPostCallMem I vatOut urnOut).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [endSkimUrnsPostCallMem_size I vatOut urnOut hlo]; decide)
    (by decide)
    (endSkimUrnsPostCallMem_read64 I vatOut urnOut hlo)

theorem endSkimUrnsPostCallMem_mload128 (I : ExecutionEnv) (vatOut urnOut : ByteArray)
    (hloVat : 160 ≤ vatOut.size) (hloUrn : 64 ≤ urnOut.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (endSkimUrnsPostCallMem I vatOut urnOut).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((endSkimUrnsPostCallMem I vatOut urnOut).readWithPadding
          (⟨128⟩ : UInt256).toNat 32))) =
      endFreeUrnInkWord urnOut := by
  unfold endFreeUrnInkWord
  rw [if_neg]
  · change UInt256.ofNat
      (fromByteArrayBigEndian
        ((endSkimUrnsPostCallMem I vatOut urnOut).readWithPadding 128 32)) =
        UInt256.ofNat (fromByteArrayBigEndian (urnOut.extract 0 32))
    rw [endSkimUrnsPostCallMem_read128_32 I vatOut urnOut hloVat hloUrn]
  · exact not_or.mpr
      ⟨by rw [endSkimUrnsPostCallMem_size I vatOut urnOut hloVat]; decide,
        by native_decide⟩

theorem endSkimUrnsPostCallMem_mload160 (I : ExecutionEnv) (vatOut urnOut : ByteArray)
    (hloVat : 160 ≤ vatOut.size) (hloUrn : 64 ≤ urnOut.size) :
    (if (⟨160⟩ : UInt256).toNat ≥ (endSkimUrnsPostCallMem I vatOut urnOut).size
        ∨ (⟨160⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((endSkimUrnsPostCallMem I vatOut urnOut).readWithPadding
          (⟨160⟩ : UInt256).toNat 32))) =
      endFreeUrnArtWord urnOut := by
  unfold endFreeUrnArtWord
  rw [if_neg]
  · change UInt256.ofNat
      (fromByteArrayBigEndian
        ((endSkimUrnsPostCallMem I vatOut urnOut).readWithPadding 160 32)) =
        UInt256.ofNat (fromByteArrayBigEndian (urnOut.extract 32 64))
    rw [endSkimUrnsPostCallMem_read160_32 I vatOut urnOut hloVat hloUrn]
  · exact not_or.mpr
      ⟨by rw [endSkimUrnsPostCallMem_size I vatOut urnOut hloVat]; decide,
        by native_decide⟩

theorem endDecode_skim_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (skimTransition.params.map Param.name)
      (transitionSignature skimTransition).paramTypes I.calldata = some (endSkimStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk", "urn"] [bytes32, addr]
    I.calldata = _
  simpa [config, skimTransition, bytes32, bytes32Width, addr, endSkimStore,
    endSkimIlkBytes, endSkimUrnAddr, endSkimUrnWord, abiBytes32, abiBytes32Width,
    abiAddress] using
    (endDecode_legacyBytes32_address_ok (cd := I.calldata) (x := "ilk")
      (y := "urn") hsz68)

theorem endDecode_skim_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (skimTransition.params.map Param.name)
      (transitionSignature skimTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk", "urn"] [bytes32, addr]
    I.calldata = none
  simpa [config, skimTransition, bytes32, bytes32Width, addr, abiBytes32,
    abiBytes32Width, abiAddress] using
    (endDecode_legacyBytes32_address_none_short (cd := I.calldata) (x := "ilk")
      (y := "urn") hsz4 hshort)

theorem endReachSkimBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endSkimConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endSkimEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x89ea45d3⟩ :=
    endSelWord_eq_of_beq I hsz 0x89 0xea 0x45 0xd3 ⟨0x89ea45d3⟩
      (by native_decide)
      (by simpa [selIs, endSkimConcreteSelector, selectorBytes] using hsel)
  obtain ⟨_, _, hfirst⟩ :=
    endReachGroup223FirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup223FirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup223FirstArmPc 0))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo endSkimEntryPc 0 hfirst
    (fun j hj => endGroup223ArmsWellFormed j (by omega))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem RD.endSkimDecodeToBody {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 endSkimDecodedPc (de :: ⟨4⟩ :: ret :: sel :: R)
        mem aw rdata acc k C)
    (hwf : code = endBytecode)
    (hroutine : (D_J code 0).contains endSkimBodyPc = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD code ee g s0 endSkimBodyPc
      (endSkimUrnKey ee :: calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd873 := h.jumpdest (by native_decide) (by evm_ov)
  have rd874 := rd873.pop (by native_decide) (by evm_ov)
  have rd875 := rd874.dup1 (by native_decide) (by evm_ov)
  have rd876 := rd875.calldataload (by native_decide) (by evm_ov)
  have rd877 := rd876.swap1 (by native_decide) (by evm_ov)
  have rd879 := rd877.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd880 := rd879.add (by native_decide) (by evm_ov)
  have rd881 := rd880.calldataload (by native_decide) (by evm_ov)
  have rd883 := rd881.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd885 := rd883.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd887 := rd885.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd888 := rd887.shl (by native_decide) (by evm_ov)
  have rd889 := rd888.sub (by native_decide) (by evm_ov)
  have rd890 := rd889.and (by native_decide) (by evm_ov)
  have rd891 := rd890.push2 endSkimBodyPc (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [endSkimBodyPc, endSkimDecodedPc, endSkimUrnKey, endSkimUrnWord,
      calldataWord,
      show (UInt256.add ⟨32⟩ ⟨4⟩) = ⟨36⟩ from by native_decide,
      show (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        solcAddrMask from by native_decide,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide]
      using rd891.jump (by native_decide) hroutine (by evm_ov)⟩

theorem endSkimX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endSkimEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g
        (initState cA gh bl σ σ₀ g A I) endSkimBodyPc
        [endSkimUrnKey I, endSkimIlkWord I, endSkimReturnPc, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := endBytecode) (sel := sel)
    (entry := endSkimEntryPc) (ret := endSkimReturnPc)
    (decoded := endSkimDecodedPc) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.endSkimDecodeToBody
    (code := endBytecode) (ret := endSkimReturnPc) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [endSkimUrnKey, endSkimUrnWord, endSkimIlkWord] using hroutine⟩

theorem endSkimX_tagZero {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSkimTagWord σ I = ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endSkimBodyPc
      [endSkimUrnKey I, endSkimIlkWord I, endSkimReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let key := endSkimIlkWord I
  have hslot : endSkimTagSlot I = solcMappingSlot ⟨12⟩ key := by
    simpa [key] using endSkimTagSlot_eq (I := I) hsz68
  have rd6710pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd6711 := rd6710pre.mstore 0 (wordAt0Mem key solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6715pre := evm_run rd6711 with [
    raw push1 ⟨12⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd6716 := rd6715pre.mstore 0 (twoWordHashMem key ⟨12⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6719pre := evm_run rd6716 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key ⟨12⟩ solcFreePtrMem).readWithPadding 0 64))) =
          solcMappingSlot ⟨12⟩ key :=
    twoWordHashMem_solcMappingSlot ⟨12⟩ key solcFreePtrMem_size
  have rd6720pre := rd6719pre.keccak256 0 (solcMappingSlot ⟨12⟩ key)
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by
      simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hhash)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd6721raw⟩ := rd6720pre.sload (by native_decide) (by evm_ov)
  have htagRaw :
      solcSlotWord σ I (solcMappingSlot ⟨12⟩ key) = ⟨0⟩ := by
    rw [← hslot]
    simpa [key, endSkimTagWord, endSlotWord] using htag
  have htagRaw' :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun ac => ac.storage.findD (solcMappingSlot ⟨12⟩ key) ⟨0⟩)) = ⟨0⟩ := by
    simpa [solcSlotWord] using htagRaw
  have rd6721zero := rd6721raw
  rw [htagRaw'] at rd6721zero
  obtain ⟨_, _, rd6721⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6721⟩
        (⟨0⟩ :: endSkimUrnKey I :: endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
        (twoWordHashMem key ⟨12⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endSkimBodyPc, key] using rd6721zero⟩
  have rd6724pre := rd6721.push2 ⟨6795⟩ (by native_decide) (by evm_ov)
  have rd6725pre := rd6724pre.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  obtain ⟨_, _, rd6725⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6725⟩
        [endSkimUrnKey I, endSkimIlkWord I, endSkimReturnPc, sel]
        (twoWordHashMem key ⟨12⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k' C' := by
    exact ⟨_, _, by simpa using rd6725pre⟩
  exact RD.solcErrorStringRevertTail
    (pc := ⟨6725⟩) (len := ⟨23⟩)
    (rawWord := ⟨1662547331793263672767660296024730882676930893819124057⟩)
    (shift := ⟨74⟩)
    (word := UInt256.shiftLeft
      ⟨1662547331793263672767660296024730882676930893819124057⟩ ⟨74⟩)
    (op := .PUSH23) (width := 23)
    rd6725
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide) rfl
    (twoWordHashMem_size_96 key ⟨12⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 key ⟨12⟩ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkimX_tagNonzero {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSkimTagWord σ I ≠ ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endSkimBodyPc
      [endSkimUrnKey I, endSkimIlkWord I, endSkimReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6795⟩
      [endSkimUrnKey I, endSkimIlkWord I, endSkimReturnPc, sel]
      (twoWordHashMem (endSkimIlkWord I) ⟨12⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  let key := endSkimIlkWord I
  have hslot : endSkimTagSlot I = solcMappingSlot ⟨12⟩ key := by
    simpa [key] using endSkimTagSlot_eq (I := I) hsz68
  have rd6710pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd6711 := rd6710pre.mstore 0 (wordAt0Mem key solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6715pre := evm_run rd6711 with [
    raw push1 ⟨12⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd6716 := rd6715pre.mstore 0 (twoWordHashMem key ⟨12⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6719pre := evm_run rd6716 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key ⟨12⟩ solcFreePtrMem).readWithPadding 0 64))) =
          solcMappingSlot ⟨12⟩ key :=
    twoWordHashMem_solcMappingSlot ⟨12⟩ key solcFreePtrMem_size
  have rd6720pre := rd6719pre.keccak256 0 (solcMappingSlot ⟨12⟩ key)
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by
      simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hhash)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd6721raw⟩ := rd6720pre.sload (by native_decide) (by evm_ov)
  have htagRaw :
      solcSlotWord σ I (solcMappingSlot ⟨12⟩ key) = endSkimTagWord σ I := by
    rw [← hslot]
    simp [endSkimTagWord, endSlotWord]
  have htagRaw' :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun ac => ac.storage.findD (solcMappingSlot ⟨12⟩ key) ⟨0⟩)) =
          endSkimTagWord σ I := by
    simpa [solcSlotWord] using htagRaw
  have rd6721nzRaw := rd6721raw
  rw [htagRaw'] at rd6721nzRaw
  obtain ⟨_, _, rd6721nz⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6721⟩
        (endSkimTagWord σ I :: endSkimUrnKey I :: endSkimIlkWord I ::
          endSkimReturnPc :: sel :: [])
        (twoWordHashMem key ⟨12⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endSkimBodyPc, key] using rd6721nzRaw⟩
  have rd6724pre := rd6721nz.push2 ⟨6795⟩ (by native_decide) (by evm_ov)
  have rd6795pre := rd6724pre.jumpiT (by native_decide) htag (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa [key] using rd6795pre⟩

theorem endSkimX_vatIlksExtcodesizeGuard {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6795⟩
      [endSkimUrnKey I, endSkimIlkWord I, endSkimReturnPc, sel]
      (endSkimVatIlksBaseMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6860⟩
      (endPackVatWord σ I :: endPackVatWord σ I :: ⟨0⟩ :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endFlowVatIlksOutSize ::
        endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σ I ::
        ⟨0⟩ :: endSkimUrnKey I :: endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      (endSkimVatIlksCalldataMem I) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k' C' := by
  have hmload64Hash :
      (if (⟨64⟩ : UInt256).toNat ≥ (endSkimVatIlksBaseMem I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endSkimVatIlksBaseMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue
      (by rw [endSkimVatIlksBaseMem_size I]; decide)
      (by decide)
      (endSkimVatIlksBaseMem_read64 I)
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (endSkimVatIlksCalldataMem I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endSkimVatIlksCalldataMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [endSkimVatIlksCalldataMem_size I]; decide)
      (by decide) (endSkimVatIlksCalldataMem_read64 I)
  have hselectorShift :
      UInt256.shiftLeft (⟨0x6cb1c69b⟩ : UInt256) ⟨225⟩ =
        endFlowVatIlksSelectorShifted := by
    native_decide
  have hvatMask :
      UInt256.land solcAddrMask (endSlotWord ⟨1⟩ σ I) = endPackVatWord σ I := by
    simpa [endPackVatWord, solcAddrMask] using
      u256_land_comm solcAddrMask (endSlotWord ⟨1⟩ σ I)
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hvatMaskRight :
      (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩).land
          (endSlotWord ⟨1⟩ σ I) = endPackVatWord σ I := by
    rw [haddrMask]
    exact hvatMask
  have hinSize :
      (UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨36⟩) = endFlowVatIlksInSize := by
    native_decide
  have hendPtr : ((⟨128⟩ : UInt256) + ⟨36⟩) = endFlowVatIlksEndPtr := by
    native_decide
  have rd6798 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd6799raw⟩ := rd6798.sload (by native_decide) (by evm_ov)
  have rd6799 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6799⟩
        (endSlotWord ⟨1⟩ σ I :: endSkimUrnKey I :: endSkimIlkWord I ::
          endSkimReturnPc :: sel :: [])
        (endSkimVatIlksBaseMem I) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd6799raw⟩
  obtain ⟨_, _, rd6799⟩ := rd6799
  have rd6859 := evm_run rd6799 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64Hash (by decide) (by evm_ov),
    raw push4 ⟨0x6cb1c69b⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨225⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (endFlowVatIlksSelectorMem (endSkimVatIlksBaseMem I))
      (UInt256.ofNat 5) (by native_decide) mem_cost
      (by
        simp [endFlowVatIlksSelectorMem, endFlowVatIlksOutPtr,
          endSkimVatIlksBaseMem, hselectorShift])
      (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 3 (endSkimVatIlksCalldataMem I) (UInt256.ofNat 6)
      (by native_decide) mem_cost
      (by
        simp [endSkimVatIlksCalldataMem, endFlowVatIlksCalldataMem,
          endFlowVatIlksArg0Mem, endFlowVatIlksOutPtr, endSkimVatIlksBaseMem])
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push4 endFlowVatIlksSelectorWord (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    convert rd6859 using 1
    all_goals
      try native_decide
      try simp [endFlowVatIlksOutPtr, endFlowVatIlksInSize, endFlowVatIlksOutSize,
        endFlowVatIlksEndPtr, hvatMaskRight, hinSize, hendPtr]
      try native_decide⟩

theorem endSkimX_vatIlksNoCode {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6795⟩
      [endSkimUrnKey I, endSkimIlkWord I, endSkimReturnPc, sel]
      (endSkimVatIlksBaseMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) = ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd6860⟩ := endSkimX_vatIlksExtcodesizeGuard h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨6860⟩) (okPc := ⟨6872⟩) rd6860
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkimX_vatIlksCallReady {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6795⟩
      [endSkimUrnKey I, endSkimIlkWord I, endSkimReturnPc, sel]
      (endSkimVatIlksBaseMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6875⟩
      (gasWord :: endPackVatWord σ I :: ⟨0⟩ :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endFlowVatIlksOutSize ::
        endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σ I ::
        ⟨0⟩ :: endSkimUrnKey I :: endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      (endSkimVatIlksCalldataMem I) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd6860⟩ := endSkimX_vatIlksExtcodesizeGuard h
  obtain ⟨gasWord, k', C', rd6875⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨6860⟩) (okPc := ⟨6872⟩) rd6860
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd6875⟩

theorem endSkimX_vatIlksPostCall {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel gasWord : UInt256} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6875⟩
      (gasWord :: endPackVatWord σ I :: ⟨0⟩ :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endFlowVatIlksOutSize ::
        endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σ I ::
        ⟨0⟩ :: endSkimUrnKey I :: endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      (endSkimVatIlksCalldataMem I) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl σ σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (endPackVatWord σ I))
          (toExecute σ (AccountAddress.ofUInt256 (endPackVatWord σ I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((endSkimVatIlksCalldataMem I).readWithPadding
            endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat)
          (I.depth + 1) I.header I.perm)
      ∧ RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6876⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endFlowVatIlksEndPtr ::
            endFlowVatIlksSelectorWord :: endPackVatWord σ I :: ⟨0⟩ ::
            endSkimUrnKey I :: endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
          (endSkimVatIlksPostCallMem I out) (UInt256.ofNat 9) out (cA', σ') k' C'
      ∧ out.size < UInt256.size := by
  obtain ⟨cA', σ', z, out, Ain, callGas, k', C', hΘ, rd6876raw, hout⟩ :=
    RD.call h (by native_decide) hdepth (by evm_ov)
  refine ⟨cA', σ', z, out, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · have hmin := endSkimVatIlksWriteLen_eq (out := out) hout
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat)
          endFlowVatIlksOutPtr.toNat endFlowVatIlksOutSize.toNat) = UInt256.ofNat 9 := by
      unfold endFlowVatIlksOutPtr endFlowVatIlksInSize endFlowVatIlksOutSize
      native_decide
    simpa [endSkimVatIlksPostCallMem, endFlowVatIlksOutPtr, endFlowVatIlksInSize,
      endFlowVatIlksOutSize, endFlowVatIlksEndPtr, hmin, haw] using rd6876raw

theorem endSkimX_vatIlksCallDepthLimit {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel gasWord : UInt256} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6875⟩
      (gasWord :: endPackVatWord σ I :: ⟨0⟩ :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endFlowVatIlksOutSize ::
        endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σ I ::
        ⟨0⟩ :: endSkimUrnKey I :: endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      (endSkimVatIlksCalldataMem I) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6876⟩
      (⟨0⟩ :: endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endPackVatWord σ I :: ⟨0⟩ :: endSkimUrnKey I :: endSkimIlkWord I ::
        endSkimReturnPc :: sel :: [])
      (endSkimVatIlksCalldataMem I) (UInt256.ofNat 9)
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', C', rd6876raw⟩ :=
    RD.callDepthLimit h (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min endFlowVatIlksOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
        endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat)
        endFlowVatIlksOutPtr.toNat endFlowVatIlksOutSize.toNat) = UInt256.ofNat 9 := by
    unfold endFlowVatIlksOutPtr endFlowVatIlksInSize endFlowVatIlksOutSize
    native_decide
  simpa [endFlowVatIlksOutPtr, endFlowVatIlksInSize, endFlowVatIlksOutSize,
    endFlowVatIlksEndPtr, hmin, byteArray_write_len_zero, haw] using rd6876raw

theorem endSkimX_vatIlksCallFailed {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6876⟩
      (⟨0⟩ :: endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endPackVatWord σ I :: ⟨0⟩ :: endSkimUrnKey I :: endSkimIlkWord I ::
        endSkimReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata (cA', σ') k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨6876⟩) (okPc := ⟨6892⟩) h
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkimX_vatIlksCallSucceeded {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6876⟩
      (⟨1⟩ :: endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endPackVatWord σ I :: ⟨0⟩ :: endSkimUrnKey I :: endSkimIlkWord I ::
        endSkimReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6894⟩
      (endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σ I ::
        ⟨0⟩ :: endSkimUrnKey I :: endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata (cA', σ') k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨6876⟩) (okPc := ⟨6892⟩) h
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simp)

theorem endSkimX_vatIlksReturnDecodeOk {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {out : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6894⟩
      (endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σ I ::
        ⟨0⟩ :: endSkimUrnKey I :: endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      (endSkimVatIlksPostCallMem I out) (UInt256.ofNat 9) out (cA', σ') k C)
    (hlo : 160 ≤ out.size) (hout : out.size < UInt256.size) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6920⟩
      (endFlowVatIlkRateWord out :: ⟨0⟩ :: endSkimUrnKey I ::
        endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      (endSkimVatIlksPostCallMem I out) (UInt256.ofNat 9) out (cA', σ') k' C' := by
  have hmload64 := endSkimVatIlksPostCallMem_mload64 I out
  have hmload160Raw := endSkimVatIlksPostCallMem_mload160_long I out hlo
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨160⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide, ulit_toNat' out.size hout]
    exact hlo
  have rd6906 := evm_run h with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨6914⟩ (by native_decide) (by evm_ov)]
  have rdJump := rd6906
  rw [hlt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rdJump
  have rd6920 := evm_run rdJump with [
    raw jumpiT (by native_decide) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by jump_dest) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mload 0 (endFlowVatIlkRateWord out) (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload160Raw (by decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [endFlowVatIlksEndPtr, endFlowVatIlksSelectorWord, endFlowVatIlksOutPtr,
      endFlowVatIlksInSize, endFlowVatIlksOutSize] using rd6920⟩

theorem endSkimX_vatIlksReturnDecodeShort {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {out : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6894⟩
      (endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σ I ::
        ⟨0⟩ :: endSkimUrnKey I :: endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      (endSkimVatIlksPostCallMem I out) (UInt256.ofNat 9) out (cA', σ') k C)
    (hshort : out.size < 160) (hout : out.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hmload64 := endSkimVatIlksPostCallMem_mload64 I out
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨160⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide, ulit_toNat' out.size hout]
    exact hshort
  have rd6906 := evm_run h with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨6914⟩ (by native_decide) (by evm_ov)]
  have rdShort := rd6906
  rw [hlt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rdShort
  have rdFall := rdShort.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdFall
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkimX_urnsExtcodesizeGuard {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {vatOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6920⟩
      (endFlowVatIlkRateWord vatOut :: ⟨0⟩ :: endSkimUrnKey I ::
        endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      (endSkimVatIlksPostCallMem I vatOut) (UInt256.ofNat 9) vatOut (cA', σ') k C)
    (hloVat : 160 ≤ vatOut.size) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6996⟩
      (endPackVatWord σ' I :: endPackVatWord σ' I :: ⟨0⟩ :: endFreeUrnsOutPtr ::
        endFreeUrnsInSize :: endFreeUrnsOutPtr :: endFreeUrnsOutSize ::
        endFreeUrnsEndPtr :: endFreeUrnsSelectorWord :: endPackVatWord σ' I ::
        ⟨0⟩ :: ⟨0⟩ :: endFlowVatIlkRateWord vatOut :: endSkimUrnKey I ::
        endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      (endSkimUrnsCalldataMem I vatOut) (UInt256.ofNat 9) vatOut (cA', σ') k' C' := by
  have hmload64Base := endSkimVatIlksPostCallMem_mload64_long I vatOut hloVat
  have hcallMem :
      (endSkimUrnsCalldataMem I vatOut).size = 288 :=
    endSkimUrnsCalldataMem_size I vatOut hloVat
  have hcallRead64 :
      (endSkimUrnsCalldataMem I vatOut).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    endSkimUrnsCalldataMem_read64 I vatOut hloVat
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (endSkimUrnsCalldataMem I vatOut).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endSkimUrnsCalldataMem I vatOut).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hcallMem]; decide) (by decide) hcallRead64
  have hselectorShift :
      UInt256.shiftLeft (⟨0x09092f97⟩ : UInt256) ⟨226⟩ =
        endFreeUrnsSelectorShifted := by
    native_decide
  have hvatMask :
      UInt256.land solcAddrMask (endSlotWord ⟨1⟩ σ' I) = endPackVatWord σ' I := by
    simpa [endPackVatWord, solcAddrMask] using
      u256_land_comm solcAddrMask (endSlotWord ⟨1⟩ σ' I)
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hvatMaskRight :
      (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩).land
          (endSlotWord ⟨1⟩ σ' I) = endPackVatWord σ' I := by
    rw [haddrMask]
    exact hvatMask
  have hurnCanon : (endSkimUrnKey I).toNat < EVM.addressModulus := by
    simpa [endSkimUrnKey, u256_land_comm solcAddrMask (endSkimUrnWord I)] using
      solcAddrMask_result_canonical (endSkimUrnWord I)
  have hurnMaskRight :
      (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩).land
          (endSkimUrnKey I) = endSkimUrnKey I := by
    rw [haddrMask]
    rw [u256_land_comm solcAddrMask (endSkimUrnKey I)]
    exact solcAddrMask_clean hurnCanon
  have hinSize :
      (UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨68⟩) = endFreeUrnsInSize := by
    native_decide
  have hendPtr : ((⟨128⟩ : UInt256) + ⟨68⟩) = endFreeUrnsEndPtr := by
    native_decide
  have rd6922 := evm_run h with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd6923raw⟩ := rd6922.sload (by native_decide) (by evm_ov)
  have rd6923 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6923⟩
        (endSlotWord ⟨1⟩ σ' I :: endFlowVatIlkRateWord vatOut :: ⟨0⟩ ::
          endSkimUrnKey I :: endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
        (endSkimVatIlksPostCallMem I vatOut) (UInt256.ofNat 9) vatOut
        (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd6923raw⟩
  obtain ⟨_, _, rd6923⟩ := rd6923
  have rd6996 := evm_run rd6923 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload64Base (by decide) (by evm_ov),
    raw push4 ⟨0x09092f97⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨226⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (endSkimUrnsSelectorMem I vatOut) (UInt256.ofNat 9)
      (by native_decide) mem_cost
      (by simp [endSkimUrnsSelectorMem, endFreeUrnsOutPtr, hselectorShift])
      (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 0 (endSkimUrnsArg0Mem I vatOut) (UInt256.ofNat 9)
      (by native_decide) mem_cost
      (by simp [endSkimUrnsArg0Mem, endFreeUrnsOutPtr])
      (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 0 (endSkimUrnsCalldataMem I vatOut) (UInt256.ofNat 9)
      (by native_decide) mem_cost
      (by simp [endSkimUrnsCalldataMem, endFreeUrnsOutPtr, hurnMaskRight])
      (by decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw swap6 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push4 endFreeUrnsSelectorWord (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    convert rd6996 using 1
    all_goals
      try native_decide
      try simp [endFreeUrnsOutPtr, endFreeUrnsInSize, endFreeUrnsOutSize,
        endFreeUrnsEndPtr, hvatMaskRight, hinSize, hendPtr]
      try native_decide⟩

theorem endSkimX_urnsNoCode {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {vatOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6920⟩
      (endFlowVatIlkRateWord vatOut :: ⟨0⟩ :: endSkimUrnKey I ::
        endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      (endSkimVatIlksPostCallMem I vatOut) (UInt256.ofNat 9) vatOut (cA', σ') k C)
    (hloVat : 160 ≤ vatOut.size)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (endPackVatWord σ' I) = ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd6996⟩ := endSkimX_urnsExtcodesizeGuard h hloVat
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨6996⟩) (okPc := ⟨7008⟩) rd6996
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkimX_urnsCallReady {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {vatOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6920⟩
      (endFlowVatIlkRateWord vatOut :: ⟨0⟩ :: endSkimUrnKey I ::
        endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      (endSkimVatIlksPostCallMem I vatOut) (UInt256.ofNat 9) vatOut (cA', σ') k C)
    (hloVat : 160 ≤ vatOut.size)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (endPackVatWord σ' I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7011⟩
      (gasWord :: endPackVatWord σ' I :: ⟨0⟩ :: endFreeUrnsOutPtr ::
        endFreeUrnsInSize :: endFreeUrnsOutPtr :: endFreeUrnsOutSize ::
        endFreeUrnsEndPtr :: endFreeUrnsSelectorWord :: endPackVatWord σ' I ::
        ⟨0⟩ :: ⟨0⟩ :: endFlowVatIlkRateWord vatOut :: endSkimUrnKey I ::
        endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      (endSkimUrnsCalldataMem I vatOut) (UInt256.ofNat 9) vatOut (cA', σ') k' C' := by
  obtain ⟨_, _, rd6996⟩ := endSkimX_urnsExtcodesizeGuard h hloVat
  obtain ⟨gasWord, k', C', rd7011⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨6996⟩) (okPc := ⟨7008⟩) rd6996
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd7011⟩

theorem endSkimX_urnsPostCall {cA cAcur gh bl σ σcur σ₀ A I} {g : Sat256}
    {sel gasWord : UInt256} {vatOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7011⟩
      (gasWord :: endPackVatWord σcur I :: ⟨0⟩ :: endFreeUrnsOutPtr ::
        endFreeUrnsInSize :: endFreeUrnsOutPtr :: endFreeUrnsOutSize ::
        endFreeUrnsEndPtr :: endFreeUrnsSelectorWord :: endPackVatWord σcur I ::
        ⟨0⟩ :: ⟨0⟩ :: endFlowVatIlkRateWord vatOut :: endSkimUrnKey I ::
        endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      (endSkimUrnsCalldataMem I vatOut) (UInt256.ofNat 9) vatOut (cAcur, σcur) k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out) = Ethereum.EVM.Θ I.blobVersionedHashes cAcur gh bl
          σcur σ₀ Ain (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (endPackVatWord σcur I))
          (toExecute σcur (AccountAddress.ofUInt256 (endPackVatWord σcur I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((endSkimUrnsCalldataMem I vatOut).readWithPadding
            endFreeUrnsOutPtr.toNat endFreeUrnsInSize.toNat)
          (I.depth + 1) I.header I.perm)
      ∧ RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7012⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endFreeUrnsEndPtr ::
            endFreeUrnsSelectorWord :: endPackVatWord σcur I :: ⟨0⟩ :: ⟨0⟩ ::
            endFlowVatIlkRateWord vatOut :: endSkimUrnKey I :: endSkimIlkWord I ::
            endSkimReturnPc :: sel :: [])
          (endSkimUrnsPostCallMem I vatOut out) (UInt256.ofNat 9) out (cA', σ') k' C'
      ∧ out.size < UInt256.size := by
  obtain ⟨cA', σ', z, out, Ain, callGas, k', C', hΘ, rd7012raw, hout⟩ :=
    RD.call h (by native_decide) hdepth (by evm_ov)
  refine ⟨cA', σ', z, out, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · have hmin := endSkimUrnsWriteLen_eq (out := out) hout
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
          endFreeUrnsOutPtr.toNat endFreeUrnsInSize.toNat)
          endFreeUrnsOutPtr.toNat endFreeUrnsOutSize.toNat) = UInt256.ofNat 9 := by
      unfold endFreeUrnsOutPtr endFreeUrnsInSize endFreeUrnsOutSize
      native_decide
    simpa [endSkimUrnsPostCallMem, endFreeUrnsOutPtr, endFreeUrnsInSize,
      endFreeUrnsOutSize, endFreeUrnsEndPtr, hmin, haw] using rd7012raw

theorem endSkimX_urnsCallDepthLimit {cA cAcur gh bl σ σcur σ₀ A I} {g : Sat256}
    {sel gasWord : UInt256} {vatOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7011⟩
      (gasWord :: endPackVatWord σcur I :: ⟨0⟩ :: endFreeUrnsOutPtr ::
        endFreeUrnsInSize :: endFreeUrnsOutPtr :: endFreeUrnsOutSize ::
        endFreeUrnsEndPtr :: endFreeUrnsSelectorWord :: endPackVatWord σcur I ::
        ⟨0⟩ :: ⟨0⟩ :: endFlowVatIlkRateWord vatOut :: endSkimUrnKey I ::
        endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      (endSkimUrnsCalldataMem I vatOut) (UInt256.ofNat 9) vatOut (cAcur, σcur) k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7012⟩
      (⟨0⟩ :: endFreeUrnsEndPtr :: endFreeUrnsSelectorWord :: endPackVatWord σcur I ::
        ⟨0⟩ :: ⟨0⟩ :: endFlowVatIlkRateWord vatOut :: endSkimUrnKey I ::
        endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      (endSkimUrnsCalldataMem I vatOut) (UInt256.ofNat 9) ByteArray.empty
      (cAcur, σcur) k' C' := by
  obtain ⟨k', C', rd7012raw⟩ :=
    RD.callDepthLimit h (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min endFreeUrnsOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
        endFreeUrnsOutPtr.toNat endFreeUrnsInSize.toNat)
        endFreeUrnsOutPtr.toNat endFreeUrnsOutSize.toNat) = UInt256.ofNat 9 := by
    unfold endFreeUrnsOutPtr endFreeUrnsInSize endFreeUrnsOutSize
    native_decide
  simpa [endFreeUrnsOutPtr, endFreeUrnsInSize, endFreeUrnsOutSize,
    endFreeUrnsEndPtr, hmin, byteArray_write_len_zero, haw] using rd7012raw

theorem endSkimX_urnsCallFailed {cA cA' gh bl σ σcur σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {vatOut : ByteArray} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7012⟩
      (⟨0⟩ :: endFreeUrnsEndPtr :: endFreeUrnsSelectorWord :: endPackVatWord σcur I ::
        ⟨0⟩ :: ⟨0⟩ :: endFlowVatIlkRateWord vatOut :: endSkimUrnKey I ::
        endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata (cA', σ') k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨7012⟩) (okPc := ⟨7028⟩) h
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkimX_urnsCallSucceeded {cA cA' gh bl σ σcur σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {vatOut : ByteArray} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7012⟩
      (⟨1⟩ :: endFreeUrnsEndPtr :: endFreeUrnsSelectorWord :: endPackVatWord σcur I ::
        ⟨0⟩ :: ⟨0⟩ :: endFlowVatIlkRateWord vatOut :: endSkimUrnKey I ::
        endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7030⟩
      (endFreeUrnsEndPtr :: endFreeUrnsSelectorWord :: endPackVatWord σcur I ::
        ⟨0⟩ :: ⟨0⟩ :: endFlowVatIlkRateWord vatOut :: endSkimUrnKey I ::
        endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata (cA', σ') k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨7012⟩) (okPc := ⟨7028⟩) h
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simp)

theorem endSkimX_urnsReturnDecodeOk {cA cA' gh bl σ σcur σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {vatOut out : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7030⟩
      (endFreeUrnsEndPtr :: endFreeUrnsSelectorWord :: endPackVatWord σcur I ::
        ⟨0⟩ :: ⟨0⟩ :: endFlowVatIlkRateWord vatOut :: endSkimUrnKey I ::
        endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      (endSkimUrnsPostCallMem I vatOut out) (UInt256.ofNat 9) out (cA', σ') k C)
    (hloVat : 160 ≤ vatOut.size) (hloUrn : 64 ≤ out.size)
    (hout : out.size < UInt256.size) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7065⟩
      (endFreeUrnArtWord out :: endFreeUrnInkWord out :: endFlowVatIlkRateWord vatOut ::
        endSkimUrnKey I :: endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      (endSkimUrnsPostCallMem I vatOut out) (UInt256.ofNat 9) out (cA', σ') k' C' := by
  have hmload64 := endSkimUrnsPostCallMem_mload64 I vatOut out hloVat
  have hmload128 := endSkimUrnsPostCallMem_mload128 I vatOut out hloVat hloUrn
  have hmload160 := endSkimUrnsPostCallMem_mload160 I vatOut out hloVat hloUrn
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨64⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, ulit_toNat' out.size hout]
    exact hloUrn
  have rd7042 := evm_run h with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨7050⟩ (by native_decide) (by evm_ov)]
  have rdJump := rd7042
  rw [hlt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rdJump
  have rd7065 := evm_run rdJump with [
    raw jumpiT (by native_decide) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by jump_dest) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 (endFreeUrnInkWord out) (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload128 (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mload 0 (endFreeUrnArtWord out) (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload160 (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [endFreeUrnsEndPtr, endFreeUrnsSelectorWord, endFreeUrnsOutPtr,
      endFreeUrnsInSize, endFreeUrnsOutSize] using rd7065⟩

theorem endSkimX_urnsReturnDecodeShort {cA cA' gh bl σ σcur σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {vatOut out : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7030⟩
      (endFreeUrnsEndPtr :: endFreeUrnsSelectorWord :: endPackVatWord σcur I ::
        ⟨0⟩ :: ⟨0⟩ :: endFlowVatIlkRateWord vatOut :: endSkimUrnKey I ::
        endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      (endSkimUrnsPostCallMem I vatOut out) (UInt256.ofNat 9) out (cA', σ') k C)
    (hloVat : 160 ≤ vatOut.size) (hshort : out.size < 64)
    (hout : out.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hmload64 := endSkimUrnsPostCallMem_mload64 I vatOut out hloVat
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨64⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, ulit_toNat' out.size hout]
    exact hshort
  have rd7042 := evm_run h with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨7050⟩ (by native_decide) (by evm_ov)]
  have rdShort := rd7042
  rw [hlt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rdShort
  have rdFall := rdShort.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdFall
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkimX_owe0RmulEntry {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {vatOut urnOut mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7065⟩
      (endFreeUrnArtWord urnOut :: endFreeUrnInkWord urnOut ::
        endFlowVatIlkRateWord vatOut :: endSkimUrnKey I :: endSkimIlkWord I ::
        endSkimReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10114⟩
      (endFlowVatIlkRateWord vatOut :: endFreeUrnArtWord urnOut :: ⟨7079⟩ ::
        ⟨7099⟩ :: ⟨0⟩ :: endFreeUrnArtWord urnOut :: endFreeUrnInkWord urnOut ::
        endFlowVatIlkRateWord vatOut :: endSkimUrnKey I :: endSkimIlkWord I ::
        endSkimReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata (cA', σ') k' C' := by
  have rd7078 := evm_run h with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw push2 ⟨7099⟩ (by native_decide) (by evm_ov),
    raw push2 ⟨7079⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw push2 ⟨10114⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by simpa using rd7078⟩

theorem endSkimX_oweRmulEntry {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {vatOut urnOut rdata : ByteArray} {k C : ℕ}
    (hsz68 : 68 ≤ I.calldata.size)
    (hloVat : 160 ≤ vatOut.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7079⟩
      (endSkimOwe0Word vatOut urnOut :: ⟨7099⟩ :: ⟨0⟩ ::
        endFreeUrnArtWord urnOut :: endFreeUrnInkWord urnOut ::
        endFlowVatIlkRateWord vatOut :: endSkimUrnKey I :: endSkimIlkWord I ::
        endSkimReturnPc :: sel :: [])
      (endSkimUrnsPostCallMem I vatOut urnOut) (UInt256.ofNat 9) rdata
      (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10114⟩
      (endSkimTagWord σ' I :: endSkimOwe0Word vatOut urnOut :: ⟨7099⟩ ::
        ⟨0⟩ :: endFreeUrnArtWord urnOut :: endFreeUrnInkWord urnOut ::
        endFlowVatIlkRateWord vatOut :: endSkimUrnKey I :: endSkimIlkWord I ::
        endSkimReturnPc :: sel :: [])
      (endSkimTagHashMem I vatOut urnOut) (UInt256.ofNat 9) rdata (cA', σ') k' C' := by
  let key := endSkimIlkWord I
  let mem0 := endSkimUrnsPostCallMem I vatOut urnOut
  let mem12 := endSkimTagHashMem I vatOut urnOut
  have hslot : endSkimTagSlot I = solcMappingSlot ⟨12⟩ key := by
    simpa [key] using endSkimTagSlot_eq (I := I) hsz68
  have hpostSize : mem0.size = 288 := by
    simpa [mem0] using endSkimUrnsPostCallMem_size I vatOut urnOut hloVat
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (mem12.readWithPadding 0 64))) =
        solcMappingSlot ⟨12⟩ key := by
    simpa [mem12, endSkimTagHashMem, key] using
      endFlow_twoWordHashMem_solcMappingSlot_of_ge64 (mem := mem0) ⟨12⟩ key
        (by rw [hpostSize]; omega)
  have rd7084 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup9 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd7085 := rd7084.mstore 0 (wordAt0Mem key mem0)
    (UInt256.ofNat 9) (by native_decide) mem_cost
    (by simp [wordAt0Mem, key, mem0]) (by native_decide) (by evm_ov)
  have rd7090pre := evm_run rd7085 with [
    raw push1 ⟨12⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd7090 := rd7090pre.mstore 0 mem12 (UInt256.ofNat 9)
    (by native_decide) mem_cost
    (by
      change (⟨12⟩ : UInt256).toByteArray.write 0 (wordAt0Mem key mem0) 32 32 =
        mem12
      simp [mem12, endSkimTagHashMem, twoWordHashMem, wordAt32Mem, key, mem0])
    (by native_decide) (by evm_ov)
  have rd7094 := evm_run rd7090 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd7095pre := rd7094.keccak256 0 (endSkimTagSlot I) (UInt256.ofNat 9)
    (by native_decide) mem_cost
    (by simpa [mem12, key, hslot] using hhash) (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd7095raw⟩ := rd7095pre.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd7095⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7095⟩
        (endSkimTagWord σ' I :: endSkimOwe0Word vatOut urnOut :: ⟨7099⟩ ::
          ⟨0⟩ :: endFreeUrnArtWord urnOut :: endFreeUrnInkWord urnOut ::
          endFlowVatIlkRateWord vatOut :: endSkimUrnKey I :: endSkimIlkWord I ::
          endSkimReturnPc :: sel :: [])
        mem12 (UInt256.ofNat 9) rdata (cA', σ') k' C' := by
    exact ⟨_, _, by
      simpa [endSkimTagWord, endSlotWord, solcSlotWord, key, hslot] using rd7095raw⟩
  have rd7099 := evm_run rd7095 with [
    raw push2 ⟨10114⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by simpa [mem12] using rd7099⟩

theorem endSkimX_minReturns {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {x y ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10206⟩
      (y :: x :: ret :: R) mem aw rdata (cA', σ') k C)
    (hret : (D_J endBytecode 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ret
      ((if x.toNat ≤ y.toNat then x else y) :: R) mem aw rdata (cA', σ') k' C' := by
  by_cases hle : x.toNat ≤ y.toNat
  · have hgt : UInt256.gt x y = ⟨0⟩ := ugt_zero hle
    have rd10216 := evm_run h with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
      raw dup2 (by native_decide) (by evm_ov),
      raw dup4 (by native_decide) (by evm_ov),
      raw gt (by native_decide) (by evm_ov),
      raw iszero (by native_decide) (by evm_ov),
      raw push2 ⟨10222⟩ (by native_decide) (by evm_ov)]
    rw [hgt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd10216
    have rd10224 := evm_run rd10216 with [
      raw jumpiT (by native_decide) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
        (by jump_dest) (by evm_ov),
      raw jumpdest (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw jumpdest (by native_decide) (by evm_ov),
      raw swap4 (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw jump (by native_decide) hret (by evm_ov)]
    exact ⟨_, _, by simpa [hle] using rd10224⟩
  · have hlt : y.toNat < x.toNat := Nat.lt_of_not_ge hle
    have hgt : UInt256.gt x y = ⟨1⟩ := ugt_one hlt
    have rd10216 := evm_run h with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
      raw dup2 (by native_decide) (by evm_ov),
      raw dup4 (by native_decide) (by evm_ov),
      raw gt (by native_decide) (by evm_ov),
      raw iszero (by native_decide) (by evm_ov),
      raw push2 ⟨10222⟩ (by native_decide) (by evm_ov)]
    rw [hgt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd10216
    have rd10224 := evm_run rd10216 with [
      raw jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
        (by evm_ov),
      raw dup2 (by native_decide) (by evm_ov),
      raw push2 ⟨10224⟩ (by native_decide) (by evm_ov),
      raw jump (by native_decide) (by jump_dest) (by evm_ov),
      raw jumpdest (by native_decide) (by evm_ov),
      raw swap4 (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw jump (by native_decide) hret (by evm_ov)]
    exact ⟨_, _, by simpa [hle] using rd10224⟩

theorem endSkimX_minEntry {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {vatOut urnOut mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7099⟩
      (endSkimOweWord σ' I vatOut urnOut :: ⟨0⟩ :: endFreeUrnArtWord urnOut ::
        endFreeUrnInkWord urnOut :: endFlowVatIlkRateWord vatOut :: endSkimUrnKey I ::
        endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10206⟩
      (endSkimOweWord σ' I vatOut urnOut :: endFreeUrnInkWord urnOut :: ⟨7113⟩ ::
        ⟨0⟩ :: endSkimOweWord σ' I vatOut urnOut :: endFreeUrnArtWord urnOut ::
        endFreeUrnInkWord urnOut :: endFlowVatIlkRateWord vatOut :: endSkimUrnKey I ::
        endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata (cA', σ') k' C' := by
  have rd7112 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw push2 ⟨7113⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw push2 ⟨10206⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by simpa using rd7112⟩

theorem endSkimX_gapSubEntry {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {vatOut urnOut rdata : ByteArray} {k C : ℕ}
    (hsz68 : 68 ≤ I.calldata.size)
    (hloVat : 160 ≤ vatOut.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7113⟩
      (endSkimWadWord σ' I vatOut urnOut :: ⟨0⟩ ::
        endSkimOweWord σ' I vatOut urnOut :: endFreeUrnArtWord urnOut ::
        endFreeUrnInkWord urnOut :: endFlowVatIlkRateWord vatOut :: endSkimUrnKey I ::
        endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      (endSkimTagHashMem I vatOut urnOut) (UInt256.ofNat 9) rdata (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10154⟩
      (endSkimWadWord σ' I vatOut urnOut :: endSkimOweWord σ' I vatOut urnOut ::
        ⟨7145⟩ :: endSkimGapWord σ' I :: ⟨7150⟩ ::
        endSkimWadWord σ' I vatOut urnOut :: endSkimOweWord σ' I vatOut urnOut ::
        endFreeUrnArtWord urnOut :: endFreeUrnInkWord urnOut ::
        endFlowVatIlkRateWord vatOut :: endSkimUrnKey I :: endSkimIlkWord I ::
        endSkimReturnPc :: sel :: [])
      (endSkimGapHashMem I vatOut urnOut) (UInt256.ofNat 9) rdata (cA', σ') k' C' := by
  let key := endSkimIlkWord I
  let mem0 := endSkimUrnsPostCallMem I vatOut urnOut
  let mem12 := endSkimTagHashMem I vatOut urnOut
  let mem13 := endSkimGapHashMem I vatOut urnOut
  have hslot : endSkimGapSlot I = solcMappingSlot ⟨13⟩ key := by
    simpa [key] using endSkimGapSlot_eq (I := I) hsz68
  have hpostSize : mem0.size = 288 := by
    simpa [mem0] using endSkimUrnsPostCallMem_size I vatOut urnOut hloVat
  have hmem12Size : mem12.size = mem0.size := by
    exact endFlow_twoWordHashMem_size_of_ge64 key ⟨12⟩
      (by rw [hpostSize]; omega)
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (mem13.readWithPadding 0 64))) =
        solcMappingSlot ⟨13⟩ key := by
    simpa [mem13, endSkimGapHashMem, key] using
      endFlow_twoWordHashMem_solcMappingSlot_of_ge64 (mem := mem12) ⟨13⟩ key
        (by rw [hmem12Size, hpostSize]; omega)
  have rd7118 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup9 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd7119 := rd7118.mstore 0 (wordAt0Mem key mem12)
    (UInt256.ofNat 9) (by native_decide) mem_cost
    (by simp [wordAt0Mem, key, mem12]) (by native_decide) (by evm_ov)
  have rd7124pre := evm_run rd7119 with [
    raw push1 ⟨13⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd7124 := rd7124pre.mstore 0 mem13 (UInt256.ofNat 9)
    (by native_decide) mem_cost
    (by
      change (⟨13⟩ : UInt256).toByteArray.write 0 (wordAt0Mem key mem12) 32 32 =
        mem13
      simp [mem13, endSkimGapHashMem, twoWordHashMem, wordAt32Mem, key, mem12])
    (by native_decide) (by evm_ov)
  have rd7128 := evm_run rd7124 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd7129pre := rd7128.keccak256 0 (endSkimGapSlot I) (UInt256.ofNat 9)
    (by native_decide) mem_cost
    (by simpa [mem13, key, hslot] using hhash) (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd7129raw⟩ := rd7129pre.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd7129⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7129⟩
        (endSkimGapWord σ' I :: endSkimWadWord σ' I vatOut urnOut :: ⟨0⟩ ::
          endSkimOweWord σ' I vatOut urnOut :: endFreeUrnArtWord urnOut ::
          endFreeUrnInkWord urnOut :: endFlowVatIlkRateWord vatOut ::
          endSkimUrnKey I :: endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
        mem13 (UInt256.ofNat 9) rdata (cA', σ') k' C' := by
    exact ⟨_, _, by
      simpa [endSkimGapWord, endSlotWord, solcSlotWord, key, hslot] using rd7129raw⟩
  have rd7144 := evm_run rd7129 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push2 ⟨7150⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨7145⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw push2 ⟨10154⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by simpa [mem13] using rd7144⟩

theorem endSkimX_gapAddReturns {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {vatOut urnOut rdata : ByteArray} {k C : ℕ}
    (hsz68 : 68 ≤ I.calldata.size)
    (hloVat : 160 ≤ vatOut.size)
    (hfitGap :
      (endSkimGapWord σ' I).toNat + (endSkimDiffWord σ' I vatOut urnOut).toNat <
        UInt256.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7113⟩
      (endSkimWadWord σ' I vatOut urnOut :: ⟨0⟩ ::
        endSkimOweWord σ' I vatOut urnOut :: endFreeUrnArtWord urnOut ::
        endFreeUrnInkWord urnOut :: endFlowVatIlkRateWord vatOut :: endSkimUrnKey I ::
        endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      (endSkimTagHashMem I vatOut urnOut) (UInt256.ofNat 9) rdata (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7150⟩
      (endSkimGapNewWord σ' I vatOut urnOut :: endSkimWadWord σ' I vatOut urnOut ::
        endSkimOweWord σ' I vatOut urnOut :: endFreeUrnArtWord urnOut ::
        endFreeUrnInkWord urnOut :: endFlowVatIlkRateWord vatOut :: endSkimUrnKey I ::
        endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      (endSkimGapHashMem I vatOut urnOut) (UInt256.ofNat 9) rdata (cA', σ') k' C' := by
  obtain ⟨_, _, rd10154⟩ := endSkimX_gapSubEntry hsz68 hloVat h
  obtain ⟨_, _, rd7145raw⟩ :=
    RD.solcCheckedSubSuccess
      (pc := ⟨10154⟩) (okPc := ⟨10108⟩)
      (a := endSkimOweWord σ' I vatOut urnOut)
      (b := endSkimWadWord σ' I vatOut urnOut)
      (ret := ⟨7145⟩)
      (R := [endSkimGapWord σ' I, ⟨7150⟩, endSkimWadWord σ' I vatOut urnOut,
        endSkimOweWord σ' I vatOut urnOut, endFreeUrnArtWord urnOut,
        endFreeUrnInkWord urnOut, endFlowVatIlkRateWord vatOut, endSkimUrnKey I,
        endSkimIlkWord I, endSkimReturnPc, sel])
      rd10154
      (by
        unfold solcCheckedSubSuccessWf
        repeat' first | apply And.intro | native_decide)
      (by
        unfold endSkimWadWord
        by_cases hle :
            (endFreeUrnInkWord urnOut).toNat ≤
              (endSkimOweWord σ' I vatOut urnOut).toNat
        · simp [hle]
        · simp [hle])
      (by jump_dest) (by jump_dest)
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd7145⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7145⟩
        (endSkimDiffWord σ' I vatOut urnOut :: endSkimGapWord σ' I :: ⟨7150⟩ ::
          endSkimWadWord σ' I vatOut urnOut ::
          endSkimOweWord σ' I vatOut urnOut :: endFreeUrnArtWord urnOut ::
          endFreeUrnInkWord urnOut :: endFlowVatIlkRateWord vatOut ::
          endSkimUrnKey I :: endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
        (endSkimGapHashMem I vatOut urnOut) (UInt256.ofNat 9) rdata
        (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [endSkimDiffWord] using rd7145raw⟩
  have rd10092 := evm_run rd7145 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨10092⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have hfitGapComm :
      (endSkimDiffWord σ' I vatOut urnOut).toNat + (endSkimGapWord σ' I).toNat <
        UInt256.size := by
    simpa [Nat.add_comm] using hfitGap
  have haddNat :
      (endSkimDiffWord σ' I vatOut urnOut + endSkimGapWord σ' I).toNat =
        (endSkimDiffWord σ' I vatOut urnOut).toNat + (endSkimGapWord σ' I).toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt hfitGapComm]
  have hlt :
      UInt256.lt (endSkimDiffWord σ' I vatOut urnOut + endSkimGapWord σ' I)
        (endSkimGapWord σ' I) = ⟨0⟩ :=
    ult_zero (by rw [haddNat]; omega)
  have rd10103pre := evm_run rd10092 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨10108⟩ (by native_decide) (by evm_ov)]
  rw [hlt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd10103pre
  have rd7150raw := evm_run rd10103pre with [
    raw jumpiT (by native_decide) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by jump_dest) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by
    simpa [endSkimGapNewWord, u256_add_comm (endSkimGapWord σ' I)
      (endSkimDiffWord σ' I vatOut urnOut)] using rd7150raw⟩

theorem endSkimX_gapAddOverflow {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {vatOut urnOut rdata : ByteArray} {k C : ℕ}
    (hsz68 : 68 ≤ I.calldata.size)
    (hloVat : 160 ≤ vatOut.size)
    (hover :
      UInt256.size ≤
        (endSkimGapWord σ' I).toNat + (endSkimDiffWord σ' I vatOut urnOut).toNat)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7113⟩
      (endSkimWadWord σ' I vatOut urnOut :: ⟨0⟩ ::
        endSkimOweWord σ' I vatOut urnOut :: endFreeUrnArtWord urnOut ::
        endFreeUrnInkWord urnOut :: endFlowVatIlkRateWord vatOut :: endSkimUrnKey I ::
        endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      (endSkimTagHashMem I vatOut urnOut) (UInt256.ofNat 9) rdata (cA', σ') k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd10154⟩ := endSkimX_gapSubEntry hsz68 hloVat h
  obtain ⟨_, _, rd7145raw⟩ :=
    RD.solcCheckedSubSuccess
      (pc := ⟨10154⟩) (okPc := ⟨10108⟩)
      (a := endSkimOweWord σ' I vatOut urnOut)
      (b := endSkimWadWord σ' I vatOut urnOut)
      (ret := ⟨7145⟩)
      (R := [endSkimGapWord σ' I, ⟨7150⟩, endSkimWadWord σ' I vatOut urnOut,
        endSkimOweWord σ' I vatOut urnOut, endFreeUrnArtWord urnOut,
        endFreeUrnInkWord urnOut, endFlowVatIlkRateWord vatOut, endSkimUrnKey I,
        endSkimIlkWord I, endSkimReturnPc, sel])
      rd10154
      (by
        unfold solcCheckedSubSuccessWf
        repeat' first | apply And.intro | native_decide)
      (by
        unfold endSkimWadWord
        by_cases hle :
            (endFreeUrnInkWord urnOut).toNat ≤
              (endSkimOweWord σ' I vatOut urnOut).toNat
        · simp [hle]
        · simp [hle])
      (by jump_dest) (by jump_dest)
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd7145⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7145⟩
        (endSkimDiffWord σ' I vatOut urnOut :: endSkimGapWord σ' I :: ⟨7150⟩ ::
          endSkimWadWord σ' I vatOut urnOut ::
          endSkimOweWord σ' I vatOut urnOut :: endFreeUrnArtWord urnOut ::
          endFreeUrnInkWord urnOut :: endFlowVatIlkRateWord vatOut ::
          endSkimUrnKey I :: endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
        (endSkimGapHashMem I vatOut urnOut) (UInt256.ofNat 9) rdata
        (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [endSkimDiffWord] using rd7145raw⟩
  have rd10092 := evm_run rd7145 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨10092⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  let gap := endSkimGapWord σ' I
  let diff := endSkimDiffWord σ' I vatOut urnOut
  have hover' : UInt256.size ≤ diff.toNat + gap.toNat := by
    dsimp [gap, diff]
    simpa [Nat.add_comm] using hover
  have hsum_lt2 : diff.toNat + gap.toNat < 2 * UInt256.size := by
    have hdiff : diff.toNat < UInt256.size := diff.val.isLt
    have hgap : gap.toNat < UInt256.size := gap.val.isLt
    omega
  have hmod : (diff.toNat + gap.toNat) % UInt256.size =
      diff.toNat + gap.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover']
    exact Nat.mod_eq_of_lt (by omega)
  have haddNat : (diff + gap).toNat = diff.toNat + gap.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  have hlt : UInt256.lt (diff + gap) gap = ⟨1⟩ := by
    apply ult_one
    rw [haddNat]
    have hdiffLt : diff.toNat < UInt256.size := diff.val.isLt
    omega
  have rd10099pre := evm_run rd10092 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd10099 := evm_run rd10099pre with [raw lt (by native_decide) (by evm_ov)]
  have rd10099' := by
    simpa [gap, diff] using rd10099
  rw [hlt] at rd10099'
  have rd10100pre := evm_run rd10099' with [raw iszero (by native_decide) (by evm_ov)]
  have rd10100 := by
    simpa using rd10100pre
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd10100
  have rd10104pre := evm_run rd10100 with [raw push2 ⟨10108⟩ (by native_decide) (by evm_ov)]
  have rd10104 := rd10104pre.jumpiNT (by native_decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact RD.solcPush1Dup1Revert0 rd10104 (by native_decide) (by native_decide)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkimGapStoreHashMem_size (I : ExecutionEnv) (vatOut urnOut : ByteArray)
    (hloVat : 160 ≤ vatOut.size) :
    (endSkimGapStoreHashMem I vatOut urnOut).size = 288 := by
  let key := endSkimIlkWord I
  let mem0 := endSkimUrnsPostCallMem I vatOut urnOut
  let mem12 := endSkimTagHashMem I vatOut urnOut
  let mem13 := endSkimGapHashMem I vatOut urnOut
  have hpostSize : mem0.size = 288 := by
    simpa [mem0] using endSkimUrnsPostCallMem_size I vatOut urnOut hloVat
  have hmem12Size : mem12.size = mem0.size := by
    exact endFlow_twoWordHashMem_size_of_ge64 key ⟨12⟩
      (by rw [hpostSize]; omega)
  have hmem13Size : mem13.size = mem12.size := by
    exact endFlow_twoWordHashMem_size_of_ge64 key ⟨13⟩
      (by rw [hmem12Size, hpostSize]; omega)
  have hmemStoreSize : (twoWordHashMem key ⟨13⟩ mem13).size = mem13.size := by
    exact endFlow_twoWordHashMem_size_of_ge64 key ⟨13⟩
      (by rw [hmem13Size, hmem12Size, hpostSize]; omega)
  simpa [endSkimGapStoreHashMem, key, mem13, hmemStoreSize, hmem13Size, hmem12Size,
    hpostSize]

theorem endSkimGapStoreHashMem_read64 (I : ExecutionEnv) (vatOut urnOut : ByteArray)
    (hloVat : 160 ≤ vatOut.size) :
    (endSkimGapStoreHashMem I vatOut urnOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  let key := endSkimIlkWord I
  let mem0 := endSkimUrnsPostCallMem I vatOut urnOut
  let mem12 := endSkimTagHashMem I vatOut urnOut
  let mem13 := endSkimGapHashMem I vatOut urnOut
  have hpostSize : mem0.size = 288 := by
    simpa [mem0] using endSkimUrnsPostCallMem_size I vatOut urnOut hloVat
  have hpostRead64 :
      mem0.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [mem0] using endSkimUrnsPostCallMem_read64 I vatOut urnOut hloVat
  have hmem12Size : mem12.size = mem0.size := by
    exact endFlow_twoWordHashMem_size_of_ge64 key ⟨12⟩
      (by rw [hpostSize]; omega)
  have hmem12Read64 :
      mem12.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [mem12, endSkimTagHashMem, key] using
      endFlow_twoWordHashMem_read64_of_ge96 key ⟨12⟩
        (by rw [hpostSize]; omega) hpostRead64
  have hmem13Size : mem13.size = mem12.size := by
    exact endFlow_twoWordHashMem_size_of_ge64 key ⟨13⟩
      (by rw [hmem12Size, hpostSize]; omega)
  have hmem13Read64 :
      mem13.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [mem13, endSkimGapHashMem, key] using
      endFlow_twoWordHashMem_read64_of_ge96 key ⟨13⟩
        (by rw [hmem12Size, hpostSize]; omega) hmem12Read64
  simpa [endSkimGapStoreHashMem, key, mem13] using
    endFlow_twoWordHashMem_read64_of_ge96 key ⟨13⟩
      (by rw [hmem13Size, hmem12Size, hpostSize]; omega) hmem13Read64

theorem endSkimGrabMem7_eq (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) :
    endSkimGrabMem7 σ I vatOut urnOut =
      endSkimGrabCalldataMem σ I vatOut urnOut := by
  rfl

theorem endSkimGrabCalldataMem_size (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimGrabCalldataMem σ I vatOut urnOut).size = 324 := by
  unfold endSkimGrabCalldataMem endSkimGrabWrites
  exact writeCascade_size_of_base (endSkimGapStoreHashMem I vatOut urnOut)
    [ (128, endFreeGrabSelectorShifted),
      (132, endSkimIlkWord I),
      (164, endSkimUrnKey I),
      (196, endSkimThisWord I),
      (228, endPackVowWord σ I),
      (260, endSkimGrabDinkWord σ I vatOut urnOut),
      (292, endSkimGrabDartWord urnOut) ]
    (endSkimGapStoreHashMem_size I vatOut urnOut hloVat)
    (by simp [WriteGapsOk]) (by simp [writeCascadeSize])

theorem endSkimGrabCalldataMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimGrabCalldataMem σ I vatOut urnOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSkimGrabCalldataMem endSkimGrabWrites
  rw [writeCascade_read_preserved_of_base (endSkimGapStoreHashMem I vatOut urnOut)
    [ (128, endFreeGrabSelectorShifted),
      (132, endSkimIlkWord I),
      (164, endSkimUrnKey I),
      (196, endSkimThisWord I),
      (228, endPackVowWord σ I),
      (260, endSkimGrabDinkWord σ I vatOut urnOut),
      (292, endSkimGrabDartWord urnOut) ]
    (endSkimGapStoreHashMem_size I vatOut urnOut hloVat)
    (by simp [WindowDisjointFromWrites])]
  exact endSkimGapStoreHashMem_read64 I vatOut urnOut hloVat

theorem endSkimGrabPostCallMem_eq (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut ret : ByteArray) :
    endSkimGrabPostCallMem σ I vatOut urnOut ret =
      endSkimGrabCalldataMem σ I vatOut urnOut := by
  unfold endSkimGrabPostCallMem
  have hmin : (min endFreeGrabOutSize (UInt256.ofNat ret.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat ret.size := by
      show (0 : Nat) ≤ (UInt256.ofNat ret.size).toNat
      exact Nat.zero_le _
    simp [endFreeGrabOutSize, min, hle]
  rw [hmin]
  exact byteArray_write_len_zero ret (endSkimGrabCalldataMem σ I vatOut urnOut)
    0 endFreeGrabOutPtr.toNat

theorem endSkimGrabCalldataMem_read128_4 (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimGrabCalldataMem σ I vatOut urnOut).readWithPadding 128 4 =
      grabSelector := by
  unfold endSkimGrabCalldataMem endSkimGrabWrites
  rw [writeCascade_read_window_of_head (endSkimGapStoreHashMem I vatOut urnOut)
    128 0 4 endFreeGrabSelectorShifted
    [ (132, endSkimIlkWord I),
      (164, endSkimUrnKey I),
      (196, endSkimThisWord I),
      (228, endPackVowWord σ I),
      (260, endSkimGrabDinkWord σ I vatOut urnOut),
      (292, endSkimGrabDartWord urnOut) ]]
  · unfold endFreeGrabSelectorShifted grabSelector selectorBytes
    native_decide
  · rw [endSkimGapStoreHashMem_size I vatOut urnOut hloVat]
    native_decide
  · simp [WindowDisjointFromWrites]
  · norm_num
  · norm_num
  · norm_num

theorem endSkimGrabCalldataMem_read132_32 (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimGrabCalldataMem σ I vatOut urnOut).readWithPadding 132 32 =
      (endSkimIlkWord I).toByteArray := by
  unfold endSkimGrabCalldataMem endSkimGrabWrites
  rw [writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord (endSkimGapStoreHashMem I vatOut urnOut) 128 endFreeGrabSelectorShifted)
    (word := endSkimIlkWord I)
    (rest :=
      [ (164, endSkimUrnKey I),
        (196, endSkimThisWord I),
        (228, endPackVowWord σ I),
        (260, endSkimGrabDinkWord σ I vatOut urnOut),
        (292, endSkimGrabDartWord urnOut) ])
    (hbase := by
      rw [writeWord_size]
      · rw [endSkimGapStoreHashMem_size I vatOut urnOut hloVat]
        native_decide)
    (hgap := by
      rw [endSkimGapStoreHashMem_size I vatOut urnOut hloVat]
      native_decide)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSkimGrabCalldataMem_read164_32 (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimGrabCalldataMem σ I vatOut urnOut).readWithPadding 164 32 =
      (endSkimUrnKey I).toByteArray := by
  unfold endSkimGrabCalldataMem endSkimGrabWrites
  rw [writeCascade_cons, writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord (endSkimGapStoreHashMem I vatOut urnOut) 128 endFreeGrabSelectorShifted)
      132 (endSkimIlkWord I))
    (word := endSkimUrnKey I)
    (rest :=
      [ (196, endSkimThisWord I),
        (228, endPackVowWord σ I),
        (260, endSkimGrabDinkWord σ I vatOut urnOut),
        (292, endSkimGrabDartWord urnOut) ])
    (hbase := by
      change (writeCascade (endSkimGapStoreHashMem I vatOut urnOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkimIlkWord I)]).size = 288
      exact writeCascade_size_of_base (endSkimGapStoreHashMem I vatOut urnOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkimIlkWord I)]
        (endSkimGapStoreHashMem_size I vatOut urnOut hloVat)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by
      native_decide)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSkimGrabCalldataMem_read196_32 (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimGrabCalldataMem σ I vatOut urnOut).readWithPadding 196 32 =
      (endSkimThisWord I).toByteArray := by
  unfold endSkimGrabCalldataMem endSkimGrabWrites
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord
        (writeWord (endSkimGapStoreHashMem I vatOut urnOut) 128 endFreeGrabSelectorShifted)
        132 (endSkimIlkWord I))
      164 (endSkimUrnKey I))
    (word := endSkimThisWord I)
    (rest :=
      [ (228, endPackVowWord σ I),
        (260, endSkimGrabDinkWord σ I vatOut urnOut),
        (292, endSkimGrabDartWord urnOut) ])
    (hbase := by
      change (writeCascade (endSkimGapStoreHashMem I vatOut urnOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkimIlkWord I),
          (164, endSkimUrnKey I)]).size = 288
      exact writeCascade_size_of_base (endSkimGapStoreHashMem I vatOut urnOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkimIlkWord I),
          (164, endSkimUrnKey I)]
        (endSkimGapStoreHashMem_size I vatOut urnOut hloVat)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by
      native_decide)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSkimGrabCalldataMem_read228_32 (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimGrabCalldataMem σ I vatOut urnOut).readWithPadding 228 32 =
      (endPackVowWord σ I).toByteArray := by
  unfold endSkimGrabCalldataMem endSkimGrabWrites
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons, writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord
        (writeWord
          (writeWord (endSkimGapStoreHashMem I vatOut urnOut) 128 endFreeGrabSelectorShifted)
          132 (endSkimIlkWord I))
        164 (endSkimUrnKey I))
      196 (endSkimThisWord I))
    (word := endPackVowWord σ I)
    (rest :=
      [ (260, endSkimGrabDinkWord σ I vatOut urnOut),
        (292, endSkimGrabDartWord urnOut) ])
    (hbase := by
      change (writeCascade (endSkimGapStoreHashMem I vatOut urnOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkimIlkWord I),
          (164, endSkimUrnKey I), (196, endSkimThisWord I)]).size = 288
      exact writeCascade_size_of_base (endSkimGapStoreHashMem I vatOut urnOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkimIlkWord I),
          (164, endSkimUrnKey I), (196, endSkimThisWord I)]
        (endSkimGapStoreHashMem_size I vatOut urnOut hloVat)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by
      native_decide)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSkimGrabCalldataMem_read260_32 (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimGrabCalldataMem σ I vatOut urnOut).readWithPadding 260 32 =
      (endSkimGrabDinkWord σ I vatOut urnOut).toByteArray := by
  unfold endSkimGrabCalldataMem endSkimGrabWrites
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons, writeCascade_cons,
    writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord
        (writeWord
          (writeWord
            (writeWord (endSkimGapStoreHashMem I vatOut urnOut) 128 endFreeGrabSelectorShifted)
            132 (endSkimIlkWord I))
          164 (endSkimUrnKey I))
        196 (endSkimThisWord I))
      228 (endPackVowWord σ I))
    (word := endSkimGrabDinkWord σ I vatOut urnOut)
    (rest := [ (292, endSkimGrabDartWord urnOut) ])
    (hbase := by
      change (writeCascade (endSkimGapStoreHashMem I vatOut urnOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkimIlkWord I),
          (164, endSkimUrnKey I), (196, endSkimThisWord I),
          (228, endPackVowWord σ I)]).size = 288
      exact writeCascade_size_of_base (endSkimGapStoreHashMem I vatOut urnOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkimIlkWord I),
          (164, endSkimUrnKey I), (196, endSkimThisWord I),
          (228, endPackVowWord σ I)]
        (endSkimGapStoreHashMem_size I vatOut urnOut hloVat)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by
      native_decide)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSkimGrabCalldataMem_read292_32 (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimGrabCalldataMem σ I vatOut urnOut).readWithPadding 292 32 =
      (endSkimGrabDartWord urnOut).toByteArray := by
  unfold endSkimGrabCalldataMem endSkimGrabWrites
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons, writeCascade_cons,
    writeCascade_cons, writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord
        (writeWord
          (writeWord
            (writeWord
              (writeWord (endSkimGapStoreHashMem I vatOut urnOut) 128
                endFreeGrabSelectorShifted)
              132 (endSkimIlkWord I))
            164 (endSkimUrnKey I))
          196 (endSkimThisWord I))
        228 (endPackVowWord σ I))
      260 (endSkimGrabDinkWord σ I vatOut urnOut))
    (word := endSkimGrabDartWord urnOut)
    (rest := [])
    (hbase := by
      change (writeCascade (endSkimGapStoreHashMem I vatOut urnOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkimIlkWord I),
          (164, endSkimUrnKey I), (196, endSkimThisWord I),
          (228, endPackVowWord σ I),
          (260, endSkimGrabDinkWord σ I vatOut urnOut)]).size = 292
      exact writeCascade_size_of_base (endSkimGapStoreHashMem I vatOut urnOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkimIlkWord I),
          (164, endSkimUrnKey I), (196, endSkimThisWord I),
          (228, endPackVowWord σ I),
          (260, endSkimGrabDinkWord σ I vatOut urnOut)]
        (endSkimGapStoreHashMem_size I vatOut urnOut hloVat)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by
      native_decide)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSkimGrabCalldataMem_read128_196 (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimGrabCalldataMem σ I vatOut urnOut).readWithPadding 128 196 =
      grabSelector ++
        (endSkimIlkWord I).toByteArray ++
        (endSkimUrnKey I).toByteArray ++
        (endSkimThisWord I).toByteArray ++
        (endPackVowWord σ I).toByteArray ++
        (endSkimGrabDinkWord σ I vatOut urnOut).toByteArray ++
        (endSkimGrabDartWord urnOut).toByteArray := by
  have hsize : (endSkimGrabCalldataMem σ I vatOut urnOut).size = 324 :=
    endSkimGrabCalldataMem_size σ I vatOut urnOut hloVat
  rw [show 196 = 4 + 192 from rfl,
    byteArray_readWithPadding_split (endSkimGrabCalldataMem σ I vatOut urnOut) 128 4 192
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 192 = 32 + 160 from rfl,
    byteArray_readWithPadding_split (endSkimGrabCalldataMem σ I vatOut urnOut) 132 32 160
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 160 = 32 + 128 from rfl,
    byteArray_readWithPadding_split (endSkimGrabCalldataMem σ I vatOut urnOut) 164 32 128
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 128 = 32 + 96 from rfl,
    byteArray_readWithPadding_split (endSkimGrabCalldataMem σ I vatOut urnOut) 196 32 96
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 96 = 32 + 64 from rfl,
    byteArray_readWithPadding_split (endSkimGrabCalldataMem σ I vatOut urnOut) 228 32 64
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (endSkimGrabCalldataMem σ I vatOut urnOut) 260 32 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [endSkimGrabCalldataMem_read128_4 σ I vatOut urnOut hloVat,
    endSkimGrabCalldataMem_read132_32 σ I vatOut urnOut hloVat,
    endSkimGrabCalldataMem_read164_32 σ I vatOut urnOut hloVat,
    endSkimGrabCalldataMem_read196_32 σ I vatOut urnOut hloVat,
    endSkimGrabCalldataMem_read228_32 σ I vatOut urnOut hloVat,
    endSkimGrabCalldataMem_read260_32 σ I vatOut urnOut hloVat,
    endSkimGrabCalldataMem_read292_32 σ I vatOut urnOut hloVat]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem endSkimGrabPostCallMem_size (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut ret : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimGrabPostCallMem σ I vatOut urnOut ret).size = 324 := by
  rw [endSkimGrabPostCallMem_eq]
  exact endSkimGrabCalldataMem_size σ I vatOut urnOut hloVat

theorem endSkimGrabPostCallMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut ret : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimGrabPostCallMem σ I vatOut urnOut ret).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [endSkimGrabPostCallMem_eq]
  exact endSkimGrabCalldataMem_read64 σ I vatOut urnOut hloVat

theorem endSkimLogDataMem_size (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut ret : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimLogDataMem σ I vatOut urnOut ret).size = 324 := by
  unfold endSkimLogDataMem
  rw [endSkimGrabPostCallMem_eq]
  exact toByteArray_write32_size_of_le (endSkimGrabCalldataMem σ I vatOut urnOut)
    (endSkimWadWord σ I vatOut urnOut) 128 324 324
    (endSkimGrabCalldataMem_size σ I vatOut urnOut hloVat)
    (by rw [endSkimGrabCalldataMem_size σ I vatOut urnOut hloVat]; omega) (by omega)

theorem endSkimLogDataMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut ret : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimLogDataMem σ I vatOut urnOut ret).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSkimLogDataMem
  rw [toByteArray_write_read_below_of_gap (endSkimWadWord σ I vatOut urnOut)
    (endSkimGrabPostCallMem σ I vatOut urnOut ret) 128 64
    (by rw [endSkimGrabPostCallMem_eq,
      endSkimGrabCalldataMem_size σ I vatOut urnOut hloVat]; omega)
    (by omega)
    (by rw [endSkimGrabPostCallMem_eq,
      endSkimGrabCalldataMem_size σ I vatOut urnOut hloVat]; native_decide)]
  exact endSkimGrabPostCallMem_read64 σ I vatOut urnOut ret hloVat

theorem endSkimGrabMem7For_eq (σCall σLoc : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) :
    endSkimGrabMem7For σCall σLoc I vatOut urnOut =
      endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut := by
  rfl

theorem endSkimGrabCalldataMemFor_size (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (vatOut urnOut : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut).size = 324 := by
  unfold endSkimGrabCalldataMemFor endSkimGrabWritesFor
  exact writeCascade_size_of_base (endSkimGapStoreHashMem I vatOut urnOut)
    [ (128, endFreeGrabSelectorShifted),
      (132, endSkimIlkWord I),
      (164, endSkimUrnKey I),
      (196, endSkimThisWord I),
      (228, endPackVowWord σCall I),
      (260, endSkimGrabDinkWord σLoc I vatOut urnOut),
      (292, endSkimGrabDartWord urnOut) ]
    (endSkimGapStoreHashMem_size I vatOut urnOut hloVat)
    (by simp [WriteGapsOk]) (by simp [writeCascadeSize])

theorem endSkimGrabCalldataMemFor_read64 (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (vatOut urnOut : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSkimGrabCalldataMemFor endSkimGrabWritesFor
  rw [writeCascade_read_preserved_of_base (endSkimGapStoreHashMem I vatOut urnOut)
    [ (128, endFreeGrabSelectorShifted),
      (132, endSkimIlkWord I),
      (164, endSkimUrnKey I),
      (196, endSkimThisWord I),
      (228, endPackVowWord σCall I),
      (260, endSkimGrabDinkWord σLoc I vatOut urnOut),
      (292, endSkimGrabDartWord urnOut) ]
    (endSkimGapStoreHashMem_size I vatOut urnOut hloVat)
    (by simp [WindowDisjointFromWrites])]
  exact endSkimGapStoreHashMem_read64 I vatOut urnOut hloVat

theorem endSkimGrabPostCallMemFor_eq (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (vatOut urnOut ret : ByteArray) :
    endSkimGrabPostCallMemFor σCall σLoc I vatOut urnOut ret =
      endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut := by
  unfold endSkimGrabPostCallMemFor
  have hmin : (min endFreeGrabOutSize (UInt256.ofNat ret.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat ret.size := by
      show (0 : Nat) ≤ (UInt256.ofNat ret.size).toNat
      exact Nat.zero_le _
    simp [endFreeGrabOutSize, min, hle]
  rw [hmin]
  exact byteArray_write_len_zero ret (endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut)
    0 endFreeGrabOutPtr.toNat

theorem endSkimGrabCalldataMemFor_read128_4 (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (vatOut urnOut : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut).readWithPadding 128 4 =
      grabSelector := by
  unfold endSkimGrabCalldataMemFor endSkimGrabWritesFor
  rw [writeCascade_read_window_of_head (endSkimGapStoreHashMem I vatOut urnOut)
    128 0 4 endFreeGrabSelectorShifted
    [ (132, endSkimIlkWord I),
      (164, endSkimUrnKey I),
      (196, endSkimThisWord I),
      (228, endPackVowWord σCall I),
      (260, endSkimGrabDinkWord σLoc I vatOut urnOut),
      (292, endSkimGrabDartWord urnOut) ]]
  · unfold endFreeGrabSelectorShifted grabSelector selectorBytes
    native_decide
  · rw [endSkimGapStoreHashMem_size I vatOut urnOut hloVat]
    native_decide
  · simp [WindowDisjointFromWrites]
  · norm_num
  · norm_num
  · norm_num

theorem endSkimGrabCalldataMemFor_read132_32 (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (vatOut urnOut : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut).readWithPadding 132 32 =
      (endSkimIlkWord I).toByteArray := by
  unfold endSkimGrabCalldataMemFor endSkimGrabWritesFor
  rw [writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord (endSkimGapStoreHashMem I vatOut urnOut) 128 endFreeGrabSelectorShifted)
    (word := endSkimIlkWord I)
    (rest :=
      [ (164, endSkimUrnKey I),
        (196, endSkimThisWord I),
        (228, endPackVowWord σCall I),
        (260, endSkimGrabDinkWord σLoc I vatOut urnOut),
        (292, endSkimGrabDartWord urnOut) ])
    (hbase := by
      rw [writeWord_size]
      · rw [endSkimGapStoreHashMem_size I vatOut urnOut hloVat]
        native_decide)
    (hgap := by
      rw [endSkimGapStoreHashMem_size I vatOut urnOut hloVat]
      native_decide)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSkimGrabCalldataMemFor_read164_32 (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (vatOut urnOut : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut).readWithPadding 164 32 =
      (endSkimUrnKey I).toByteArray := by
  unfold endSkimGrabCalldataMemFor endSkimGrabWritesFor
  rw [writeCascade_cons, writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord (endSkimGapStoreHashMem I vatOut urnOut) 128 endFreeGrabSelectorShifted)
      132 (endSkimIlkWord I))
    (word := endSkimUrnKey I)
    (rest :=
      [ (196, endSkimThisWord I),
        (228, endPackVowWord σCall I),
        (260, endSkimGrabDinkWord σLoc I vatOut urnOut),
        (292, endSkimGrabDartWord urnOut) ])
    (hbase := by
      change (writeCascade (endSkimGapStoreHashMem I vatOut urnOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkimIlkWord I)]).size = 288
      exact writeCascade_size_of_base (endSkimGapStoreHashMem I vatOut urnOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkimIlkWord I)]
        (endSkimGapStoreHashMem_size I vatOut urnOut hloVat)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by
      native_decide)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSkimGrabCalldataMemFor_read196_32 (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (vatOut urnOut : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut).readWithPadding 196 32 =
      (endSkimThisWord I).toByteArray := by
  unfold endSkimGrabCalldataMemFor endSkimGrabWritesFor
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord
        (writeWord (endSkimGapStoreHashMem I vatOut urnOut) 128 endFreeGrabSelectorShifted)
        132 (endSkimIlkWord I))
      164 (endSkimUrnKey I))
    (word := endSkimThisWord I)
    (rest :=
      [ (228, endPackVowWord σCall I),
        (260, endSkimGrabDinkWord σLoc I vatOut urnOut),
        (292, endSkimGrabDartWord urnOut) ])
    (hbase := by
      change (writeCascade (endSkimGapStoreHashMem I vatOut urnOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkimIlkWord I),
          (164, endSkimUrnKey I)]).size = 288
      exact writeCascade_size_of_base (endSkimGapStoreHashMem I vatOut urnOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkimIlkWord I),
          (164, endSkimUrnKey I)]
        (endSkimGapStoreHashMem_size I vatOut urnOut hloVat)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by
      native_decide)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSkimGrabCalldataMemFor_read228_32 (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (vatOut urnOut : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut).readWithPadding 228 32 =
      (endPackVowWord σCall I).toByteArray := by
  unfold endSkimGrabCalldataMemFor endSkimGrabWritesFor
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons, writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord
        (writeWord
          (writeWord (endSkimGapStoreHashMem I vatOut urnOut) 128 endFreeGrabSelectorShifted)
          132 (endSkimIlkWord I))
        164 (endSkimUrnKey I))
      196 (endSkimThisWord I))
    (word := endPackVowWord σCall I)
    (rest :=
      [ (260, endSkimGrabDinkWord σLoc I vatOut urnOut),
        (292, endSkimGrabDartWord urnOut) ])
    (hbase := by
      change (writeCascade (endSkimGapStoreHashMem I vatOut urnOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkimIlkWord I),
          (164, endSkimUrnKey I), (196, endSkimThisWord I)]).size = 288
      exact writeCascade_size_of_base (endSkimGapStoreHashMem I vatOut urnOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkimIlkWord I),
          (164, endSkimUrnKey I), (196, endSkimThisWord I)]
        (endSkimGapStoreHashMem_size I vatOut urnOut hloVat)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by
      native_decide)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSkimGrabCalldataMemFor_read260_32 (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (vatOut urnOut : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut).readWithPadding 260 32 =
      (endSkimGrabDinkWord σLoc I vatOut urnOut).toByteArray := by
  unfold endSkimGrabCalldataMemFor endSkimGrabWritesFor
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons, writeCascade_cons,
    writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord
        (writeWord
          (writeWord
            (writeWord (endSkimGapStoreHashMem I vatOut urnOut) 128 endFreeGrabSelectorShifted)
            132 (endSkimIlkWord I))
          164 (endSkimUrnKey I))
        196 (endSkimThisWord I))
      228 (endPackVowWord σCall I))
    (word := endSkimGrabDinkWord σLoc I vatOut urnOut)
    (rest := [ (292, endSkimGrabDartWord urnOut) ])
    (hbase := by
      change (writeCascade (endSkimGapStoreHashMem I vatOut urnOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkimIlkWord I),
          (164, endSkimUrnKey I), (196, endSkimThisWord I),
          (228, endPackVowWord σCall I)]).size = 288
      exact writeCascade_size_of_base (endSkimGapStoreHashMem I vatOut urnOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkimIlkWord I),
          (164, endSkimUrnKey I), (196, endSkimThisWord I),
          (228, endPackVowWord σCall I)]
        (endSkimGapStoreHashMem_size I vatOut urnOut hloVat)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by
      native_decide)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSkimGrabCalldataMemFor_read292_32 (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (vatOut urnOut : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut).readWithPadding 292 32 =
      (endSkimGrabDartWord urnOut).toByteArray := by
  unfold endSkimGrabCalldataMemFor endSkimGrabWritesFor
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons, writeCascade_cons,
    writeCascade_cons, writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord
        (writeWord
          (writeWord
            (writeWord
              (writeWord (endSkimGapStoreHashMem I vatOut urnOut) 128
                endFreeGrabSelectorShifted)
              132 (endSkimIlkWord I))
            164 (endSkimUrnKey I))
          196 (endSkimThisWord I))
        228 (endPackVowWord σCall I))
      260 (endSkimGrabDinkWord σLoc I vatOut urnOut))
    (word := endSkimGrabDartWord urnOut)
    (rest := [])
    (hbase := by
      change (writeCascade (endSkimGapStoreHashMem I vatOut urnOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkimIlkWord I),
          (164, endSkimUrnKey I), (196, endSkimThisWord I),
          (228, endPackVowWord σCall I),
          (260, endSkimGrabDinkWord σLoc I vatOut urnOut)]).size = 292
      exact writeCascade_size_of_base (endSkimGapStoreHashMem I vatOut urnOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkimIlkWord I),
          (164, endSkimUrnKey I), (196, endSkimThisWord I),
          (228, endPackVowWord σCall I),
          (260, endSkimGrabDinkWord σLoc I vatOut urnOut)]
        (endSkimGapStoreHashMem_size I vatOut urnOut hloVat)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by
      native_decide)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSkimGrabCalldataMemFor_read128_196 (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (vatOut urnOut : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut).readWithPadding 128 196 =
      grabSelector ++
        (endSkimIlkWord I).toByteArray ++
        (endSkimUrnKey I).toByteArray ++
        (endSkimThisWord I).toByteArray ++
        (endPackVowWord σCall I).toByteArray ++
        (endSkimGrabDinkWord σLoc I vatOut urnOut).toByteArray ++
        (endSkimGrabDartWord urnOut).toByteArray := by
  have hsize : (endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut).size = 324 :=
    endSkimGrabCalldataMemFor_size σCall σLoc I vatOut urnOut hloVat
  rw [show 196 = 4 + 192 from rfl,
    byteArray_readWithPadding_split
      (endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut) 128 4 192
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 192 = 32 + 160 from rfl,
    byteArray_readWithPadding_split
      (endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut) 132 32 160
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 160 = 32 + 128 from rfl,
    byteArray_readWithPadding_split
      (endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut) 164 32 128
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 128 = 32 + 96 from rfl,
    byteArray_readWithPadding_split
      (endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut) 196 32 96
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 96 = 32 + 64 from rfl,
    byteArray_readWithPadding_split
      (endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut) 228 32 64
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split
      (endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut) 260 32 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [endSkimGrabCalldataMemFor_read128_4 σCall σLoc I vatOut urnOut hloVat,
    endSkimGrabCalldataMemFor_read132_32 σCall σLoc I vatOut urnOut hloVat,
    endSkimGrabCalldataMemFor_read164_32 σCall σLoc I vatOut urnOut hloVat,
    endSkimGrabCalldataMemFor_read196_32 σCall σLoc I vatOut urnOut hloVat,
    endSkimGrabCalldataMemFor_read228_32 σCall σLoc I vatOut urnOut hloVat,
    endSkimGrabCalldataMemFor_read260_32 σCall σLoc I vatOut urnOut hloVat,
    endSkimGrabCalldataMemFor_read292_32 σCall σLoc I vatOut urnOut hloVat]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem endSkimGrabPostCallMemFor_size (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (vatOut urnOut ret : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimGrabPostCallMemFor σCall σLoc I vatOut urnOut ret).size = 324 := by
  rw [endSkimGrabPostCallMemFor_eq]
  exact endSkimGrabCalldataMemFor_size σCall σLoc I vatOut urnOut hloVat

theorem endSkimGrabPostCallMemFor_read64 (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (vatOut urnOut ret : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimGrabPostCallMemFor σCall σLoc I vatOut urnOut ret).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [endSkimGrabPostCallMemFor_eq]
  exact endSkimGrabCalldataMemFor_read64 σCall σLoc I vatOut urnOut hloVat

theorem endSkimLogDataMemFor_size (σCall σLoc : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut ret : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimLogDataMemFor σCall σLoc I vatOut urnOut ret).size = 324 := by
  unfold endSkimLogDataMemFor
  rw [endSkimGrabPostCallMemFor_eq]
  exact toByteArray_write32_size_of_le
    (endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut)
    (endSkimWadWord σLoc I vatOut urnOut) 128 324 324
    (endSkimGrabCalldataMemFor_size σCall σLoc I vatOut urnOut hloVat)
    (by rw [endSkimGrabCalldataMemFor_size σCall σLoc I vatOut urnOut hloVat]; omega)
    (by omega)

theorem endSkimLogDataMemFor_read64 (σCall σLoc : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut ret : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimLogDataMemFor σCall σLoc I vatOut urnOut ret).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSkimLogDataMemFor
  rw [toByteArray_write_read_below_of_gap (endSkimWadWord σLoc I vatOut urnOut)
    (endSkimGrabPostCallMemFor σCall σLoc I vatOut urnOut ret) 128 64
    (by rw [endSkimGrabPostCallMemFor_eq,
      endSkimGrabCalldataMemFor_size σCall σLoc I vatOut urnOut hloVat]; omega)
    (by omega)
    (by rw [endSkimGrabPostCallMemFor_eq,
      endSkimGrabCalldataMemFor_size σCall σLoc I vatOut urnOut hloVat]; native_decide)]
  exact endSkimGrabPostCallMemFor_read64 σCall σLoc I vatOut urnOut ret hloVat

noncomputable def endSkimLogDataMem2For (σCall σLoc : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut ret : ByteArray) : ByteArray :=
  (endFreeUrnArtWord urnOut).toByteArray.write 0
    (endSkimLogDataMemFor σCall σLoc I vatOut urnOut ret) 160 32

theorem endSkimLogDataMem2For_size (σCall σLoc : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut ret : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimLogDataMem2For σCall σLoc I vatOut urnOut ret).size = 324 := by
  unfold endSkimLogDataMem2For
  exact toByteArray_write32_size_of_le
    (endSkimLogDataMemFor σCall σLoc I vatOut urnOut ret)
    (endFreeUrnArtWord urnOut) 160 324 324
    (endSkimLogDataMemFor_size σCall σLoc I vatOut urnOut ret hloVat)
    (by rw [endSkimLogDataMemFor_size σCall σLoc I vatOut urnOut ret hloVat]; omega)
    (by omega)

theorem endSkimLogDataMem2For_read64 (σCall σLoc : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut ret : ByteArray) (hloVat : 160 ≤ vatOut.size) :
    (endSkimLogDataMem2For σCall σLoc I vatOut urnOut ret).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSkimLogDataMem2For
  rw [toByteArray_write_read_below_of_gap (endFreeUrnArtWord urnOut)
    (endSkimLogDataMemFor σCall σLoc I vatOut urnOut ret) 160 64
    (by rw [endSkimLogDataMemFor_size σCall σLoc I vatOut urnOut ret hloVat]; omega)
    (by omega)
    (by rw [endSkimLogDataMemFor_size σCall σLoc I vatOut urnOut ret hloVat]; native_decide)]
  exact endSkimLogDataMemFor_read64 σCall σLoc I vatOut urnOut ret hloVat

theorem endSkimUrnWordOfAddr (I : ExecutionEnv) :
    EVM.word ↑(endSkimUrnAddr I) = endSkimUrnKey I := by
  change UInt256.ofNat (endSkimUrnAddr I).val = endSkimUrnKey I
  simpa [endSkimUrnAddr, endSkimUrnKey] using
    (keyValueToWord_address (AccountAddress.ofNat (endSkimUrnWord I).toNat)).symm.trans
      (keyValueToWord_address_ofNat_mask (endSkimUrnWord I))

theorem endSkimThisWordOfAddr (I : ExecutionEnv) :
    EVM.word ↑I.codeOwner = endSkimThisWord I := by
  change UInt256.ofNat I.codeOwner.val = endSkimThisWord I
  rfl

theorem endSkimGrabEncode_eq (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray)
    (hsz68 : 68 ≤ I.calldata.size) (hloVat : 160 ≤ vatOut.size)
    (hwad : (endSkimWadWord σ I vatOut urnOut).toNat ≤ 2 ^ 255)
    (hart : (endFreeUrnArtWord urnOut).toNat ≤ 2 ^ 255) :
    config.externalABI.encode? "grab"
        [.fixedBytes bytes32Width (endBytes32ArgBytes I),
          .address (endSkimUrnAddr I),
          .address I.codeOwner,
          .address (endPackVowAddr σ I),
          .int (-(Int.ofNat (endSkimWadWord σ I vatOut urnOut).toNat)),
          .int (-(Int.ofNat (endFreeUrnArtWord urnOut).toNat))] =
      some ((endSkimGrabCalldataMem σ I vatOut urnOut).readWithPadding
        endFreeGrabOutPtr.toNat endFreeGrabInSize.toNat) := by
  change config.externalABI.encode? "grab"
      [.fixedBytes bytes32Width (endBytes32ArgBytes I),
        .address (endSkimUrnAddr I),
        .address I.codeOwner,
        .address (endPackVowAddr σ I),
        .int (-(Int.ofNat (endSkimWadWord σ I vatOut urnOut).toNat)),
        .int (-(Int.ofNat (endFreeUrnArtWord urnOut).toNat))] =
    some ((endSkimGrabCalldataMem σ I vatOut urnOut).readWithPadding 128 196)
  rw [endSkimGrabCalldataMem_read128_196 σ I vatOut urnOut hloVat]
  have hbytes : endBytes32ArgBytes I = EVM.Word.toBytesBE (endSkimIlkWord I) := by
    have hlen32 : (endBytes32ArgBytes I).length = 32 :=
      endBytes32ArgBytes_len32 (I := I) (by omega)
    have hword : ABI.bytesToWord (endBytes32ArgBytes I) = endSkimIlkWord I := by
      simpa [endBytes32ArgBytes, endSkimIlkWord, endBytes32ArgWord] using
        (decode_word_at_eq_any I.calldata 4 (by omega))
    have hto := toBytesBE_bytesToWord_of_length (bs := endBytes32ArgBytes I) hlen32
    rw [hword] at hto
    exact hto.symm
  have hurnWord : EVM.word ↑(endSkimUrnAddr I) = endSkimUrnKey I :=
    endSkimUrnWordOfAddr I
  have hthisWord : EVM.word ↑I.codeOwner = endSkimThisWord I :=
    endSkimThisWordOfAddr I
  have hvowCanon : (endPackVowWord σ I).toNat < EVM.addressModulus := by
    simpa [endPackVowWord] using
      solcAddrMask_result_canonical (endSlotWord ⟨4⟩ σ I)
  have hvowVal :
      (endPackVowAddr σ I).val = (endPackVowWord σ I).toNat := by
    unfold endPackVowAddr AccountAddress.ofNat
    simp only [Fin.val_ofNat]
    apply Nat.mod_eq_of_lt
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hvowCanon
  have hvowWord : EVM.word ↑(endPackVowAddr σ I) = endPackVowWord σ I := by
    change UInt256.ofNat (endPackVowAddr σ I).val = endPackVowWord σ I
    rw [hvowVal]
    exact u256_ofNat_toNat _
  have hdinkWord :
      EVM.wordOfInt (-(Int.ofNat (endSkimWadWord σ I vatOut urnOut).toNat)) =
        endSkimGrabDinkWord σ I vatOut urnOut :=
    endFreeWordOfInt_neg_ofNat_toNat (endSkimWadWord σ I vatOut urnOut) hwad
  have hdinkWordCast :
      EVM.wordOfInt (-((endSkimWadWord σ I vatOut urnOut).toNat : Int)) =
        endSkimGrabDinkWord σ I vatOut urnOut := by
    simpa using hdinkWord
  have hdartWord :
      EVM.wordOfInt (-(Int.ofNat (endFreeUrnArtWord urnOut).toNat)) =
        endSkimGrabDartWord urnOut :=
    endFreeWordOfInt_neg_ofNat_toNat (endFreeUrnArtWord urnOut) hart
  have hdartWordCast :
      EVM.wordOfInt (-((endFreeUrnArtWord urnOut).toNat : Int)) =
        endSkimGrabDartWord urnOut := by
    simpa using hdartWord
  have hdinkBounds :
      -(Int.ofNat (EVM.twoPow (256 - 1))) ≤
          -(Int.ofNat (endSkimWadWord σ I vatOut urnOut).toNat) ∧
        -(Int.ofNat (endSkimWadWord σ I vatOut urnOut).toNat) <
          Int.ofNat (EVM.twoPow (256 - 1)) := by
    constructor
    · apply neg_le_neg
      exact Int.ofNat_le.mpr (by simpa [EVM.twoPow] using hwad)
    · have hnonpos :
          -(Int.ofNat (endSkimWadWord σ I vatOut urnOut).toNat) ≤ 0 := by
        exact neg_nonpos.mpr (Int.natCast_nonneg _)
      exact lt_of_le_of_lt hnonpos (by norm_num [EVM.twoPow])
  have hdartBounds :
      -(Int.ofNat (EVM.twoPow (256 - 1))) ≤
          -(Int.ofNat (endFreeUrnArtWord urnOut).toNat) ∧
        -(Int.ofNat (endFreeUrnArtWord urnOut).toNat) <
          Int.ofNat (EVM.twoPow (256 - 1)) := by
    constructor
    · apply neg_le_neg
      exact Int.ofNat_le.mpr (by simpa [EVM.twoPow] using hart)
    · have hnonpos : -(Int.ofNat (endFreeUrnArtWord urnOut).toNat) ≤ 0 := by
        exact neg_nonpos.mpr (Int.natCast_nonneg _)
      exact lt_of_le_of_lt hnonpos (by norm_num [EVM.twoPow])
  have hdinkBoundsSimp :
      (endSkimWadWord σ I vatOut urnOut).toNat ≤ EVM.twoPow 255 ∧
        -(Int.ofNat (endSkimWadWord σ I vatOut urnOut).toNat) <
          Int.ofNat (EVM.twoPow 255) := by
    constructor
    · simpa [EVM.twoPow] using hwad
    · simpa [EVM.twoPow] using hdinkBounds.2
  have hdartBoundsSimp :
      (endFreeUrnArtWord urnOut).toNat ≤ EVM.twoPow 255 ∧
        -(Int.ofNat (endFreeUrnArtWord urnOut).toNat) <
          Int.ofNat (EVM.twoPow 255) := by
    constructor
    · simpa [EVM.twoPow] using hart
    · simpa [EVM.twoPow] using hdartBounds.2
  have hdinkUpperCast :
      -((endSkimWadWord σ I vatOut urnOut).toNat : Int) < (EVM.twoPow 255 : Int) := by
    simpa using hdinkBoundsSimp.2
  have hdartUpperCast :
      -((endFreeUrnArtWord urnOut).toNat : Int) < (EVM.twoPow 255 : Int) := by
    simpa using hdartBoundsSimp.2
  have hbytesLen : (EVM.Word.toBytesBE (endSkimIlkWord I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (endSkimIlkWord I)
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, bytes32, bytes32Width, addr, int256,
    int256Int, grabSelector, selectorBytes, hbytes, hbytesLen, hurnWord, hthisWord,
    hvowWord, hdinkBoundsSimp, hdartBoundsSimp]
  rw [if_pos hdinkUpperCast, if_pos hdartUpperCast]
  simp [hdinkWordCast, hdartWordCast, word_toBytesBE_toByteArray_eq_toByteArray, zeroBytes,
    ByteArray.append_assoc]

theorem endSkimGrabEncodeFor_eq (σCall σLoc : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray)
    (hsz68 : 68 ≤ I.calldata.size) (hloVat : 160 ≤ vatOut.size)
    (hwad : (endSkimWadWord σLoc I vatOut urnOut).toNat ≤ 2 ^ 255)
    (hart : (endFreeUrnArtWord urnOut).toNat ≤ 2 ^ 255) :
    config.externalABI.encode? "grab"
        [.fixedBytes bytes32Width (endBytes32ArgBytes I),
          .address (endSkimUrnAddr I),
          .address I.codeOwner,
          .address (endPackVowAddr σCall I),
          .int (-(Int.ofNat (endSkimWadWord σLoc I vatOut urnOut).toNat)),
          .int (-(Int.ofNat (endFreeUrnArtWord urnOut).toNat))] =
      some ((endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut).readWithPadding
        endFreeGrabOutPtr.toNat endFreeGrabInSize.toNat) := by
  change config.externalABI.encode? "grab"
      [.fixedBytes bytes32Width (endBytes32ArgBytes I),
        .address (endSkimUrnAddr I),
        .address I.codeOwner,
        .address (endPackVowAddr σCall I),
        .int (-(Int.ofNat (endSkimWadWord σLoc I vatOut urnOut).toNat)),
        .int (-(Int.ofNat (endFreeUrnArtWord urnOut).toNat))] =
    some ((endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut).readWithPadding 128 196)
  rw [endSkimGrabCalldataMemFor_read128_196 σCall σLoc I vatOut urnOut hloVat]
  have hbytes : endBytes32ArgBytes I = EVM.Word.toBytesBE (endSkimIlkWord I) := by
    have hlen32 : (endBytes32ArgBytes I).length = 32 :=
      endBytes32ArgBytes_len32 (I := I) (by omega)
    have hword : ABI.bytesToWord (endBytes32ArgBytes I) = endSkimIlkWord I := by
      simpa [endBytes32ArgBytes, endSkimIlkWord, endBytes32ArgWord] using
        (decode_word_at_eq_any I.calldata 4 (by omega))
    have hto := toBytesBE_bytesToWord_of_length (bs := endBytes32ArgBytes I) hlen32
    rw [hword] at hto
    exact hto.symm
  have hurnWord : EVM.word ↑(endSkimUrnAddr I) = endSkimUrnKey I :=
    endSkimUrnWordOfAddr I
  have hthisWord : EVM.word ↑I.codeOwner = endSkimThisWord I :=
    endSkimThisWordOfAddr I
  have hvowCanon : (endPackVowWord σCall I).toNat < EVM.addressModulus := by
    simpa [endPackVowWord] using
      solcAddrMask_result_canonical (endSlotWord ⟨4⟩ σCall I)
  have hvowVal :
      (endPackVowAddr σCall I).val = (endPackVowWord σCall I).toNat := by
    unfold endPackVowAddr AccountAddress.ofNat
    simp only [Fin.val_ofNat]
    apply Nat.mod_eq_of_lt
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hvowCanon
  have hvowWord : EVM.word ↑(endPackVowAddr σCall I) = endPackVowWord σCall I := by
    change UInt256.ofNat (endPackVowAddr σCall I).val = endPackVowWord σCall I
    rw [hvowVal]
    exact u256_ofNat_toNat _
  have hdinkWord :
      EVM.wordOfInt (-(Int.ofNat (endSkimWadWord σLoc I vatOut urnOut).toNat)) =
        endSkimGrabDinkWord σLoc I vatOut urnOut :=
    endFreeWordOfInt_neg_ofNat_toNat (endSkimWadWord σLoc I vatOut urnOut) hwad
  have hdinkWordCast :
      EVM.wordOfInt (-((endSkimWadWord σLoc I vatOut urnOut).toNat : Int)) =
        endSkimGrabDinkWord σLoc I vatOut urnOut := by
    simpa using hdinkWord
  have hdartWord :
      EVM.wordOfInt (-(Int.ofNat (endFreeUrnArtWord urnOut).toNat)) =
        endSkimGrabDartWord urnOut :=
    endFreeWordOfInt_neg_ofNat_toNat (endFreeUrnArtWord urnOut) hart
  have hdartWordCast :
      EVM.wordOfInt (-((endFreeUrnArtWord urnOut).toNat : Int)) =
        endSkimGrabDartWord urnOut := by
    simpa using hdartWord
  have hdinkBounds :
      -(Int.ofNat (EVM.twoPow (256 - 1))) ≤
          -(Int.ofNat (endSkimWadWord σLoc I vatOut urnOut).toNat) ∧
        -(Int.ofNat (endSkimWadWord σLoc I vatOut urnOut).toNat) <
          Int.ofNat (EVM.twoPow (256 - 1)) := by
    constructor
    · apply neg_le_neg
      exact Int.ofNat_le.mpr (by simpa [EVM.twoPow] using hwad)
    · have hnonpos :
          -(Int.ofNat (endSkimWadWord σLoc I vatOut urnOut).toNat) ≤ 0 := by
        exact neg_nonpos.mpr (Int.natCast_nonneg _)
      exact lt_of_le_of_lt hnonpos (by norm_num [EVM.twoPow])
  have hdartBounds :
      -(Int.ofNat (EVM.twoPow (256 - 1))) ≤
          -(Int.ofNat (endFreeUrnArtWord urnOut).toNat) ∧
        -(Int.ofNat (endFreeUrnArtWord urnOut).toNat) <
          Int.ofNat (EVM.twoPow (256 - 1)) := by
    constructor
    · apply neg_le_neg
      exact Int.ofNat_le.mpr (by simpa [EVM.twoPow] using hart)
    · have hnonpos : -(Int.ofNat (endFreeUrnArtWord urnOut).toNat) ≤ 0 := by
        exact neg_nonpos.mpr (Int.natCast_nonneg _)
      exact lt_of_le_of_lt hnonpos (by norm_num [EVM.twoPow])
  have hdinkBoundsSimp :
      (endSkimWadWord σLoc I vatOut urnOut).toNat ≤ EVM.twoPow 255 ∧
        -(Int.ofNat (endSkimWadWord σLoc I vatOut urnOut).toNat) <
          Int.ofNat (EVM.twoPow 255) := by
    constructor
    · simpa [EVM.twoPow] using hwad
    · simpa [EVM.twoPow] using hdinkBounds.2
  have hdartBoundsSimp :
      (endFreeUrnArtWord urnOut).toNat ≤ EVM.twoPow 255 ∧
        -(Int.ofNat (endFreeUrnArtWord urnOut).toNat) <
          Int.ofNat (EVM.twoPow 255) := by
    constructor
    · simpa [EVM.twoPow] using hart
    · simpa [EVM.twoPow] using hdartBounds.2
  have hdinkUpperCast :
      -((endSkimWadWord σLoc I vatOut urnOut).toNat : Int) < (EVM.twoPow 255 : Int) := by
    simpa using hdinkBoundsSimp.2
  have hdartUpperCast :
      -((endFreeUrnArtWord urnOut).toNat : Int) < (EVM.twoPow 255 : Int) := by
    simpa using hdartBoundsSimp.2
  have hbytesLen : (EVM.Word.toBytesBE (endSkimIlkWord I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (endSkimIlkWord I)
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, bytes32, bytes32Width, addr, int256,
    int256Int, grabSelector, selectorBytes, hbytes, hbytesLen, hurnWord, hthisWord,
    hvowWord, hdinkBoundsSimp, hdartBoundsSimp]
  rw [if_pos hdinkUpperCast, if_pos hdartUpperCast]
  simp [hdinkWordCast, hdartWordCast, word_toBytesBE_toByteArray_eq_toByteArray, zeroBytes,
    ByteArray.append_assoc]

theorem endSkim_solcErrorStringMem0_size_of_size288 {mem : ByteArray}
    (hmem : mem.size = 288) :
    (solcErrorStringMem0 mem).size = 288 := by
  unfold solcErrorStringMem0
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega)]
  simp [ByteArray.size_append, ByteArray.size_extract, hmem]

theorem endSkim_solcErrorStringMem1_size_of_size288 {mem : ByteArray}
    (hmem : mem.size = 288) :
    (solcErrorStringMem1 mem).size = 288 := by
  unfold solcErrorStringMem1
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [endSkim_solcErrorStringMem0_size_of_size288 hmem]; omega)]
  simp [ByteArray.size_append, ByteArray.size_extract,
    endSkim_solcErrorStringMem0_size_of_size288 hmem]

theorem endSkim_solcErrorStringMem2_size_of_size288 (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 288) :
    (solcErrorStringMem2 len mem).size = 288 := by
  unfold solcErrorStringMem2
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [endSkim_solcErrorStringMem1_size_of_size288 hmem]; omega)]
  simp [ByteArray.size_append, ByteArray.size_extract,
    endSkim_solcErrorStringMem1_size_of_size288 hmem]

theorem endSkim_solcErrorStringMem3_size_of_size288 (len word : UInt256)
    {mem : ByteArray} (hmem : mem.size = 288) :
    (solcErrorStringMem3 len word mem).size = 288 := by
  unfold solcErrorStringMem3
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [endSkim_solcErrorStringMem2_size_of_size288 len hmem]; omega)]
  simp [ByteArray.size_append, ByteArray.size_extract,
    endSkim_solcErrorStringMem2_size_of_size288 len hmem]

theorem endSkim_solcErrorStringMem3_read64_of_size288 (len word : UInt256)
    {mem : ByteArray} (hmem : mem.size = 288)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem3
  rw [toByteArray_write_read_below_of_gap word _ 196 64
      (by rw [endSkim_solcErrorStringMem2_size_of_size288 len hmem]; omega) (by omega)
      (by
        rw [endSkim_solcErrorStringMem2_size_of_size288 len hmem]
        exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem2
  rw [toByteArray_write_read_below_of_gap len _ 164 64
      (by rw [endSkim_solcErrorStringMem1_size_of_size288 hmem]; omega) (by omega)
      (by
        rw [endSkim_solcErrorStringMem1_size_of_size288 hmem]
        exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [endSkim_solcErrorStringMem0_size_of_size288 hmem]; omega) (by omega)
      (by
        rw [endSkim_solcErrorStringMem0_size_of_size288 hmem]
        exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 64
      (by rw [hmem]; omega) (by omega) (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread64

theorem endSkim_solcErrorStringMem3_mload64_of_size288 (len word : UInt256)
    {mem : ByteArray} (hmem : mem.size = 288)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcErrorStringMem3 len word mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcErrorStringMem3 len word mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [endSkim_solcErrorStringMem3_size_of_size288 len word hmem]; decide)
    (by decide) (endSkim_solcErrorStringMem3_read64_of_size288 len word hmem hread64)

set_option maxHeartbeats 1000000 in
theorem endSkim_solcErrorStringRevertTail_aw9 {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {pc len rawWord shift word : UInt256}
    {op : Operation.POp} {width : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc stk mem (UInt256.ofNat 9) rdata acc k C)
    (hwf : solcErrorStringRevertTailWf code pc len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmem : mem.size = 288)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hdRawOut, hdShl, hd68,
      hdDup3, hdAdd, hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3,
      hdSub, hd100, hdAdd2, hdSwap4, hdRev⟩
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw dup1 hd2 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) hd3
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 9)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 0 (solcErrorStringMem1 mem) (UInt256.ofNat 9)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 0 (solcErrorStringMem2 len mem)
      (UInt256.ofNat 9) hd26 mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst rawWord (width := width) (op := op)
    hpush hd27 (by simp only [List.length_cons]; omega)
  have rdWord := evm_run rdRaw with [
    raw push1 shift hdRawOut (by evm_ov),
    raw shl hdShl (by evm_ov)]
  rw [hword] at rdWord
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ hd68 (by evm_ov),
    raw dup3 hdDup3 (by evm_ov),
    raw add hdAdd (by evm_ov),
    raw mstore 0 (solcErrorStringMem3 len word mem)
      (UInt256.ofNat 9) hdMstore3 mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) hdMload
      mem_cost
      (endSkim_solcErrorStringMem3_mload64_of_size288 len word hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

theorem endSkimX_gapStoreAtHash {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {vatOut urnOut rdata : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hloVat : 160 ≤ vatOut.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7150⟩
      (endSkimGapNewWord σ' I vatOut urnOut :: endSkimWadWord σ' I vatOut urnOut ::
        endSkimOweWord σ' I vatOut urnOut :: endFreeUrnArtWord urnOut ::
        endFreeUrnInkWord urnOut :: endFlowVatIlkRateWord vatOut :: endSkimUrnKey I ::
        endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      (endSkimGapHashMem I vatOut urnOut) (UInt256.ofNat 9) rdata (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7166⟩
      (endSkimWadWord σ' I vatOut urnOut :: endSkimOweWord σ' I vatOut urnOut ::
        endFreeUrnArtWord urnOut :: endFreeUrnInkWord urnOut ::
        endFlowVatIlkRateWord vatOut :: endSkimUrnKey I :: endSkimIlkWord I ::
        endSkimReturnPc :: sel :: [])
      (endSkimGapStoreHashMem I vatOut urnOut) (UInt256.ofNat 9) rdata
      (cA', endSkimPostGapAccountMap σ' I (endSkimGapNewWord σ' I vatOut urnOut))
      k' C' := by
  let key := endSkimIlkWord I
  let mem0 := endSkimUrnsPostCallMem I vatOut urnOut
  let mem12 := endSkimTagHashMem I vatOut urnOut
  let mem13 := endSkimGapHashMem I vatOut urnOut
  let memStore := endSkimGapStoreHashMem I vatOut urnOut
  have hslot : endSkimGapSlot I = solcMappingSlot ⟨13⟩ key := by
    simpa [key] using endSkimGapSlot_eq (I := I) hsz68
  have hpostSize : mem0.size = 288 := by
    simpa [mem0] using endSkimUrnsPostCallMem_size I vatOut urnOut hloVat
  have hmem12Size : mem12.size = mem0.size := by
    exact endFlow_twoWordHashMem_size_of_ge64 key ⟨12⟩
      (by rw [hpostSize]; omega)
  have hmem13Size : mem13.size = mem12.size := by
    exact endFlow_twoWordHashMem_size_of_ge64 key ⟨13⟩
      (by rw [hmem12Size, hpostSize]; omega)
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (memStore.readWithPadding 0 64))) =
        solcMappingSlot ⟨13⟩ key := by
    simpa [memStore, endSkimGapStoreHashMem, key, mem13] using
      endFlow_twoWordHashMem_solcMappingSlot_of_ge64 (mem := mem13) ⟨13⟩ key
        (by rw [hmem13Size, hmem12Size, hpostSize]; omega)
  have rd7154 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup9 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd7155 := rd7154.mstore 0 (wordAt0Mem key mem13)
    (UInt256.ofNat 9) (by native_decide) mem_cost
    (by simp [wordAt0Mem, key, mem13]) (by native_decide) (by evm_ov)
  have rd7160pre := evm_run rd7155 with [
    raw push1 ⟨13⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd7160 := rd7160pre.mstore 0 memStore (UInt256.ofNat 9)
    (by native_decide) mem_cost
    (by
      change (⟨13⟩ : UInt256).toByteArray.write 0 (wordAt0Mem key mem13) 32 32 =
        memStore
      simp [memStore, endSkimGapStoreHashMem, twoWordHashMem, wordAt32Mem, key, mem13])
    (by native_decide) (by evm_ov)
  have rd7164 := evm_run rd7160 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd7165 := rd7164.keccak256 0 (endSkimGapSlot I) (UInt256.ofNat 9)
    (by native_decide) mem_cost
    (by simpa [memStore, key, hslot] using hhash) (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd7166raw⟩ := rd7165.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [endSkimPostGapAccountMap, memStore] using rd7166raw⟩

theorem endSkimX_gapStoreIntGuardOk {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {vatOut urnOut rdata : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hloVat : 160 ≤ vatOut.size)
    (hwadLimit : (endSkimWadWord σ' I vatOut urnOut).toNat ≤ 2 ^ 255)
    (hartLimit : (endFreeUrnArtWord urnOut).toNat ≤ 2 ^ 255)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7150⟩
      (endSkimGapNewWord σ' I vatOut urnOut :: endSkimWadWord σ' I vatOut urnOut ::
        endSkimOweWord σ' I vatOut urnOut :: endFreeUrnArtWord urnOut ::
        endFreeUrnInkWord urnOut :: endFlowVatIlkRateWord vatOut :: endSkimUrnKey I ::
        endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      (endSkimGapHashMem I vatOut urnOut) (UInt256.ofNat 9) rdata (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7253⟩
      (endSkimWadWord σ' I vatOut urnOut :: endSkimOweWord σ' I vatOut urnOut ::
        endFreeUrnArtWord urnOut :: endFreeUrnInkWord urnOut ::
        endFlowVatIlkRateWord vatOut :: endSkimUrnKey I :: endSkimIlkWord I ::
        endSkimReturnPc :: sel :: [])
      (endSkimGapStoreHashMem I vatOut urnOut) (UInt256.ofNat 9) rdata
      (cA', endSkimPostGapAccountMap σ' I (endSkimGapNewWord σ' I vatOut urnOut))
      k' C' := by
  let key := endSkimIlkWord I
  let mem0 := endSkimUrnsPostCallMem I vatOut urnOut
  let mem12 := endSkimTagHashMem I vatOut urnOut
  let mem13 := endSkimGapHashMem I vatOut urnOut
  let memStore := endSkimGapStoreHashMem I vatOut urnOut
  have hslot : endSkimGapSlot I = solcMappingSlot ⟨13⟩ key := by
    simpa [key] using endSkimGapSlot_eq (I := I) hsz68
  have hpostSize : mem0.size = 288 := by
    simpa [mem0] using endSkimUrnsPostCallMem_size I vatOut urnOut hloVat
  have hmem12Size : mem12.size = mem0.size := by
    exact endFlow_twoWordHashMem_size_of_ge64 key ⟨12⟩
      (by rw [hpostSize]; omega)
  have hmem13Size : mem13.size = mem12.size := by
    exact endFlow_twoWordHashMem_size_of_ge64 key ⟨13⟩
      (by rw [hmem12Size, hpostSize]; omega)
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (memStore.readWithPadding 0 64))) =
        solcMappingSlot ⟨13⟩ key := by
    simpa [memStore, endSkimGapStoreHashMem, key, mem13] using
      endFlow_twoWordHashMem_solcMappingSlot_of_ge64 (mem := mem13) ⟨13⟩ key
        (by rw [hmem13Size, hmem12Size, hpostSize]; omega)
  have rd7154 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup9 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd7155 := rd7154.mstore 0 (wordAt0Mem key mem13)
    (UInt256.ofNat 9) (by native_decide) mem_cost
    (by simp [wordAt0Mem, key, mem13]) (by native_decide) (by evm_ov)
  have rd7160pre := evm_run rd7155 with [
    raw push1 ⟨13⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd7160 := rd7160pre.mstore 0 memStore (UInt256.ofNat 9)
    (by native_decide) mem_cost
    (by
      change (⟨13⟩ : UInt256).toByteArray.write 0 (wordAt0Mem key mem13) 32 32 =
        memStore
      simp [memStore, endSkimGapStoreHashMem, twoWordHashMem, wordAt32Mem, key, mem13])
    (by native_decide) (by evm_ov)
  have rd7164 := evm_run rd7160 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd7165 := rd7164.keccak256 0 (endSkimGapSlot I) (UInt256.ofNat 9)
    (by native_decide) mem_cost
    (by simpa [memStore, key, hslot] using hhash) (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd7166raw⟩ := rd7165.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd7166⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7166⟩
        (endSkimWadWord σ' I vatOut urnOut ::
          endSkimOweWord σ' I vatOut urnOut :: endFreeUrnArtWord urnOut ::
          endFreeUrnInkWord urnOut :: endFlowVatIlkRateWord vatOut ::
          endSkimUrnKey I :: endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
        memStore (UInt256.ofNat 9) rdata
        (cA', endSkimPostGapAccountMap σ' I (endSkimGapNewWord σ' I vatOut urnOut))
        k' C' := by
    exact ⟨_, _, by simpa [endSkimPostGapAccountMap, memStore] using rd7166raw⟩
  have hlimit : endFreeInt256LimitWord.toNat = 2 ^ 255 := by native_decide
  have hgtWad :
      UInt256.gt (endSkimWadWord σ' I vatOut urnOut) endFreeInt256LimitWord = ⟨0⟩ := by
    apply ugt_zero
    rw [hlimit]
    exact hwadLimit
  have hgtArt : UInt256.gt (endFreeUrnArtWord urnOut) endFreeInt256LimitWord = ⟨0⟩ := by
    apply ugt_zero
    rw [hlimit]
    exact hartLimit
  have rd7179pre := evm_run rd7166 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨255⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨7189⟩ (by native_decide) (by evm_ov)]
  rw [hgtWad, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd7179pre
  have rd7180 := rd7179pre.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd7188 := evm_run rd7180 with [
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨255⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  rw [hgtArt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd7188
  have rd7253 := evm_run rd7188 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨7253⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by simpa [memStore, endFreeInt256LimitWord] using rd7253⟩

theorem endSkimX_gapStoreIntGuardWadOverflow {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {vatOut urnOut rdata : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hloVat : 160 ≤ vatOut.size)
    (hwad : 2 ^ 255 < (endSkimWadWord σ' I vatOut urnOut).toNat)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7150⟩
      (endSkimGapNewWord σ' I vatOut urnOut :: endSkimWadWord σ' I vatOut urnOut ::
        endSkimOweWord σ' I vatOut urnOut :: endFreeUrnArtWord urnOut ::
        endFreeUrnInkWord urnOut :: endFlowVatIlkRateWord vatOut :: endSkimUrnKey I ::
        endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      (endSkimGapHashMem I vatOut urnOut) (UInt256.ofNat 9) rdata (cA', σ') k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd7166⟩ := endSkimX_gapStoreAtHash hperm hsz68 hloVat h
  have hlimit : endFreeInt256LimitWord.toNat = 2 ^ 255 := by native_decide
  have hgtWad :
      UInt256.gt (endSkimWadWord σ' I vatOut urnOut) endFreeInt256LimitWord = ⟨1⟩ := by
    apply ugt_one
    rw [hlimit]
    exact hwad
  have rd7179pre := evm_run rd7166 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨255⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨7189⟩ (by native_decide) (by evm_ov)]
  rw [hgtWad, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd7179pre
  have rd7189 := rd7179pre.jumpiT (by native_decide)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest) (by evm_ov)
  have rd7194 := evm_run rd7189 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨7253⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
      (by evm_ov)]
  exact endSkim_solcErrorStringRevertTail_aw9
    (pc := ⟨7194⟩) (len := ⟨12⟩)
    (rawWord := ⟨0x456e642f6f766572666c6f77⟩) (shift := ⟨160⟩)
    (word := UInt256.shiftLeft ⟨0x456e642f6f766572666c6f77⟩ ⟨160⟩)
    (op := .PUSH12) (width := 12)
    rd7194
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide) rfl
    (endSkimGapStoreHashMem_size I vatOut urnOut hloVat)
    (endSkimGapStoreHashMem_read64 I vatOut urnOut hloVat)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkimX_gapStoreIntGuardArtOverflow {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {vatOut urnOut rdata : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hloVat : 160 ≤ vatOut.size)
    (hwadLimit : (endSkimWadWord σ' I vatOut urnOut).toNat ≤ 2 ^ 255)
    (hart : 2 ^ 255 < (endFreeUrnArtWord urnOut).toNat)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7150⟩
      (endSkimGapNewWord σ' I vatOut urnOut :: endSkimWadWord σ' I vatOut urnOut ::
        endSkimOweWord σ' I vatOut urnOut :: endFreeUrnArtWord urnOut ::
        endFreeUrnInkWord urnOut :: endFlowVatIlkRateWord vatOut :: endSkimUrnKey I ::
        endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      (endSkimGapHashMem I vatOut urnOut) (UInt256.ofNat 9) rdata (cA', σ') k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd7166⟩ := endSkimX_gapStoreAtHash hperm hsz68 hloVat h
  have hlimit : endFreeInt256LimitWord.toNat = 2 ^ 255 := by native_decide
  have hgtWad :
      UInt256.gt (endSkimWadWord σ' I vatOut urnOut) endFreeInt256LimitWord = ⟨0⟩ := by
    apply ugt_zero
    rw [hlimit]
    exact hwadLimit
  have hgtArt : UInt256.gt (endFreeUrnArtWord urnOut) endFreeInt256LimitWord = ⟨1⟩ := by
    apply ugt_one
    rw [hlimit]
    exact hart
  have rd7179pre := evm_run rd7166 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨255⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨7189⟩ (by native_decide) (by evm_ov)]
  rw [hgtWad, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd7179pre
  have rd7180 := rd7179pre.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd7188 := evm_run rd7180 with [
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨255⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  rw [hgtArt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd7188
  have rd7194 := evm_run rd7188 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨7253⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
      (by evm_ov)]
  exact endSkim_solcErrorStringRevertTail_aw9
    (pc := ⟨7194⟩) (len := ⟨12⟩)
    (rawWord := ⟨0x456e642f6f766572666c6f77⟩) (shift := ⟨160⟩)
    (word := UInt256.shiftLeft ⟨0x456e642f6f766572666c6f77⟩ ⟨160⟩)
    (op := .PUSH12) (width := 12)
    rd7194
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide) rfl
    (endSkimGapStoreHashMem_size I vatOut urnOut hloVat)
    (endSkimGapStoreHashMem_read64 I vatOut urnOut hloVat)
    (by simp only [List.length_cons, List.length_nil]; omega)

end Benchmarks.Dss.End

namespace Reasoning.Theory

theorem dup12_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk ll : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP12, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
    (hov : t.length + 13 ≤ 1024) :
    Xstep (D_J code 0) s =
      (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
       else .ok
        (stSwap s
          (ll :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t),
          .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP12, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_dup12 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t).length -
          12 + 13 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

end Reasoning.Theory

namespace Reasoning.Reach

theorem RD.dup12 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP12, .none)) (hov : t.length + 13 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (ll :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => Reasoning.Theory.dup12_xstep hc hp hdec hs hov)

end Reasoning.Reach

namespace Benchmarks.Dss.End

theorem endSkimX_grabExtcodesizeGuard {cA cA' gh bl σ σCall σLoc σ₀ A I}
    {g : Sat256} {sel : UInt256} {vatOut urnOut rdata : ByteArray} {k C : ℕ}
    (hloVat : 160 ≤ vatOut.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7253⟩
      (endSkimWadWord σLoc I vatOut urnOut :: endSkimOweWord σLoc I vatOut urnOut ::
        endFreeUrnArtWord urnOut :: endFreeUrnInkWord urnOut ::
        endFlowVatIlkRateWord vatOut :: endSkimUrnKey I :: endSkimIlkWord I ::
        endSkimReturnPc :: sel :: [])
      (endSkimGapStoreHashMem I vatOut urnOut) (UInt256.ofNat 9) rdata
      (cA', σCall) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7357⟩
      (endPackVatWord σCall I :: endPackVatWord σCall I :: ⟨0⟩ ::
        endFreeGrabOutPtr :: endFreeGrabInSize :: endFreeGrabOutPtr ::
        endFreeGrabOutSize :: endFreeGrabEndPtr :: endFreeGrabSelectorWord ::
        endPackVatWord σCall I ::
        endSkimWadWord σLoc I vatOut urnOut :: endSkimOweWord σLoc I vatOut urnOut ::
        endFreeUrnArtWord urnOut :: endFreeUrnInkWord urnOut ::
        endFlowVatIlkRateWord vatOut :: endSkimUrnKey I :: endSkimIlkWord I ::
        endSkimReturnPc :: sel :: [])
      (endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut) (UInt256.ofNat 11)
      rdata (cA', σCall) k' C' := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (endSkimGapStoreHashMem I vatOut urnOut).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endSkimGapStoreHashMem I vatOut urnOut).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [endSkimGapStoreHashMem_size I vatOut urnOut hloVat]; decide)
      (by decide) (endSkimGapStoreHashMem_read64 I vatOut urnOut hloVat)
  have hmload64Grab :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endSkimGrabMem7For σCall σLoc I vatOut urnOut).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 11 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endSkimGrabMem7For σCall σLoc I vatOut urnOut).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    simpa [endSkimGrabMem7For_eq] using
      (mloadFreePtrValue
        (by rw [endSkimGrabCalldataMemFor_size σCall σLoc I vatOut urnOut hloVat]; decide)
        (by decide) (endSkimGrabCalldataMemFor_read64 σCall σLoc I vatOut urnOut hloVat))
  have hselectorShift :
      UInt256.shiftLeft (⟨0x01eeacfd⟩ : UInt256) ⟨230⟩ =
        endFreeGrabSelectorShifted := by
    native_decide
  have hthisWord : EVM.word ↑I.codeOwner = endSkimThisWord I := by
    exact endSkimThisWordOfAddr I
  have hurnMask :
      UInt256.land (endSkimUrnKey I) solcAddrMask = endSkimUrnKey I := by
    have hcanon : (endSkimUrnKey I).toNat < EVM.addressModulus := by
      rw [endSkimUrnKey, u256_land_comm solcAddrMask (endSkimUrnWord I)]
      exact solcAddrMask_result_canonical (endSkimUrnWord I)
    exact solcAddrMask_clean hcanon
  have hurnMaskLeft :
      UInt256.land solcAddrMask (endSkimUrnKey I) = endSkimUrnKey I := by
    have hcanon : (endSkimUrnKey I).toNat < EVM.addressModulus := by
      rw [endSkimUrnKey, u256_land_comm solcAddrMask (endSkimUrnWord I)]
      exact solcAddrMask_result_canonical (endSkimUrnWord I)
    exact solcAddrMask_clean_left hcanon
  have hvowMask :
      UInt256.land (endSlotWord ⟨4⟩ σCall I) solcAddrMask = endPackVowWord σCall I := by
    rfl
  have hvowMaskLeft :
      UInt256.land solcAddrMask (endSlotWord ⟨4⟩ σCall I) = endPackVowWord σCall I := by
    simpa [endPackVowWord] using
      u256_land_comm solcAddrMask (endSlotWord ⟨4⟩ σCall I)
  have hvatMask :
      UInt256.land (endSlotWord ⟨1⟩ σCall I) solcAddrMask = endPackVatWord σCall I := by
    rfl
  have hvatMaskLeft :
      UInt256.land solcAddrMask (endSlotWord ⟨1⟩ σCall I) = endPackVatWord σCall I := by
    simpa [endPackVatWord] using
      u256_land_comm solcAddrMask (endSlotWord ⟨1⟩ σCall I)
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hdink :
      UInt256.sub ⟨0⟩ (endSkimWadWord σLoc I vatOut urnOut) =
        endSkimGrabDinkWord σLoc I vatOut urnOut := by
    rfl
  have hdart :
      UInt256.sub ⟨0⟩ (endFreeUrnArtWord urnOut) =
        endSkimGrabDartWord urnOut := by
    rfl
  have rd7257 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd7257raw⟩ := rd7257.sload (by native_decide) (by evm_ov)
  have rd7257 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7257⟩
        (endSlotWord ⟨1⟩ σCall I :: endSkimWadWord σLoc I vatOut urnOut ::
          endSkimOweWord σLoc I vatOut urnOut :: endFreeUrnArtWord urnOut ::
          endFreeUrnInkWord urnOut :: endFlowVatIlkRateWord vatOut :: endSkimUrnKey I ::
          endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
        (endSkimGapStoreHashMem I vatOut urnOut) (UInt256.ofNat 9) rdata
        (cA', σCall) k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd7257raw⟩
  obtain ⟨_, _, rd7257⟩ := rd7257
  have rd7261 := evm_run rd7257 with [
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd7261raw⟩ := rd7261.sload (by native_decide) (by evm_ov)
  have rd7261 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7261⟩
        (endSlotWord ⟨4⟩ σCall I :: ⟨4⟩ :: endSlotWord ⟨1⟩ σCall I ::
          endSkimWadWord σLoc I vatOut urnOut ::
          endSkimOweWord σLoc I vatOut urnOut :: endFreeUrnArtWord urnOut ::
          endFreeUrnInkWord urnOut :: endFlowVatIlkRateWord vatOut :: endSkimUrnKey I ::
          endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
        (endSkimGapStoreHashMem I vatOut urnOut) (UInt256.ofNat 9) rdata
        (cA', σCall) k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd7261raw⟩
  obtain ⟨_, _, rd7261⟩ := rd7261
  have rd7357raw := evm_run rd7261 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw push4 ⟨0x01eeacfd⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨230⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (endSkimGrabMem1 I vatOut urnOut) (UInt256.ofNat 9)
      (by native_decide) mem_cost
      (by rw [hselectorShift]; rfl) (by decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup12 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 0 (endSkimGrabMem2 I vatOut urnOut) (UInt256.ofNat 9)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup11 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 0 (endSkimGrabMem3 I vatOut urnOut) (UInt256.ofNat 9)
      (by native_decide) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨36⟩).toNat = 164 by native_decide]
        rw [haddrMask, hurnMaskLeft]
        rfl)
      (by decide) (by evm_ov),
    raw address (by native_decide) (by evm_ov),
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 0 (endSkimGrabMem4 I vatOut urnOut) (UInt256.ofNat 9)
      (by native_decide) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨68⟩).toNat = 196 by native_decide]
        simp [endSkimGrabMem4, Reasoning.Theory.writeWord, endSkimThisWord])
      (by decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 0 (endSkimGrabMem5For σCall I vatOut urnOut) (UInt256.ofNat 9)
      (by native_decide) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨100⟩).toNat = 228 by native_decide]
        rw [haddrMask, hvowMaskLeft]
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨132⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (endSkimGrabMem6For σCall σLoc I vatOut urnOut) (UInt256.ofNat 10)
      (by native_decide) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨132⟩).toNat = 260 by native_decide]
        rw [hdink]
        rfl)
      (by decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨164⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (endSkimGrabMem7For σCall σLoc I vatOut urnOut) (UInt256.ofNat 11)
      (by native_decide) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨164⟩).toNat = 292 by native_decide]
        rw [hdart]
        rfl)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 11) (by native_decide)
      mem_cost hmload64Grab (by decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push4 ⟨0x7bab3f40⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨196⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  have rd7357 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7357⟩
        (endPackVatWord σCall I :: endPackVatWord σCall I :: ⟨0⟩ ::
          endFreeGrabOutPtr :: endFreeGrabInSize :: endFreeGrabOutPtr ::
          endFreeGrabOutSize :: endFreeGrabEndPtr :: endFreeGrabSelectorWord ::
          endPackVatWord σCall I ::
          endSkimWadWord σLoc I vatOut urnOut ::
          endSkimOweWord σLoc I vatOut urnOut :: endFreeUrnArtWord urnOut ::
          endFreeUrnInkWord urnOut :: endFlowVatIlkRateWord vatOut :: endSkimUrnKey I ::
          endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
        (endSkimGrabMem7For σCall σLoc I vatOut urnOut) (UInt256.ofNat 11)
        rdata (cA', σCall) k' C' := by
    exact ⟨_, _, by
      simpa [endFreeGrabOutPtr, endFreeGrabInSize, endFreeGrabOutSize,
        endFreeGrabEndPtr, endFreeGrabSelectorWord, endPackVatWord, endPackVowWord,
        endSlotWord, solcSlotWord, solcAddrMask, hvatMask, hvatMaskLeft, hvowMask,
        hvowMaskLeft, hurnMask, hurnMaskLeft, haddrMask, hthisWord] using rd7357raw⟩
  obtain ⟨k', C', rd7357⟩ := rd7357
  exact ⟨k', C', by simpa [endSkimGrabMem7For_eq] using rd7357⟩

theorem endSkimX_grabNoCode {cA cA' gh bl σ σCall σLoc σ₀ A I}
    {g : Sat256} {sel : UInt256} {vatOut urnOut rdata : ByteArray} {k C : ℕ}
    (hloVat : 160 ≤ vatOut.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7253⟩
      (endSkimWadWord σLoc I vatOut urnOut :: endSkimOweWord σLoc I vatOut urnOut ::
        endFreeUrnArtWord urnOut :: endFreeUrnInkWord urnOut ::
        endFlowVatIlkRateWord vatOut :: endSkimUrnKey I :: endSkimIlkWord I ::
        endSkimReturnPc :: sel :: [])
      (endSkimGapStoreHashMem I vatOut urnOut) (UInt256.ofNat 9) rdata
      (cA', σCall) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σCall (endPackVatWord σCall I) = ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd7357⟩ := endSkimX_grabExtcodesizeGuard hloVat h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨7357⟩) (okPc := ⟨7369⟩) rd7357
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkimX_grabCallReady {cA cA' gh bl σ σCall σLoc σ₀ A I}
    {g : Sat256} {sel : UInt256} {vatOut urnOut rdata : ByteArray} {k C : ℕ}
    (hloVat : 160 ≤ vatOut.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7253⟩
      (endSkimWadWord σLoc I vatOut urnOut :: endSkimOweWord σLoc I vatOut urnOut ::
        endFreeUrnArtWord urnOut :: endFreeUrnInkWord urnOut ::
        endFlowVatIlkRateWord vatOut :: endSkimUrnKey I :: endSkimIlkWord I ::
        endSkimReturnPc :: sel :: [])
      (endSkimGapStoreHashMem I vatOut urnOut) (UInt256.ofNat 9) rdata
      (cA', σCall) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σCall (endPackVatWord σCall I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7372⟩
      (gasWord :: endPackVatWord σCall I :: ⟨0⟩ :: endFreeGrabOutPtr ::
        endFreeGrabInSize :: endFreeGrabOutPtr :: endFreeGrabOutSize ::
        endFreeGrabEndPtr :: endFreeGrabSelectorWord :: endPackVatWord σCall I ::
        endSkimWadWord σLoc I vatOut urnOut :: endSkimOweWord σLoc I vatOut urnOut ::
        endFreeUrnArtWord urnOut :: endFreeUrnInkWord urnOut ::
        endFlowVatIlkRateWord vatOut :: endSkimUrnKey I :: endSkimIlkWord I ::
        endSkimReturnPc :: sel :: [])
      (endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut) (UInt256.ofNat 11)
      rdata (cA', σCall) k' C' := by
  obtain ⟨_, _, rd7357⟩ := endSkimX_grabExtcodesizeGuard hloVat h
  obtain ⟨gasWord, k', C', rd7372⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨7357⟩) (okPc := ⟨7369⟩) rd7357
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd7372⟩

theorem endSkimX_grabPostCall {cA cA' gh bl σ σCall σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {vatOut urnOut : ByteArray} {k C : ℕ}
    {σLoc : AccountMap}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7372⟩
      (gasWord :: endPackVatWord σCall I :: ⟨0⟩ :: endFreeGrabOutPtr ::
        endFreeGrabInSize :: endFreeGrabOutPtr :: endFreeGrabOutSize ::
        endFreeGrabEndPtr :: endFreeGrabSelectorWord :: endPackVatWord σCall I ::
        endSkimWadWord σLoc I vatOut urnOut :: endSkimOweWord σLoc I vatOut urnOut ::
        endFreeUrnArtWord urnOut :: endFreeUrnInkWord urnOut ::
        endFlowVatIlkRateWord vatOut :: endSkimUrnKey I :: endSkimIlkWord I ::
        endSkimReturnPc :: sel :: [])
      (endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut) (UInt256.ofNat 11)
      urnOut (cA', σCall) k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap)
      (z : Bool) (ret : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA'', σ'', g'', A', z, ret) = Ethereum.EVM.Θ I.blobVersionedHashes cA' gh bl σCall σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (endPackVatWord σCall I))
          (toExecute σCall (AccountAddress.ofUInt256 (endPackVatWord σCall I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut).readWithPadding
            endFreeGrabOutPtr.toNat endFreeGrabInSize.toNat)
          (I.depth + 1) I.header I.perm)
      ∧ RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7373⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endFreeGrabEndPtr :: endFreeGrabSelectorWord ::
            endPackVatWord σCall I :: endSkimWadWord σLoc I vatOut urnOut ::
            endSkimOweWord σLoc I vatOut urnOut :: endFreeUrnArtWord urnOut ::
            endFreeUrnInkWord urnOut :: endFlowVatIlkRateWord vatOut :: endSkimUrnKey I ::
            endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
          (endSkimGrabPostCallMemFor σCall σLoc I vatOut urnOut ret)
          (UInt256.ofNat 11) ret (cA'', σ'') k' C'
      ∧ ret.size < UInt256.size := by
  obtain ⟨cA'', σ'', z, ret, Ain, callGas, k', C', hΘ, rd7373raw, hret⟩ :=
    RD.call h (by native_decide) hdepth (by evm_ov)
  refine ⟨cA'', σ'', z, ret, Ain, callGas, k', C', ?_, ?_, hret⟩
  · simpa [initState] using hΘ
  · have hmin : (min endFreeGrabOutSize (UInt256.ofNat ret.size)).toNat = 0 := by
      have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat ret.size := by
        show (0 : Nat) ≤ (UInt256.ofNat ret.size).toNat
        exact Nat.zero_le _
      simp [endFreeGrabOutSize, min, hle]
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 11).toNat
          endFreeGrabOutPtr.toNat endFreeGrabInSize.toNat)
          endFreeGrabOutPtr.toNat endFreeGrabOutSize.toNat) = UInt256.ofNat 11 := by
      unfold endFreeGrabOutPtr endFreeGrabInSize endFreeGrabOutSize
      native_decide
    simpa [endSkimGrabPostCallMemFor, endFreeGrabOutPtr, endFreeGrabInSize,
      endFreeGrabOutSize, endFreeGrabEndPtr, hmin, byteArray_write_len_zero, haw]
      using rd7373raw

theorem endSkimX_grabCallDepthLimit {cA cA' gh bl σ σCall σLoc σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {vatOut urnOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7372⟩
      (gasWord :: endPackVatWord σCall I :: ⟨0⟩ :: endFreeGrabOutPtr ::
        endFreeGrabInSize :: endFreeGrabOutPtr :: endFreeGrabOutSize ::
        endFreeGrabEndPtr :: endFreeGrabSelectorWord :: endPackVatWord σCall I ::
        endSkimWadWord σLoc I vatOut urnOut :: endSkimOweWord σLoc I vatOut urnOut ::
        endFreeUrnArtWord urnOut :: endFreeUrnInkWord urnOut ::
        endFlowVatIlkRateWord vatOut :: endSkimUrnKey I :: endSkimIlkWord I ::
        endSkimReturnPc :: sel :: [])
      (endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut) (UInt256.ofNat 11)
      urnOut (cA', σCall) k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7373⟩
      (⟨0⟩ :: endFreeGrabEndPtr :: endFreeGrabSelectorWord ::
        endPackVatWord σCall I :: endSkimWadWord σLoc I vatOut urnOut ::
        endSkimOweWord σLoc I vatOut urnOut :: endFreeUrnArtWord urnOut ::
        endFreeUrnInkWord urnOut :: endFlowVatIlkRateWord vatOut :: endSkimUrnKey I ::
        endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
      (endSkimGrabCalldataMemFor σCall σLoc I vatOut urnOut) (UInt256.ofNat 11)
      ByteArray.empty (cA', σCall) k' C' := by
  obtain ⟨k', C', rd7373raw⟩ :=
    RD.callDepthLimit h (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min endFreeGrabOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 11).toNat
        endFreeGrabOutPtr.toNat endFreeGrabInSize.toNat)
        endFreeGrabOutPtr.toNat endFreeGrabOutSize.toNat) = UInt256.ofNat 11 := by
    unfold endFreeGrabOutPtr endFreeGrabInSize endFreeGrabOutSize
    native_decide
  simpa [endFreeGrabOutPtr, endFreeGrabInSize, endFreeGrabOutSize,
    endFreeGrabEndPtr, hmin, byteArray_write_len_zero, haw] using rd7373raw

theorem endSkimX_grabCallFailed {cA cA' gh bl σ σpre σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {vatOut urnOut mem rdata : ByteArray} {k C : ℕ}
    {σLoc : AccountMap}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7373⟩
      (⟨0⟩ :: endFreeGrabEndPtr :: endFreeGrabSelectorWord :: endPackVatWord σpre I ::
        endSkimWadWord σLoc I vatOut urnOut :: endSkimOweWord σLoc I vatOut urnOut ::
        endFreeUrnArtWord urnOut :: endFreeUrnInkWord urnOut ::
        endFlowVatIlkRateWord vatOut :: endSkimUrnKey I :: endSkimIlkWord I ::
        endSkimReturnPc :: sel :: [])
      mem (UInt256.ofNat 11) rdata (cA', σpost) k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨7373⟩) (okPc := ⟨7389⟩) h
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkimX_grabCallSucceeded {cA cA' gh bl σ σpre σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {vatOut urnOut mem rdata : ByteArray} {k C : ℕ}
    {σLoc : AccountMap}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7373⟩
      (⟨1⟩ :: endFreeGrabEndPtr :: endFreeGrabSelectorWord :: endPackVatWord σpre I ::
        endSkimWadWord σLoc I vatOut urnOut :: endSkimOweWord σLoc I vatOut urnOut ::
        endFreeUrnArtWord urnOut :: endFreeUrnInkWord urnOut ::
        endFlowVatIlkRateWord vatOut :: endSkimUrnKey I :: endSkimIlkWord I ::
        endSkimReturnPc :: sel :: [])
      mem (UInt256.ofNat 11) rdata (cA', σpost) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7391⟩
      (endFreeGrabEndPtr :: endFreeGrabSelectorWord :: endPackVatWord σpre I ::
        endSkimWadWord σLoc I vatOut urnOut :: endSkimOweWord σLoc I vatOut urnOut ::
        endFreeUrnArtWord urnOut :: endFreeUrnInkWord urnOut ::
        endFlowVatIlkRateWord vatOut :: endSkimUrnKey I :: endSkimIlkWord I ::
        endSkimReturnPc :: sel :: [])
      mem (UInt256.ofNat 11) rdata (cA', σpost) k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨7373⟩) (okPc := ⟨7389⟩) h
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simp)

theorem endSkimX_grabLogReturn {I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} {σCall σLoc : AccountMap} {vatOut urnOut ret : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true) (hloVat : 160 ≤ vatOut.size)
    (h : RD endBytecode I g s0 ⟨7391⟩
      (endFreeGrabEndPtr :: endFreeGrabSelectorWord :: endPackVatWord σCall I ::
        endSkimWadWord σLoc I vatOut urnOut :: endSkimOweWord σLoc I vatOut urnOut ::
        endFreeUrnArtWord urnOut :: endFreeUrnInkWord urnOut ::
        endFlowVatIlkRateWord vatOut :: endSkimUrnKey I :: endSkimIlkWord I ::
        endSkimReturnPc :: sel :: [])
      (endSkimGrabPostCallMemFor σCall σLoc I vatOut urnOut ret) (UInt256.ofNat 11)
      ret acc k C) :
    RDret endBytecode g s0 acc ByteArray.empty := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endSkimGrabPostCallMemFor σCall σLoc I vatOut urnOut ret).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 11 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endSkimGrabPostCallMemFor σCall σLoc I vatOut urnOut ret).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    exact mloadFreePtrValue
      (by rw [endSkimGrabPostCallMemFor_size σCall σLoc I vatOut urnOut ret hloVat]; decide)
      (by decide) (endSkimGrabPostCallMemFor_read64 σCall σLoc I vatOut urnOut ret hloVat)
  have hmload64Log :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endSkimLogDataMem2For σCall σLoc I vatOut urnOut ret).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 11 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endSkimLogDataMem2For σCall σLoc I vatOut urnOut ret).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    exact mloadFreePtrValue
      (by rw [endSkimLogDataMem2For_size σCall σLoc I vatOut urnOut ret hloVat]; decide)
      (by decide) (endSkimLogDataMem2For_read64 σCall σLoc I vatOut urnOut ret hloVat)
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hurnMaskLeft :
      UInt256.land solcAddrMask (endSkimUrnKey I) = endSkimUrnKey I := by
    have hcanon : (endSkimUrnKey I).toNat < EVM.addressModulus := by
      rw [endSkimUrnKey, u256_land_comm solcAddrMask (endSkimUrnWord I)]
      exact solcAddrMask_result_canonical (endSkimUrnWord I)
    exact solcAddrMask_clean_left hcanon
  let skimEvent : UInt256 :=
    ⟨72531690091934883729294839565717540360935620414341866074853302191316144859993⟩
  have rd7405raw := evm_run h with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov)]
  have rd7405 : ∃ k' C', RD endBytecode I g s0 ⟨7405⟩
      (endSkimIlkWord I :: endSkimUrnKey I ::
        endSkimWadWord σLoc I vatOut urnOut :: endSkimOweWord σLoc I vatOut urnOut ::
        endFreeUrnArtWord urnOut :: endFreeUrnInkWord urnOut ::
        endFlowVatIlkRateWord vatOut :: endSkimUrnKey I :: endSkimIlkWord I ::
        endSkimReturnPc :: sel :: [])
      (endSkimGrabPostCallMemFor σCall σLoc I vatOut urnOut ret) (UInt256.ofNat 11)
      ret acc k' C' := by
    exact ⟨_, _, by simpa [haddrMask, hurnMaskLeft] using rd7405raw⟩
  obtain ⟨_, _, rd7405⟩ := rd7405
  have rdEvent := rd7405.pushConst skimEvent (width := 32) (op := .PUSH32)
    (by native_decide) (by native_decide) (by evm_ov)
  have rd7446pre := evm_run rdEvent with [
    raw dup4 (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 11) (by native_decide)
      mem_cost hmload64 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdWadMem := rd7446pre.mstore 0
    (endSkimLogDataMemFor σCall σLoc I vatOut urnOut ret) (UInt256.ofNat 11)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd7452pre := evm_run rdWadMem with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdArtMem := rd7452pre.mstore 0
    (endSkimLogDataMem2For σCall σLoc I vatOut urnOut ret) (UInt256.ofNat 11)
    (by native_decide) mem_cost
    (by
      rw [show ((⟨32⟩ : UInt256) + ⟨128⟩).toNat = 160 by native_decide]
      rfl)
    (by native_decide) (by evm_ov)
  have rd7467raw := evm_run rdArtMem with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 11) (by native_decide)
      mem_cost hmload64Log (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd7467 : ∃ k' C', RD endBytecode I g s0 ⟨7467⟩
      (⟨128⟩ :: ⟨64⟩ :: skimEvent :: endSkimIlkWord I :: endSkimUrnKey I ::
        endSkimWadWord σLoc I vatOut urnOut :: endSkimOweWord σLoc I vatOut urnOut ::
        endFreeUrnArtWord urnOut :: endFreeUrnInkWord urnOut ::
        endFlowVatIlkRateWord vatOut :: endSkimUrnKey I :: endSkimIlkWord I ::
        endSkimReturnPc :: sel :: [])
      (endSkimLogDataMem2For σCall σLoc I vatOut urnOut ret) (UInt256.ofNat 11)
      ret acc k' C' := by
    exact ⟨_, _, by
      simpa [skimEvent, haddrMask, hurnMaskLeft] using rd7467raw⟩
  obtain ⟨_, _, rd7467⟩ := rd7467
  have rdLog := RD.log3
    (a := (⟨128⟩ : UInt256)) (b := (⟨64⟩ : UInt256))
    (c := skimEvent) (d := endSkimIlkWord I) (e := endSkimUrnKey I)
    (t := [endSkimWadWord σLoc I vatOut urnOut, endSkimOweWord σLoc I vatOut urnOut,
      endFreeUrnArtWord urnOut, endFreeUrnInkWord urnOut, endFlowVatIlkRateWord vatOut,
      endSkimUrnKey I, endSkimIlkWord I, endSkimReturnPc, sel])
    0
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat 11).toNat (⟨128⟩ : UInt256).toNat
        (⟨64⟩ : UInt256).toNat))
    rd7467 (by native_decide) hperm mem_cost (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPopWad := RD.pop (a := endSkimWadWord σLoc I vatOut urnOut)
    (t := [endSkimOweWord σLoc I vatOut urnOut, endFreeUrnArtWord urnOut,
      endFreeUrnInkWord urnOut, endFlowVatIlkRateWord vatOut, endSkimUrnKey I,
      endSkimIlkWord I, endSkimReturnPc, sel])
    rdLog (by native_decide) (by evm_ov)
  have rdPopOwe := RD.pop (a := endSkimOweWord σLoc I vatOut urnOut)
    (t := [endFreeUrnArtWord urnOut, endFreeUrnInkWord urnOut,
      endFlowVatIlkRateWord vatOut, endSkimUrnKey I, endSkimIlkWord I,
      endSkimReturnPc, sel])
    rdPopWad (by native_decide) (by evm_ov)
  have rdPopArt := RD.pop (a := endFreeUrnArtWord urnOut)
    (t := [endFreeUrnInkWord urnOut, endFlowVatIlkRateWord vatOut, endSkimUrnKey I,
      endSkimIlkWord I, endSkimReturnPc, sel])
    rdPopOwe (by native_decide) (by evm_ov)
  have rdPopInk := RD.pop (a := endFreeUrnInkWord urnOut)
    (t := [endFlowVatIlkRateWord vatOut, endSkimUrnKey I, endSkimIlkWord I,
      endSkimReturnPc, sel])
    rdPopArt (by native_decide) (by evm_ov)
  have rdPopRate := RD.pop (a := endFlowVatIlkRateWord vatOut)
    (t := [endSkimUrnKey I, endSkimIlkWord I, endSkimReturnPc, sel])
    rdPopInk (by native_decide) (by evm_ov)
  have rdPopUrn := RD.pop (a := endSkimUrnKey I)
    (t := [endSkimIlkWord I, endSkimReturnPc, sel])
    rdPopRate (by native_decide) (by evm_ov)
  have rdPopIlk := RD.pop (a := endSkimIlkWord I)
    (t := [endSkimReturnPc, sel])
    rdPopUrn (by native_decide) (by evm_ov)
  have rd562 := RD.jump (a := endSkimReturnPc) (t := [sel]) rdPopIlk
    (by native_decide) (by jump_dest) (by evm_ov)
  have rd563 := RD.jumpdest (pc := endSkimReturnPc) (stk := [sel]) rd562
    (by native_decide) (by evm_ov)
  exact RD.stop rd563 (by native_decide) (by evm_ov)

theorem evalExpr_endSkim_ilk (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endSkimStore I } evm (.var "ilk") =
      .ok (.fixedBytes bytes32Width (endSkimIlkBytes I)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((endSkimStore I).get? "ilk") =
    .ok (.fixedBytes bytes32Width (endSkimIlkBytes I))
  rw [endSkimStore_get_ilk]
  rfl

theorem evalStorageRef_endSkim_tag (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := endSkimStore I } evm
      (tagRef (.var "ilk")) = .ok (endSkimTagEvaledRef I) := by
  have hargLen : min 32 (I.calldata.toList.length - 4) = bytes32Width.val + 1 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [htlen]
    simp [bytes32Width]
    omega
  have hilk := evalExpr_endSkim_ilk evm I
  simp [endSkimTagEvaledRef, endSkimIlkKey, hilk, endSkimIlkBytes,
    endBytes32ArgKey, endBytes32ArgBytes, evalStorageRef, evalStorageRefSteps,
    evalStorageRefStep, tagRef, valueToKey?, EvalResult.ofOption, EvalResult.bind,
    pure, bind]
  rw [if_pos hargLen]

theorem evalExpr_endSkim_tag (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := endSkimStore I } evm
      (.storage (tagRef (.var "ilk"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (endSkimTagSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := endSkimStore I })
    (slot := tagRef (.var "ilk"))
    (er := endSkimTagEvaledRef I)
    (t := .int uint256Int)
    (loc := wordLoc (endSkimTagSlot I))
    (hbase := by simp [endSkimStore, tagRef])
    (her := evalStorageRef_endSkim_tag evm I hsz68)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := endStorageLocLoad_uint256 evm (endSkimTagSlot I))

theorem evalExpr_endSkim_tag_ne_false (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (htag :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endSkimTagSlot I) = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endSkimStore I } evm
      (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endSkimStore I } evm
        (.storage (tagRef (.var "ilk"))) = .ok (.int 0) := by
    simpa [htag] using evalExpr_endSkim_tag evm I hsz68
  have hzero :
      evalExpr? config { contract := contract, locals := endSkimStore I } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  exact endEvalExpr_ne_int_false hstorage hzero rfl

theorem evalExpr_endSkim_tag_ne_true (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (htag :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endSkimTagSlot I) ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endSkimStore I } evm
      (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endSkimStore I } evm
        (.storage (tagRef (.var "ilk"))) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (endSkimTagSlot I)).toNat)) :=
    evalExpr_endSkim_tag evm I hsz68
  have hzero :
      evalExpr? config { contract := contract, locals := endSkimStore I } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  apply endEvalExpr_ne_int_true hstorage hzero
  intro hbad
  exact htag (uint256_toNat_eq_zero (Int.ofNat.inj hbad))

theorem endSkimCheckedVatIlksNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := endSkimStore I } evm0
      (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
        "vatIlk") .reverted := by
  intro evm0
  have hreceiver :
      evalExpr? config { contract := contract, locals := endSkimStore I } evm0
        (.storage vatRef) = .ok (.address (endPackVatAddr σ I)) := by
    have hbase : (endSkimStore I).get? "vat" = none := by
      simp [endSkimStore]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endPack_vat (locals := endSkimStore I) evm0 hbase
  have hcodeZero :
      (UInt256.ofNat
        ((evm0.lookupAccount (endPackVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat =
        0 := by
    simpa [evm0] using
      endPackVatCode_zero_of_codeSize_zero
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSkimStore I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  simpa [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm0)
      (locals := endSkimStore I) (receiver := .storage vatRef)
      (retVar := "vatIlk") (name := "vatIlks") (sendVal := 0)
      (args := [.var "ilk"]) (perm := true) hguard

theorem endSkimCheckedVatIlksFailure {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat : EVM.State} {out : ByteArray}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "vatIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (false, evmVat, out) true) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := endSkimStore I } evm0
      (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
        "vatIlk") .reverted := by
  intro evm0
  have hreceiver :
      evalExpr? config { contract := contract, locals := endSkimStore I } evm0
        (.storage vatRef) = .ok (.address (endPackVatAddr σ I)) := by
    have hbase : (endSkimStore I).get? "vat" = none := by
      simp [endSkimStore]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endPack_vat (locals := endSkimStore I) evm0 hbase
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm0.lookupAccount (endPackVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
    simpa [evm0] using
      endPackVatCode_pos_of_codeSize_ne
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSkimStore I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hilk :
      evalExpr? config { contract := contract, locals := endSkimStore I } evm0 (.var "ilk") =
        .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((endSkimStore I).get? "ilk") =
      .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I))
    rw [endSkimStore_get_ilk]
    rfl
  have hargs :
      evalExprs? config { contract := contract, locals := endSkimStore I } evm0 [.var "ilk"] =
        .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I)] := by
    simp [evalExprs?, hilk, EvalResult.bind, bind, pure]
  simpa [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config) (C := contract) (evm := evm0) (evm' := evmVat)
      (locals := endSkimStore I) (receiver := .storage vatRef)
      (retVar := "vatIlk") (name := "vatIlks") (target := endPackVatAddr σ I)
      (sendVal := 0) (args := [.var "ilk"])
      (argVals := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
      (out := out) (perm := true) hguard hreceiver hargs (by simpa [evm0] using hcall)

theorem endSkimCheckedVatIlksDecodeRevert {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat : EVM.State} {out : ByteArray}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "vatIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmVat, out) true)
    (hshort : out.size < 160) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := endSkimStore I } evm0
      (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
        "vatIlk") .reverted := by
  intro evm0
  have hreceiver :
      evalExpr? config { contract := contract, locals := endSkimStore I } evm0
        (.storage vatRef) = .ok (.address (endPackVatAddr σ I)) := by
    have hbase : (endSkimStore I).get? "vat" = none := by
      simp [endSkimStore]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endPack_vat (locals := endSkimStore I) evm0 hbase
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm0.lookupAccount (endPackVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
    simpa [evm0] using
      endPackVatCode_pos_of_codeSize_ne
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSkimStore I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hilk :
      evalExpr? config { contract := contract, locals := endSkimStore I } evm0 (.var "ilk") =
        .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((endSkimStore I).get? "ilk") =
      .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I))
    rw [endSkimStore_get_ilk]
    rfl
  have hargs :
      evalExprs? config { contract := contract, locals := endSkimStore I } evm0 [.var "ilk"] =
        .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I)] := by
    simp [evalExprs?, hilk, EvalResult.bind, bind, pure]
  simpa [checkedExternalCallStmts] using
    checkedExternalCallDecodeRevert
      (cfg := config) (C := contract) (evm := evm0) (evm' := evmVat)
      (locals := endSkimStore I) (receiver := .storage vatRef)
      (retVar := "vatIlk") (name := "vatIlks") (target := endPackVatAddr σ I)
      (sendVal := 0) (args := [.var "ilk"])
      (argVals := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
      (out := out) (perm := true) hguard hreceiver hargs
      (by simpa [evm0] using hcall) (endFlowVatIlksDecode_none_short hshort)

theorem endSkimCheckedVatIlksSuccess {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat : EVM.State} {out : ByteArray}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "vatIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmVat, out) true)
    (hlo : 160 ≤ out.size) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := endSkimStore I } evm0
      (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
        "vatIlk")
      (.ok { contract := contract, locals := endSkimStoreVatIlk I out } evmVat) := by
  intro evm0
  have hreceiver :
      evalExpr? config { contract := contract, locals := endSkimStore I } evm0
        (.storage vatRef) = .ok (.address (endPackVatAddr σ I)) := by
    have hbase : (endSkimStore I).get? "vat" = none := by
      simp [endSkimStore]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endPack_vat (locals := endSkimStore I) evm0 hbase
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm0.lookupAccount (endPackVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
    simpa [evm0] using
      endPackVatCode_pos_of_codeSize_ne
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSkimStore I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hilk :
      evalExpr? config { contract := contract, locals := endSkimStore I } evm0 (.var "ilk") =
        .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((endSkimStore I).get? "ilk") =
      .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I))
    rw [endSkimStore_get_ilk]
    rfl
  have hargs :
      evalExprs? config { contract := contract, locals := endSkimStore I } evm0 [.var "ilk"] =
        .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I)] := by
    simp [evalExprs?, hilk, EvalResult.bind, bind, pure]
  have hvalue := endFlowVatIlksDecode_ok (out := out) hlo
  have hblock := checkedExternalCallSuccess
    (cfg := config) (C := contract) (evm := evm0) (evm' := evmVat)
    (locals := endSkimStore I) (receiver := .storage vatRef)
    (retVar := "vatIlk") (name := "vatIlks") (target := endPackVatAddr σ I)
    (sendVal := 0) (args := [.var "ilk"])
    (argVals := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
    (out := out) (perm := true)
    (value :=
      [.int (Int.ofNat (endFlowVatIlkArtWord out).toNat),
        .int (Int.ofNat (endFlowVatIlkRateWord out).toNat),
        .int (Int.ofNat (endFlowVatIlkSpotWord out).toNat),
        .int (Int.ofNat (endFlowVatIlkLineWord out).toNat),
        .int (Int.ofNat (endFlowVatIlkDustWord out).toNat)])
    hguard hreceiver hargs (by simpa [evm0] using hcall) hvalue
  simpa [checkedExternalCallStmts, endSkimStoreVatIlk, collapseReturns] using hblock

theorem evalExpr_endSkim_vatIlk_rate (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    evalExpr? config { contract := contract, locals := endSkimStoreVatIlk I out } evm
      (.tupleGet (.var "vatIlk") 1) =
        .ok (.int (Int.ofNat (endFlowVatIlkRateWord out).toNat)) := by
  have hvar :
      evalExpr? config { contract := contract, locals := endSkimStoreVatIlk I out } evm
        (.var "vatIlk") =
          .ok (.tuple [.int (Int.ofNat (endFlowVatIlkArtWord out).toNat),
            .int (Int.ofNat (endFlowVatIlkRateWord out).toNat),
            .int (Int.ofNat (endFlowVatIlkSpotWord out).toNat),
            .int (Int.ofNat (endFlowVatIlkLineWord out).toNat),
            .int (Int.ofNat (endFlowVatIlkDustWord out).toNat)]) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((endSkimStoreVatIlk I out).get? "vatIlk") =
        .ok (.tuple [.int (Int.ofNat (endFlowVatIlkArtWord out).toNat),
          .int (Int.ofNat (endFlowVatIlkRateWord out).toNat),
          .int (Int.ofNat (endFlowVatIlkSpotWord out).toNat),
          .int (Int.ofNat (endFlowVatIlkLineWord out).toNat),
          .int (Int.ofNat (endFlowVatIlkDustWord out).toNat)])
    rw [endSkimStoreVatIlk, store_get_self]
    rfl
  rw [evalExpr?]
  simp [hvar, tupleGetValue?, EvalResult.bind, bind]

theorem endSkimStmtRate (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    ExecStmt config { contract := contract, locals := endSkimStoreVatIlk I out } evm
      (.letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1))
      (.ok { contract := contract, locals := endSkimStoreRate I out } evm) := by
  simpa [endSkimStoreRate] using
    ExecStmt.letDecl (evalExpr_endSkim_vatIlk_rate evm I out)

theorem evalExprs_endSkim_urnsArgs (evm : EVM.State) (I : ExecutionEnv)
    (vatOut : ByteArray) :
    evalExprs? config { contract := contract, locals := endSkimStoreRate I vatOut } evm
      [.var "ilk", .var "urn"] =
        .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I), .address (endSkimUrnAddr I)] := by
  have hilk :
      evalExpr? config { contract := contract, locals := endSkimStoreRate I vatOut } evm
        (.var "ilk") = .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((endSkimStoreRate I vatOut).get? "ilk") =
        .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I))
    rw [endSkimStoreRate, store_get_ne _ _ (by native_decide),
      endSkimStoreVatIlk, store_get_ne _ _ (by native_decide), endSkimStore_get_ilk]
    rfl
  have hurn :
      evalExpr? config { contract := contract, locals := endSkimStoreRate I vatOut } evm
        (.var "urn") = .ok (.address (endSkimUrnAddr I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((endSkimStoreRate I vatOut).get? "urn") =
        .ok (.address (endSkimUrnAddr I))
    rw [endSkimStoreRate, store_get_ne _ _ (by native_decide),
      endSkimStoreVatIlk, store_get_ne _ _ (by native_decide), endSkimStore, store_get_self]
    rfl
  simp [evalExprs?, hilk, hurn, EvalResult.bind, bind, pure]

theorem endSkimVatReceiver_afterRate {σ I vatOut evm}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    evalExpr? config { contract := contract, locals := endSkimStoreRate I vatOut } evm
      (.storage vatRef) = .ok (.address (endPackVatAddr σ I)) := by
  have hbase : (endSkimStoreRate I vatOut).get? "vat" = none := by
    simp [endSkimStoreRate, endSkimStoreVatIlk, endSkimStore]
  simpa [hmap, howner, Solm.EVM.storageLoad, State.lookupAccount,
    endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
    evalExpr_endPack_vat (locals := endSkimStoreRate I vatOut) evm hbase

theorem endSkimVatCode_zero_afterRate {σ I} {vatOut : ByteArray} {evm : EVM.State}
    (hmap : evm.accountMap = σ)
    (hzero : Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount (endPackVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat =
        0 := by
  simpa [State.lookupAccount, hmap] using
    endUniswapExtCodeSizeWord_zero_lookup_code_zero
      (σ := σ) (target := endPackVatWord σ I) (addr := endPackVatAddr σ I)
      (endPackVatAddr_eq_ofUInt256 σ I) hzero

theorem endSkimVatCode_pos_afterRate {σ I} {vatOut : ByteArray} {evm : EVM.State}
    (hmap : evm.accountMap = σ)
    (hne : Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((evm.lookupAccount (endPackVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
  simpa [State.lookupAccount, hmap] using
    endUniswapExtCodeSizeWord_ne_zero_lookup_code_pos
      (σ := σ) (target := endPackVatWord σ I) (addr := endPackVatAddr σ I)
      (endPackVatAddr_eq_ofUInt256 σ I) hne

theorem endSkimCheckedUrnsNoCode {σ I} {vatOut : ByteArray} {evm : EVM.State}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) = ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endSkimStoreRate I vatOut } evm
      (checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0)
        [.var "ilk", .var "urn"] "vatUrn") .reverted := by
  have hreceiver := endSkimVatReceiver_afterRate (σ := σ) (I := I) (vatOut := vatOut)
    (evm := evm) hmap howner
  have hcodeZero := endSkimVatCode_zero_afterRate (σ := σ) (I := I) (vatOut := vatOut)
    (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSkimStoreRate I vatOut } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  simpa [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm)
      (locals := endSkimStoreRate I vatOut) (receiver := .storage vatRef)
      (retVar := "vatUrn") (name := "urns") (sendVal := 0)
      (args := [.var "ilk", .var "urn"]) (perm := true) hguard

theorem endSkimCheckedUrnsFailure {σ I} {vatOut urnOut : ByteArray}
    {evm evmUrns : EVM.State}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endPackVatAddr σ I)) "urns" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I), .address (endSkimUrnAddr I)]
        (false, evmUrns, urnOut) true) :
    ExecBlock config { contract := contract, locals := endSkimStoreRate I vatOut } evm
      (checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0)
        [.var "ilk", .var "urn"] "vatUrn") .reverted := by
  have hreceiver := endSkimVatReceiver_afterRate (σ := σ) (I := I) (vatOut := vatOut)
    (evm := evm) hmap howner
  have hcodePos := endSkimVatCode_pos_afterRate (σ := σ) (I := I) (vatOut := vatOut)
    (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSkimStoreRate I vatOut } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs := evalExprs_endSkim_urnsArgs evm I vatOut
  simpa [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config) (C := contract) (evm := evm) (evm' := evmUrns)
      (locals := endSkimStoreRate I vatOut) (receiver := .storage vatRef)
      (retVar := "vatUrn") (name := "urns") (target := endPackVatAddr σ I)
      (sendVal := 0) (args := [.var "ilk", .var "urn"])
      (argVals := [.fixedBytes bytes32Width (endBytes32ArgBytes I),
        .address (endSkimUrnAddr I)])
      (out := urnOut) (perm := true) hguard hreceiver hargs hcall

theorem endSkimCheckedUrnsDecodeRevert {σ I} {vatOut urnOut : ByteArray}
    {evm evmUrns : EVM.State}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endPackVatAddr σ I)) "urns" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I), .address (endSkimUrnAddr I)]
        (true, evmUrns, urnOut) true)
    (hshort : urnOut.size < 64) :
    ExecBlock config { contract := contract, locals := endSkimStoreRate I vatOut } evm
      (checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0)
        [.var "ilk", .var "urn"] "vatUrn") .reverted := by
  have hreceiver := endSkimVatReceiver_afterRate (σ := σ) (I := I) (vatOut := vatOut)
    (evm := evm) hmap howner
  have hcodePos := endSkimVatCode_pos_afterRate (σ := σ) (I := I) (vatOut := vatOut)
    (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSkimStoreRate I vatOut } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs := evalExprs_endSkim_urnsArgs evm I vatOut
  simpa [checkedExternalCallStmts] using
    checkedExternalCallDecodeRevert
      (cfg := config) (C := contract) (evm := evm) (evm' := evmUrns)
      (locals := endSkimStoreRate I vatOut) (receiver := .storage vatRef)
      (retVar := "vatUrn") (name := "urns") (target := endPackVatAddr σ I)
      (sendVal := 0) (args := [.var "ilk", .var "urn"])
      (argVals := [.fixedBytes bytes32Width (endBytes32ArgBytes I),
        .address (endSkimUrnAddr I)])
      (out := urnOut) (perm := true) hguard hreceiver hargs hcall
      (endFreeUrnsDecode_none_short hshort)

theorem endSkimCheckedUrnsSuccess {σ I} {vatOut urnOut : ByteArray}
    {evm evmUrns : EVM.State}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endPackVatAddr σ I)) "urns" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I), .address (endSkimUrnAddr I)]
        (true, evmUrns, urnOut) true)
    (hlo : 64 ≤ urnOut.size) :
    ExecBlock config { contract := contract, locals := endSkimStoreRate I vatOut } evm
      (checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0)
        [.var "ilk", .var "urn"] "vatUrn")
      (.ok { contract := contract, locals := endSkimStoreVatUrn I vatOut urnOut } evmUrns) := by
  have hreceiver := endSkimVatReceiver_afterRate (σ := σ) (I := I) (vatOut := vatOut)
    (evm := evm) hmap howner
  have hcodePos := endSkimVatCode_pos_afterRate (σ := σ) (I := I) (vatOut := vatOut)
    (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSkimStoreRate I vatOut } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs := evalExprs_endSkim_urnsArgs evm I vatOut
  have hblock := checkedExternalCallSuccess
    (cfg := config) (C := contract) (evm := evm) (evm' := evmUrns)
    (locals := endSkimStoreRate I vatOut) (receiver := .storage vatRef)
    (retVar := "vatUrn") (name := "urns") (target := endPackVatAddr σ I)
    (sendVal := 0) (args := [.var "ilk", .var "urn"])
    (argVals := [.fixedBytes bytes32Width (endBytes32ArgBytes I),
      .address (endSkimUrnAddr I)])
    (out := urnOut) (perm := true)
    (value :=
      [.int (Int.ofNat (endFreeUrnInkWord urnOut).toNat),
        .int (Int.ofNat (endFreeUrnArtWord urnOut).toNat)])
    hguard hreceiver hargs hcall (endFreeUrnsDecode_ok hlo)
  simpa [checkedExternalCallStmts, endSkimStoreVatUrn, collapseReturns] using hblock

theorem evalExpr_endSkim_vatUrn_ink (evm : EVM.State) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endSkimStoreVatUrn I vatOut urnOut } evm
      (.tupleGet (.var "vatUrn") 0) =
        .ok (.int (Int.ofNat (endFreeUrnInkWord urnOut).toNat)) := by
  have hvar :
      evalExpr? config { contract := contract, locals := endSkimStoreVatUrn I vatOut urnOut }
        evm (.var "vatUrn") =
          .ok (.tuple [.int (Int.ofNat (endFreeUrnInkWord urnOut).toNat),
            .int (Int.ofNat (endFreeUrnArtWord urnOut).toNat)]) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((endSkimStoreVatUrn I vatOut urnOut).get? "vatUrn") =
        .ok (.tuple [.int (Int.ofNat (endFreeUrnInkWord urnOut).toNat),
          .int (Int.ofNat (endFreeUrnArtWord urnOut).toNat)])
    rw [endSkimStoreVatUrn, store_get_self]
    rfl
  rw [evalExpr?]
  simp [hvar, tupleGetValue?, EvalResult.bind, bind]

theorem evalExpr_endSkim_vatUrn_art_afterInk (evm : EVM.State) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endSkimStoreInk I vatOut urnOut } evm
      (.tupleGet (.var "vatUrn") 1) =
        .ok (.int (Int.ofNat (endFreeUrnArtWord urnOut).toNat)) := by
  have hvar :
      evalExpr? config { contract := contract, locals := endSkimStoreInk I vatOut urnOut }
        evm (.var "vatUrn") =
          .ok (.tuple [.int (Int.ofNat (endFreeUrnInkWord urnOut).toNat),
            .int (Int.ofNat (endFreeUrnArtWord urnOut).toNat)]) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((endSkimStoreInk I vatOut urnOut).get? "vatUrn") =
        .ok (.tuple [.int (Int.ofNat (endFreeUrnInkWord urnOut).toNat),
          .int (Int.ofNat (endFreeUrnArtWord urnOut).toNat)])
    rw [endSkimStoreInk, store_get_ne _ _ (by native_decide),
      endSkimStoreVatUrn, store_get_self]
    rfl
  rw [evalExpr?]
  simp [hvar, tupleGetValue?, EvalResult.bind, bind]

theorem endSkimStmtInk (evm : EVM.State) (I : ExecutionEnv) (vatOut urnOut : ByteArray) :
    ExecStmt config { contract := contract, locals := endSkimStoreVatUrn I vatOut urnOut } evm
      (.letDecl "ink" (some uint256) (.tupleGet (.var "vatUrn") 0))
      (.ok { contract := contract, locals := endSkimStoreInk I vatOut urnOut } evm) := by
  simpa [endSkimStoreInk] using
    ExecStmt.letDecl (evalExpr_endSkim_vatUrn_ink evm I vatOut urnOut)

theorem endSkimStmtArt (evm : EVM.State) (I : ExecutionEnv) (vatOut urnOut : ByteArray) :
    ExecStmt config { contract := contract, locals := endSkimStoreInk I vatOut urnOut } evm
      (.letDecl "art" (some uint256) (.tupleGet (.var "vatUrn") 1))
      (.ok { contract := contract, locals := endSkimStoreArt I vatOut urnOut } evm) := by
  simpa [endSkimStoreArt] using
    ExecStmt.letDecl (evalExpr_endSkim_vatUrn_art_afterInk evm I vatOut urnOut)

theorem endExecMinFunctionReturn (evm : EVM.State) {x y z : UInt256}
    (hz : z = if x.toNat ≤ y.toNat then x else y) :
    ExecFuncBody config { contract := contract, locals := endUintBinaryLocals x y } evm
      minFunction.body
      (.returned { contract := contract, locals := endUintBinaryLocals x y } evm
        (some [.int (Int.ofNat z.toNat)])) := by
  let locals := endUintBinaryLocals x y
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (endUintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (endUintBinaryLocals_get_y x y)
  by_cases hle : x.toNat ≤ y.toNat
  · have hcond :
        evalExpr? config { contract := contract, locals := locals } evm
          (.binary .le (.var "x") (.var "y")) = .ok (.bool true) :=
      endThawEvalExpr_le_uint256_true hx hy hle
    have hxRet :
        evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
          .ok (.int (Int.ofNat z.toNat)) := by
      simpa [hz, hle] using hx
    have hthen :
        ExecBlock config { contract := contract, locals := locals } evm
          [.return [.var "x"]]
          (.returned { contract := contract, locals := locals } evm
            (some [.int (Int.ofNat z.toNat)])) := by
      exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hxRet))
    have hblock :
        ExecBlock config { contract := contract, locals := locals } evm
          [ .ite (.binary .le (.var "x") (.var "y"))
              [ .return [.var "x"] ] [ .return [.var "y"] ] ]
          (.returned { contract := contract, locals := locals } evm
            (some [.int (Int.ofNat z.toNat)])) := by
      exact ExecBlock.consReturn (ExecStmt.iteTrue hcond hthen)
    simpa [minFunction, locals] using ExecFuncBody.execBlockRet hblock
  · have hlt : y.toNat < x.toNat := Nat.lt_of_not_ge hle
    have hcond :
        evalExpr? config { contract := contract, locals := locals } evm
          (.binary .le (.var "x") (.var "y")) = .ok (.bool false) := by
      simp [evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?]
      exact hlt
    have hyRet :
        evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
          .ok (.int (Int.ofNat z.toNat)) := by
      simpa [hz, hle] using hy
    have helse :
        ExecBlock config { contract := contract, locals := locals } evm
          [.return [.var "y"]]
          (.returned { contract := contract, locals := locals } evm
            (some [.int (Int.ofNat z.toNat)])) := by
      exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hyRet))
    have hblock :
        ExecBlock config { contract := contract, locals := locals } evm
          [ .ite (.binary .le (.var "x") (.var "y"))
              [ .return [.var "x"] ] [ .return [.var "y"] ] ]
          (.returned { contract := contract, locals := locals } evm
            (some [.int (Int.ofNat z.toNat)])) := by
      exact ExecBlock.consReturn (ExecStmt.iteFalse hcond helse)
    simpa [minFunction, locals] using ExecFuncBody.execBlockRet hblock

theorem endSkimStmtOwe0RmulReturns (evm : EVM.State) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray)
    (hfit :
      (endFreeUrnArtWord urnOut).toNat * (endFlowVatIlkRateWord vatOut).toNat <
        UInt256.size) :
    ExecStmt config { contract := contract, locals := endSkimStoreArt I vatOut urnOut } evm
      (.internalCall "rmul" [.var "art", .var "rate"] "owe0")
      (.ok { contract := contract, locals := endSkimStoreOwe0 I vatOut urnOut } evm) := by
  have hart :
      evalExpr? config { contract := contract, locals := endSkimStoreArt I vatOut urnOut } evm
        (.var "art") = .ok (.int (Int.ofNat (endFreeUrnArtWord urnOut).toNat)) := by
    simpa [endSkimStoreArt] using
      endEvalExpr_varUInt256 (evm := evm)
        (locals := endSkimStoreArt I vatOut urnOut)
        (name := "art") (value := endFreeUrnArtWord urnOut)
        (by simp [endSkimStoreArt])
  have hrate :
      evalExpr? config { contract := contract, locals := endSkimStoreArt I vatOut urnOut } evm
        (.var "rate") = .ok (.int (Int.ofNat (endFlowVatIlkRateWord vatOut).toNat)) := by
    simpa [endSkimStoreArt, endSkimStoreInk, endSkimStoreVatUrn, endSkimStoreRate] using
      endEvalExpr_varUInt256 (evm := evm)
        (locals := endSkimStoreArt I vatOut urnOut)
        (name := "rate") (value := endFlowVatIlkRateWord vatOut)
        (by
          rw [endSkimStoreArt, store_get_ne _ _ (by native_decide),
            endSkimStoreInk, store_get_ne _ _ (by native_decide),
            endSkimStoreVatUrn, store_get_ne _ _ (by native_decide),
            endSkimStoreRate, store_get_self])
  have hargs :
      evalExprs? config { contract := contract, locals := endSkimStoreArt I vatOut urnOut }
        evm [.var "art", .var "rate"] =
          .ok [.int (Int.ofNat (endFreeUrnArtWord urnOut).toNat),
            .int (Int.ofNat (endFlowVatIlkRateWord vatOut).toNat)] := by
    simp [evalExprs?, hart, hrate, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? rmulFunction.params
          [.int (Int.ofNat (endFreeUrnArtWord urnOut).toNat),
            .int (Int.ofNat (endFlowVatIlkRateWord vatOut).toNat)] =
        some (endUintBinaryLocals (endFreeUrnArtWord urnOut)
          (endFlowVatIlkRateWord vatOut)) := by
    simp [rmulFunction, uint256, bindParams?, endUintBinaryLocals]
  have hbody :=
    endExecRmulFunctionReturn (evm := evm)
      (x := endFreeUrnArtWord urnOut) (y := endFlowVatIlkRateWord vatOut)
      (prod := endFreeUrnArtWord urnOut * endFlowVatIlkRateWord vatOut)
      (q := endSkimOwe0Word vatOut urnOut) rfl hfit rfl
  have hstmt := internalCallFunctionReturn
    (cfg := config) (caller := { contract := contract, locals := endSkimStoreArt I vatOut urnOut })
    (evm := evm) (name := "rmul") (retVar := "owe0")
    (args := [.var "art", .var "rate"])
    (argVals :=
      [.int (Int.ofNat (endFreeUrnArtWord urnOut).toNat),
        .int (Int.ofNat (endFlowVatIlkRateWord vatOut).toNat)])
    (callee := rmulFunction)
    (locals := endUintBinaryLocals (endFreeUrnArtWord urnOut)
      (endFlowVatIlkRateWord vatOut))
    hargs (by rfl) hbind hbody
  simpa [endSkimStoreOwe0, resumeAfterInternalCall, collapseReturns,
    endSkimOwe0Word] using hstmt

theorem endSkimStmtOwe0RmulReverts (evm : EVM.State) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray)
    (hover :
      UInt256.size ≤
        (endFreeUrnArtWord urnOut).toNat * (endFlowVatIlkRateWord vatOut).toNat) :
    ExecStmt config { contract := contract, locals := endSkimStoreArt I vatOut urnOut } evm
      (.internalCall "rmul" [.var "art", .var "rate"] "owe0") .reverted := by
  have hart :
      evalExpr? config { contract := contract, locals := endSkimStoreArt I vatOut urnOut } evm
        (.var "art") = .ok (.int (Int.ofNat (endFreeUrnArtWord urnOut).toNat)) := by
    simpa [endSkimStoreArt] using
      endEvalExpr_varUInt256 (evm := evm)
        (locals := endSkimStoreArt I vatOut urnOut)
        (name := "art") (value := endFreeUrnArtWord urnOut)
        (by simp [endSkimStoreArt])
  have hrate :
      evalExpr? config { contract := contract, locals := endSkimStoreArt I vatOut urnOut } evm
        (.var "rate") = .ok (.int (Int.ofNat (endFlowVatIlkRateWord vatOut).toNat)) := by
    simpa [endSkimStoreArt, endSkimStoreInk, endSkimStoreVatUrn, endSkimStoreRate] using
      endEvalExpr_varUInt256 (evm := evm)
        (locals := endSkimStoreArt I vatOut urnOut)
        (name := "rate") (value := endFlowVatIlkRateWord vatOut)
        (by
          rw [endSkimStoreArt, store_get_ne _ _ (by native_decide),
            endSkimStoreInk, store_get_ne _ _ (by native_decide),
            endSkimStoreVatUrn, store_get_ne _ _ (by native_decide),
            endSkimStoreRate, store_get_self])
  have hargs :
      evalExprs? config { contract := contract, locals := endSkimStoreArt I vatOut urnOut }
        evm [.var "art", .var "rate"] =
          .ok [.int (Int.ofNat (endFreeUrnArtWord urnOut).toNat),
            .int (Int.ofNat (endFlowVatIlkRateWord vatOut).toNat)] := by
    simp [evalExprs?, hart, hrate, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? rmulFunction.params
          [.int (Int.ofNat (endFreeUrnArtWord urnOut).toNat),
            .int (Int.ofNat (endFlowVatIlkRateWord vatOut).toNat)] =
        some (endUintBinaryLocals (endFreeUrnArtWord urnOut)
          (endFlowVatIlkRateWord vatOut)) := by
    simp [rmulFunction, uint256, bindParams?, endUintBinaryLocals]
  have hbody :=
    endExecRmulFunctionRevertMul (evm := evm)
      (x := endFreeUrnArtWord urnOut) (y := endFlowVatIlkRateWord vatOut) hover
  exact internalCallFunctionRevert
    (cfg := config) (caller := { contract := contract, locals := endSkimStoreArt I vatOut urnOut })
    (evm := evm) (name := "rmul") (retVar := "owe0")
    (args := [.var "art", .var "rate"])
    (argVals :=
      [.int (Int.ofNat (endFreeUrnArtWord urnOut).toNat),
        .int (Int.ofNat (endFlowVatIlkRateWord vatOut).toNat)])
    (callee := rmulFunction)
    (locals := endUintBinaryLocals (endFreeUrnArtWord urnOut)
      (endFlowVatIlkRateWord vatOut))
    hargs (by rfl) hbind hbody

theorem endSkimStmtOweRmulReturns (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (vatOut urnOut : ByteArray)
    (hsz68 : 68 ≤ I.calldata.size)
    (hTagLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endSkimTagSlot I) =
        endSkimTagWord σ I)
    (hfit :
      (endSkimOwe0Word vatOut urnOut).toNat * (endSkimTagWord σ I).toNat <
        UInt256.size) :
    ExecStmt config { contract := contract, locals := endSkimStoreOwe0 I vatOut urnOut } evm
      (.internalCall "rmul" [.var "owe0", .storage (tagRef (.var "ilk"))] "owe")
      (.ok { contract := contract, locals := endSkimStoreOwe σ I vatOut urnOut } evm) := by
  have howe0 :
      evalExpr? config { contract := contract, locals := endSkimStoreOwe0 I vatOut urnOut }
        evm (.var "owe0") =
          .ok (.int (Int.ofNat (endSkimOwe0Word vatOut urnOut).toNat)) := by
    simpa [endSkimStoreOwe0] using
      endEvalExpr_varUInt256 (evm := evm)
        (locals := endSkimStoreOwe0 I vatOut urnOut)
        (name := "owe0") (value := endSkimOwe0Word vatOut urnOut)
        (by simp [endSkimStoreOwe0])
  have htag :
      evalExpr? config { contract := contract, locals := endSkimStoreOwe0 I vatOut urnOut }
        evm (.storage (tagRef (.var "ilk"))) =
          .ok (.int (Int.ofNat (endSkimTagWord σ I).toNat)) := by
    have hbase : (endSkimStoreOwe0 I vatOut urnOut).get? "tag" = none := by
      rw [endSkimStoreOwe0, store_get_ne _ _ (by native_decide),
        endSkimStoreArt, store_get_ne _ _ (by native_decide),
        endSkimStoreInk, store_get_ne _ _ (by native_decide),
        endSkimStoreVatUrn, store_get_ne _ _ (by native_decide),
        endSkimStoreRate, store_get_ne _ _ (by native_decide),
        endSkimStoreVatIlk, store_get_ne _ _ (by native_decide),
        endSkimStore, store_get_ne _ _ (by native_decide),
        store_get_ne _ _ (by native_decide)]
      simp
    have hget :
        (endSkimStoreOwe0 I vatOut urnOut).get? "ilk" = some (endFlowIlkValue I) := by
      rw [endSkimStoreOwe0, store_get_ne _ _ (by native_decide),
        endSkimStoreArt, store_get_ne _ _ (by native_decide),
        endSkimStoreInk, store_get_ne _ _ (by native_decide),
        endSkimStoreVatUrn, store_get_ne _ _ (by native_decide),
        endSkimStoreRate, store_get_ne _ _ (by native_decide),
        endSkimStoreVatIlk, store_get_ne _ _ (by native_decide),
        endSkimStore, store_get_ne _ _ (by native_decide), store_get_self]
    have hstorage := evalExpr_endFlow_tag_of_get evm I hbase hget (by omega)
    simpa [hTagLoad, endSkimTagWord, endFlowTagWord, endSkimTagSlot, endFlowTagSlot]
      using hstorage
  have hargs :
      evalExprs? config { contract := contract, locals := endSkimStoreOwe0 I vatOut urnOut }
        evm [.var "owe0", .storage (tagRef (.var "ilk"))] =
          .ok [.int (Int.ofNat (endSkimOwe0Word vatOut urnOut).toNat),
            .int (Int.ofNat (endSkimTagWord σ I).toNat)] := by
    simp [evalExprs?, howe0, htag, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? rmulFunction.params
          [.int (Int.ofNat (endSkimOwe0Word vatOut urnOut).toNat),
            .int (Int.ofNat (endSkimTagWord σ I).toNat)] =
        some (endUintBinaryLocals (endSkimOwe0Word vatOut urnOut)
          (endSkimTagWord σ I)) := by
    simp [rmulFunction, uint256, bindParams?, endUintBinaryLocals]
  have hbody :=
    endExecRmulFunctionReturn (evm := evm)
      (x := endSkimOwe0Word vatOut urnOut) (y := endSkimTagWord σ I)
      (prod := endSkimOwe0Word vatOut urnOut * endSkimTagWord σ I)
      (q := endSkimOweWord σ I vatOut urnOut) rfl hfit rfl
  have hstmt := internalCallFunctionReturn
    (cfg := config)
    (caller := { contract := contract, locals := endSkimStoreOwe0 I vatOut urnOut })
    (evm := evm) (name := "rmul") (retVar := "owe")
    (args := [.var "owe0", .storage (tagRef (.var "ilk"))])
    (argVals :=
      [.int (Int.ofNat (endSkimOwe0Word vatOut urnOut).toNat),
        .int (Int.ofNat (endSkimTagWord σ I).toNat)])
    (callee := rmulFunction)
    (locals := endUintBinaryLocals (endSkimOwe0Word vatOut urnOut)
      (endSkimTagWord σ I))
    hargs (by rfl) hbind hbody
  simpa [endSkimStoreOwe, resumeAfterInternalCall, collapseReturns,
    endSkimOweWord] using hstmt

theorem endSkimStmtOweRmulReverts (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (vatOut urnOut : ByteArray)
    (hsz68 : 68 ≤ I.calldata.size)
    (hTagLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endSkimTagSlot I) =
        endSkimTagWord σ I)
    (hover :
      UInt256.size ≤ (endSkimOwe0Word vatOut urnOut).toNat * (endSkimTagWord σ I).toNat) :
    ExecStmt config { contract := contract, locals := endSkimStoreOwe0 I vatOut urnOut } evm
      (.internalCall "rmul" [.var "owe0", .storage (tagRef (.var "ilk"))] "owe")
      .reverted := by
  have howe0 :
      evalExpr? config { contract := contract, locals := endSkimStoreOwe0 I vatOut urnOut }
        evm (.var "owe0") =
          .ok (.int (Int.ofNat (endSkimOwe0Word vatOut urnOut).toNat)) := by
    simpa [endSkimStoreOwe0] using
      endEvalExpr_varUInt256 (evm := evm)
        (locals := endSkimStoreOwe0 I vatOut urnOut)
        (name := "owe0") (value := endSkimOwe0Word vatOut urnOut)
        (by simp [endSkimStoreOwe0])
  have htag :
      evalExpr? config { contract := contract, locals := endSkimStoreOwe0 I vatOut urnOut }
        evm (.storage (tagRef (.var "ilk"))) =
          .ok (.int (Int.ofNat (endSkimTagWord σ I).toNat)) := by
    have hbase : (endSkimStoreOwe0 I vatOut urnOut).get? "tag" = none := by
      rw [endSkimStoreOwe0, store_get_ne _ _ (by native_decide),
        endSkimStoreArt, store_get_ne _ _ (by native_decide),
        endSkimStoreInk, store_get_ne _ _ (by native_decide),
        endSkimStoreVatUrn, store_get_ne _ _ (by native_decide),
        endSkimStoreRate, store_get_ne _ _ (by native_decide),
        endSkimStoreVatIlk, store_get_ne _ _ (by native_decide),
        endSkimStore, store_get_ne _ _ (by native_decide),
        store_get_ne _ _ (by native_decide)]
      simp
    have hget :
        (endSkimStoreOwe0 I vatOut urnOut).get? "ilk" = some (endFlowIlkValue I) := by
      rw [endSkimStoreOwe0, store_get_ne _ _ (by native_decide),
        endSkimStoreArt, store_get_ne _ _ (by native_decide),
        endSkimStoreInk, store_get_ne _ _ (by native_decide),
        endSkimStoreVatUrn, store_get_ne _ _ (by native_decide),
        endSkimStoreRate, store_get_ne _ _ (by native_decide),
        endSkimStoreVatIlk, store_get_ne _ _ (by native_decide),
        endSkimStore, store_get_ne _ _ (by native_decide), store_get_self]
    have hstorage := evalExpr_endFlow_tag_of_get evm I hbase hget (by omega)
    simpa [hTagLoad, endSkimTagWord, endFlowTagWord, endSkimTagSlot, endFlowTagSlot]
      using hstorage
  have hargs :
      evalExprs? config { contract := contract, locals := endSkimStoreOwe0 I vatOut urnOut }
        evm [.var "owe0", .storage (tagRef (.var "ilk"))] =
          .ok [.int (Int.ofNat (endSkimOwe0Word vatOut urnOut).toNat),
            .int (Int.ofNat (endSkimTagWord σ I).toNat)] := by
    simp [evalExprs?, howe0, htag, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? rmulFunction.params
          [.int (Int.ofNat (endSkimOwe0Word vatOut urnOut).toNat),
            .int (Int.ofNat (endSkimTagWord σ I).toNat)] =
        some (endUintBinaryLocals (endSkimOwe0Word vatOut urnOut)
          (endSkimTagWord σ I)) := by
    simp [rmulFunction, uint256, bindParams?, endUintBinaryLocals]
  have hbody :=
    endExecRmulFunctionRevertMul (evm := evm)
      (x := endSkimOwe0Word vatOut urnOut) (y := endSkimTagWord σ I) hover
  exact internalCallFunctionRevert
    (cfg := config)
    (caller := { contract := contract, locals := endSkimStoreOwe0 I vatOut urnOut })
    (evm := evm) (name := "rmul") (retVar := "owe")
    (args := [.var "owe0", .storage (tagRef (.var "ilk"))])
    (argVals :=
      [.int (Int.ofNat (endSkimOwe0Word vatOut urnOut).toNat),
        .int (Int.ofNat (endSkimTagWord σ I).toNat)])
    (callee := rmulFunction)
    (locals := endUintBinaryLocals (endSkimOwe0Word vatOut urnOut)
      (endSkimTagWord σ I))
    hargs (by rfl) hbind hbody

theorem endSkimStmtWadMinReturns (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (vatOut urnOut : ByteArray) :
    ExecStmt config { contract := contract, locals := endSkimStoreOwe σ I vatOut urnOut } evm
      (.internalCall "min" [.var "ink", .var "owe"] "wad")
      (.ok { contract := contract, locals := endSkimStoreWad σ I vatOut urnOut } evm) := by
  have hink :
      evalExpr? config { contract := contract, locals := endSkimStoreOwe σ I vatOut urnOut }
        evm (.var "ink") =
          .ok (.int (Int.ofNat (endFreeUrnInkWord urnOut).toNat)) := by
    simpa [endSkimStoreOwe, endSkimStoreOwe0, endSkimStoreArt, endSkimStoreInk] using
      endEvalExpr_varUInt256 (evm := evm)
        (locals := endSkimStoreOwe σ I vatOut urnOut)
        (name := "ink") (value := endFreeUrnInkWord urnOut)
        (by
          rw [endSkimStoreOwe, store_get_ne _ _ (by native_decide),
            endSkimStoreOwe0, store_get_ne _ _ (by native_decide),
            endSkimStoreArt, store_get_ne _ _ (by native_decide),
            endSkimStoreInk, store_get_self])
  have howe :
      evalExpr? config { contract := contract, locals := endSkimStoreOwe σ I vatOut urnOut }
        evm (.var "owe") =
          .ok (.int (Int.ofNat (endSkimOweWord σ I vatOut urnOut).toNat)) := by
    simpa [endSkimStoreOwe] using
      endEvalExpr_varUInt256 (evm := evm)
        (locals := endSkimStoreOwe σ I vatOut urnOut)
        (name := "owe") (value := endSkimOweWord σ I vatOut urnOut)
        (by simp [endSkimStoreOwe])
  have hargs :
      evalExprs? config { contract := contract, locals := endSkimStoreOwe σ I vatOut urnOut }
        evm [.var "ink", .var "owe"] =
          .ok [.int (Int.ofNat (endFreeUrnInkWord urnOut).toNat),
            .int (Int.ofNat (endSkimOweWord σ I vatOut urnOut).toNat)] := by
    simp [evalExprs?, hink, howe, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? minFunction.params
          [.int (Int.ofNat (endFreeUrnInkWord urnOut).toNat),
            .int (Int.ofNat (endSkimOweWord σ I vatOut urnOut).toNat)] =
        some (endUintBinaryLocals (endFreeUrnInkWord urnOut)
          (endSkimOweWord σ I vatOut urnOut)) := by
    simp [minFunction, uint256, bindParams?, endUintBinaryLocals]
  have hbody :=
    endExecMinFunctionReturn (evm := evm)
      (x := endFreeUrnInkWord urnOut) (y := endSkimOweWord σ I vatOut urnOut)
      (z := endSkimWadWord σ I vatOut urnOut) rfl
  have hstmt := internalCallFunctionReturn
    (cfg := config)
    (caller := { contract := contract, locals := endSkimStoreOwe σ I vatOut urnOut })
    (evm := evm) (name := "min") (retVar := "wad")
    (args := [.var "ink", .var "owe"])
    (argVals :=
      [.int (Int.ofNat (endFreeUrnInkWord urnOut).toNat),
        .int (Int.ofNat (endSkimOweWord σ I vatOut urnOut).toNat)])
    (callee := minFunction)
    (locals := endUintBinaryLocals (endFreeUrnInkWord urnOut)
      (endSkimOweWord σ I vatOut urnOut))
    hargs (by rfl) hbind hbody
  simpa [endSkimStoreWad, resumeAfterInternalCall, collapseReturns,
    endSkimWadWord] using hstmt

theorem endSkimWad_le_owe (σ : AccountMap) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray) :
    (endSkimWadWord σ I vatOut urnOut).toNat ≤
      (endSkimOweWord σ I vatOut urnOut).toNat := by
  unfold endSkimWadWord
  by_cases hle :
      (endFreeUrnInkWord urnOut).toNat ≤ (endSkimOweWord σ I vatOut urnOut).toNat
  · simp [hle]
  · simp [hle]

theorem endSkimStmtDiffSubReturns (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (vatOut urnOut : ByteArray) :
    ExecStmt config { contract := contract, locals := endSkimStoreWad σ I vatOut urnOut } evm
      (.internalCall "sub" [.var "owe", .var "wad"] "diff")
      (.ok { contract := contract, locals := endSkimStoreDiff σ I vatOut urnOut } evm) := by
  have howe :
      evalExpr? config { contract := contract, locals := endSkimStoreWad σ I vatOut urnOut }
        evm (.var "owe") =
          .ok (.int (Int.ofNat (endSkimOweWord σ I vatOut urnOut).toNat)) := by
    simpa [endSkimStoreWad, endSkimStoreOwe] using
      endEvalExpr_varUInt256 (evm := evm)
        (locals := endSkimStoreWad σ I vatOut urnOut)
        (name := "owe") (value := endSkimOweWord σ I vatOut urnOut)
        (by
          rw [endSkimStoreWad, store_get_ne _ _ (by native_decide),
            endSkimStoreOwe, store_get_self])
  have hwad :
      evalExpr? config { contract := contract, locals := endSkimStoreWad σ I vatOut urnOut }
        evm (.var "wad") =
          .ok (.int (Int.ofNat (endSkimWadWord σ I vatOut urnOut).toNat)) := by
    simpa [endSkimStoreWad] using
      endEvalExpr_varUInt256 (evm := evm)
        (locals := endSkimStoreWad σ I vatOut urnOut)
        (name := "wad") (value := endSkimWadWord σ I vatOut urnOut)
        (by simp [endSkimStoreWad])
  have hargs :
      evalExprs? config { contract := contract, locals := endSkimStoreWad σ I vatOut urnOut }
        evm [.var "owe", .var "wad"] =
          .ok [.int (Int.ofNat (endSkimOweWord σ I vatOut urnOut).toNat),
            .int (Int.ofNat (endSkimWadWord σ I vatOut urnOut).toNat)] := by
    simp [evalExprs?, howe, hwad, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? subFunction.params
          [.int (Int.ofNat (endSkimOweWord σ I vatOut urnOut).toNat),
            .int (Int.ofNat (endSkimWadWord σ I vatOut urnOut).toNat)] =
        some (endUintBinaryLocals (endSkimOweWord σ I vatOut urnOut)
          (endSkimWadWord σ I vatOut urnOut)) := by
    simp [subFunction, uint256, bindParams?, endUintBinaryLocals]
  have hbody :=
    endExecSubFunctionReturn (evm := evm)
      (x := endSkimOweWord σ I vatOut urnOut)
      (y := endSkimWadWord σ I vatOut urnOut)
      (diff := endSkimDiffWord σ I vatOut urnOut) rfl
      (endSkimWad_le_owe σ I vatOut urnOut)
  have hstmt := internalCallFunctionReturn
    (cfg := config)
    (caller := { contract := contract, locals := endSkimStoreWad σ I vatOut urnOut })
    (evm := evm) (name := "sub") (retVar := "diff")
    (args := [.var "owe", .var "wad"])
    (argVals :=
      [.int (Int.ofNat (endSkimOweWord σ I vatOut urnOut).toNat),
        .int (Int.ofNat (endSkimWadWord σ I vatOut urnOut).toNat)])
    (callee := subFunction)
    (locals := endUintBinaryLocals (endSkimOweWord σ I vatOut urnOut)
      (endSkimWadWord σ I vatOut urnOut))
    hargs (by rfl) hbind hbody
  simpa [endSkimStoreDiff, resumeAfterInternalCall, collapseReturns,
    endSkimDiffWord] using hstmt

theorem endSkimStmtGapNewAddReturns (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (vatOut urnOut : ByteArray)
    (hsz68 : 68 ≤ I.calldata.size)
    (hGapLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endSkimGapSlot I) =
        endSkimGapWord σ I)
    (hfit :
      (endSkimGapWord σ I).toNat + (endSkimDiffWord σ I vatOut urnOut).toNat <
        UInt256.size) :
    ExecStmt config { contract := contract, locals := endSkimStoreDiff σ I vatOut urnOut } evm
      (.internalCall "add" [.storage (gapRef (.var "ilk")), .var "diff"] "gapNew")
      (.ok { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut } evm) := by
  have hgap :
      evalExpr? config { contract := contract, locals := endSkimStoreDiff σ I vatOut urnOut }
        evm (.storage (gapRef (.var "ilk"))) =
          .ok (.int (Int.ofNat (endSkimGapWord σ I).toNat)) := by
    have hbase : (endSkimStoreDiff σ I vatOut urnOut).get? "gap" = none := by
      rw [endSkimStoreDiff, store_get_ne _ _ (by native_decide),
        endSkimStoreWad, store_get_ne _ _ (by native_decide),
        endSkimStoreOwe, store_get_ne _ _ (by native_decide),
        endSkimStoreOwe0, store_get_ne _ _ (by native_decide),
        endSkimStoreArt, store_get_ne _ _ (by native_decide),
        endSkimStoreInk, store_get_ne _ _ (by native_decide),
        endSkimStoreVatUrn, store_get_ne _ _ (by native_decide),
        endSkimStoreRate, store_get_ne _ _ (by native_decide),
        endSkimStoreVatIlk, store_get_ne _ _ (by native_decide),
        endSkimStore, store_get_ne _ _ (by native_decide),
        store_get_ne _ _ (by native_decide)]
      simp
    have hget :
        (endSkimStoreDiff σ I vatOut urnOut).get? "ilk" = some (endFlowIlkValue I) := by
      rw [endSkimStoreDiff, store_get_ne _ _ (by native_decide),
        endSkimStoreWad, store_get_ne _ _ (by native_decide),
        endSkimStoreOwe, store_get_ne _ _ (by native_decide),
        endSkimStoreOwe0, store_get_ne _ _ (by native_decide),
        endSkimStoreArt, store_get_ne _ _ (by native_decide),
        endSkimStoreInk, store_get_ne _ _ (by native_decide),
        endSkimStoreVatUrn, store_get_ne _ _ (by native_decide),
        endSkimStoreRate, store_get_ne _ _ (by native_decide),
        endSkimStoreVatIlk, store_get_ne _ _ (by native_decide),
        endSkimStore, store_get_ne _ _ (by native_decide), store_get_self]
    have hstorage := evalExpr_endFlow_gap_of_get evm I hbase hget (by omega)
    simpa [hGapLoad, endSkimGapWord, endFlowGapWord, endSkimGapSlot, endFlowGapSlot]
      using hstorage
  have hdiff :
      evalExpr? config { contract := contract, locals := endSkimStoreDiff σ I vatOut urnOut }
        evm (.var "diff") =
          .ok (.int (Int.ofNat (endSkimDiffWord σ I vatOut urnOut).toNat)) := by
    simpa [endSkimStoreDiff] using
      endEvalExpr_varUInt256 (evm := evm)
        (locals := endSkimStoreDiff σ I vatOut urnOut)
        (name := "diff") (value := endSkimDiffWord σ I vatOut urnOut)
        (by simp [endSkimStoreDiff])
  have hargs :
      evalExprs? config { contract := contract, locals := endSkimStoreDiff σ I vatOut urnOut }
        evm [.storage (gapRef (.var "ilk")), .var "diff"] =
          .ok [.int (Int.ofNat (endSkimGapWord σ I).toNat),
            .int (Int.ofNat (endSkimDiffWord σ I vatOut urnOut).toNat)] := by
    simp [evalExprs?, hgap, hdiff, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? addFunction.params
          [.int (Int.ofNat (endSkimGapWord σ I).toNat),
            .int (Int.ofNat (endSkimDiffWord σ I vatOut urnOut).toNat)] =
        some (endUintBinaryLocals (endSkimGapWord σ I)
          (endSkimDiffWord σ I vatOut urnOut)) := by
    simp [addFunction, uint256, bindParams?, endUintBinaryLocals]
  have hbody :=
    endExecAddFunctionReturn (evm := evm)
      (x := endSkimGapWord σ I) (y := endSkimDiffWord σ I vatOut urnOut)
      (sum := endSkimGapNewWord σ I vatOut urnOut) rfl hfit
  have hstmt := internalCallFunctionReturn
    (cfg := config)
    (caller := { contract := contract, locals := endSkimStoreDiff σ I vatOut urnOut })
    (evm := evm) (name := "add") (retVar := "gapNew")
    (args := [.storage (gapRef (.var "ilk")), .var "diff"])
    (argVals :=
      [.int (Int.ofNat (endSkimGapWord σ I).toNat),
        .int (Int.ofNat (endSkimDiffWord σ I vatOut urnOut).toNat)])
    (callee := addFunction)
    (locals := endUintBinaryLocals (endSkimGapWord σ I)
      (endSkimDiffWord σ I vatOut urnOut))
    hargs (by rfl) hbind hbody
  simpa [endSkimStoreGapNew, resumeAfterInternalCall, collapseReturns,
    endSkimGapNewWord] using hstmt

theorem endSkimStmtGapNewAddReverts (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (vatOut urnOut : ByteArray)
    (hsz68 : 68 ≤ I.calldata.size)
    (hGapLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endSkimGapSlot I) =
        endSkimGapWord σ I)
    (hover :
      UInt256.size ≤
        (endSkimGapWord σ I).toNat + (endSkimDiffWord σ I vatOut urnOut).toNat) :
    ExecStmt config { contract := contract, locals := endSkimStoreDiff σ I vatOut urnOut } evm
      (.internalCall "add" [.storage (gapRef (.var "ilk")), .var "diff"] "gapNew")
      .reverted := by
  have hgap :
      evalExpr? config { contract := contract, locals := endSkimStoreDiff σ I vatOut urnOut }
        evm (.storage (gapRef (.var "ilk"))) =
          .ok (.int (Int.ofNat (endSkimGapWord σ I).toNat)) := by
    have hbase : (endSkimStoreDiff σ I vatOut urnOut).get? "gap" = none := by
      rw [endSkimStoreDiff, store_get_ne _ _ (by native_decide),
        endSkimStoreWad, store_get_ne _ _ (by native_decide),
        endSkimStoreOwe, store_get_ne _ _ (by native_decide),
        endSkimStoreOwe0, store_get_ne _ _ (by native_decide),
        endSkimStoreArt, store_get_ne _ _ (by native_decide),
        endSkimStoreInk, store_get_ne _ _ (by native_decide),
        endSkimStoreVatUrn, store_get_ne _ _ (by native_decide),
        endSkimStoreRate, store_get_ne _ _ (by native_decide),
        endSkimStoreVatIlk, store_get_ne _ _ (by native_decide),
        endSkimStore, store_get_ne _ _ (by native_decide),
        store_get_ne _ _ (by native_decide)]
      simp
    have hget :
        (endSkimStoreDiff σ I vatOut urnOut).get? "ilk" = some (endFlowIlkValue I) := by
      rw [endSkimStoreDiff, store_get_ne _ _ (by native_decide),
        endSkimStoreWad, store_get_ne _ _ (by native_decide),
        endSkimStoreOwe, store_get_ne _ _ (by native_decide),
        endSkimStoreOwe0, store_get_ne _ _ (by native_decide),
        endSkimStoreArt, store_get_ne _ _ (by native_decide),
        endSkimStoreInk, store_get_ne _ _ (by native_decide),
        endSkimStoreVatUrn, store_get_ne _ _ (by native_decide),
        endSkimStoreRate, store_get_ne _ _ (by native_decide),
        endSkimStoreVatIlk, store_get_ne _ _ (by native_decide),
        endSkimStore, store_get_ne _ _ (by native_decide), store_get_self]
    have hstorage := evalExpr_endFlow_gap_of_get evm I hbase hget (by omega)
    simpa [hGapLoad, endSkimGapWord, endFlowGapWord, endSkimGapSlot, endFlowGapSlot]
      using hstorage
  have hdiff :
      evalExpr? config { contract := contract, locals := endSkimStoreDiff σ I vatOut urnOut }
        evm (.var "diff") =
          .ok (.int (Int.ofNat (endSkimDiffWord σ I vatOut urnOut).toNat)) := by
    simpa [endSkimStoreDiff] using
      endEvalExpr_varUInt256 (evm := evm)
        (locals := endSkimStoreDiff σ I vatOut urnOut)
        (name := "diff") (value := endSkimDiffWord σ I vatOut urnOut)
        (by simp [endSkimStoreDiff])
  have hargs :
      evalExprs? config { contract := contract, locals := endSkimStoreDiff σ I vatOut urnOut }
        evm [.storage (gapRef (.var "ilk")), .var "diff"] =
          .ok [.int (Int.ofNat (endSkimGapWord σ I).toNat),
            .int (Int.ofNat (endSkimDiffWord σ I vatOut urnOut).toNat)] := by
    simp [evalExprs?, hgap, hdiff, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? addFunction.params
          [.int (Int.ofNat (endSkimGapWord σ I).toNat),
            .int (Int.ofNat (endSkimDiffWord σ I vatOut urnOut).toNat)] =
        some (endUintBinaryLocals (endSkimGapWord σ I)
          (endSkimDiffWord σ I vatOut urnOut)) := by
    simp [addFunction, uint256, bindParams?, endUintBinaryLocals]
  have hbody :=
    endExecAddFunctionRevert (evm := evm)
      (x := endSkimGapWord σ I) (y := endSkimDiffWord σ I vatOut urnOut) hover
  exact internalCallFunctionRevert
    (cfg := config)
    (caller := { contract := contract, locals := endSkimStoreDiff σ I vatOut urnOut })
    (evm := evm) (name := "add") (retVar := "gapNew")
    (args := [.storage (gapRef (.var "ilk")), .var "diff"])
    (argVals :=
      [.int (Int.ofNat (endSkimGapWord σ I).toNat),
        .int (Int.ofNat (endSkimDiffWord σ I vatOut urnOut).toNat)])
    (callee := addFunction)
    (locals := endUintBinaryLocals (endSkimGapWord σ I)
      (endSkimDiffWord σ I vatOut urnOut))
    hargs (by rfl) hbind hbody

theorem endSkimAssignGap {locals : Store} (evm : EVM.State) (I : ExecutionEnv)
    (gapNew : UInt256)
    (hbase : locals.get? "gap" = none)
    (hget : locals.get? "ilk" = some (endFlowIlkValue I))
    (hsz68 : 68 ≤ I.calldata.size) :
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (gapRef (.var "ilk")) (.int (Int.ofNat gapNew.toNat)) =
        .ok ({ contract := contract, locals := locals }, endSkimPostGapState evm I gapNew) := by
  have href := evalStorageRef_endFlow_gap_of_get evm I hget (by omega)
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc (endSkimGapSlot I))
      (hbase := hbase)
      (her := by simpa [endSkimGapSlot, endFlowGapSlot] using href)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa only [endSkimPostGapState] using endStorageLocStore_uint256 evm (endSkimGapSlot I)
    gapNew

theorem endSkimStmtGapAssign (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (vatOut urnOut : ByteArray)
    (hsz68 : 68 ≤ I.calldata.size) :
    ExecStmt config { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
      evm (.assign .storage (gapRef (.var "ilk")) (.var "gapNew"))
      (.ok { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
        (endSkimPostGapState evm I (endSkimGapNewWord σ I vatOut urnOut))) := by
  have hgapNew :
      evalExpr? config { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
        evm (.var "gapNew") =
          .ok (.int (Int.ofNat (endSkimGapNewWord σ I vatOut urnOut).toNat)) := by
    simpa [endSkimStoreGapNew] using
      endEvalExpr_varUInt256 (evm := evm)
        (locals := endSkimStoreGapNew σ I vatOut urnOut)
        (name := "gapNew") (value := endSkimGapNewWord σ I vatOut urnOut)
        (by rw [endSkimStoreGapNew, store_get_self])
  have hassign :
      assignStorageRef? config
        { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
        evm .storage (gapRef (.var "ilk"))
        (.int (Int.ofNat (endSkimGapNewWord σ I vatOut urnOut).toNat)) =
          .ok ({ contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut },
            endSkimPostGapState evm I (endSkimGapNewWord σ I vatOut urnOut)) := by
    have hbase : (endSkimStoreGapNew σ I vatOut urnOut).get? "gap" = none := by
      rw [endSkimStoreGapNew, store_get_ne _ _ (by native_decide),
        endSkimStoreDiff, store_get_ne _ _ (by native_decide),
        endSkimStoreWad, store_get_ne _ _ (by native_decide),
        endSkimStoreOwe, store_get_ne _ _ (by native_decide),
        endSkimStoreOwe0, store_get_ne _ _ (by native_decide),
        endSkimStoreArt, store_get_ne _ _ (by native_decide),
        endSkimStoreInk, store_get_ne _ _ (by native_decide),
        endSkimStoreVatUrn, store_get_ne _ _ (by native_decide),
        endSkimStoreRate, store_get_ne _ _ (by native_decide),
        endSkimStoreVatIlk, store_get_ne _ _ (by native_decide),
        endSkimStore, store_get_ne _ _ (by native_decide),
        store_get_ne _ _ (by native_decide)]
      simp
    have hget :
        (endSkimStoreGapNew σ I vatOut urnOut).get? "ilk" = some (endFlowIlkValue I) := by
      rw [endSkimStoreGapNew, store_get_ne _ _ (by native_decide),
        endSkimStoreDiff, store_get_ne _ _ (by native_decide),
        endSkimStoreWad, store_get_ne _ _ (by native_decide),
        endSkimStoreOwe, store_get_ne _ _ (by native_decide),
        endSkimStoreOwe0, store_get_ne _ _ (by native_decide),
        endSkimStoreArt, store_get_ne _ _ (by native_decide),
        endSkimStoreInk, store_get_ne _ _ (by native_decide),
        endSkimStoreVatUrn, store_get_ne _ _ (by native_decide),
        endSkimStoreRate, store_get_ne _ _ (by native_decide),
        endSkimStoreVatIlk, store_get_ne _ _ (by native_decide),
        endSkimStore, store_get_ne _ _ (by native_decide), store_get_self]
    exact endSkimAssignGap evm I (endSkimGapNewWord σ I vatOut urnOut) hbase hget hsz68
  exact ExecStmt.assign hgapNew hassign

theorem evalExpr_endSkim_wad_afterGapNew (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (vatOut urnOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
      evm (.var "wad") =
        .ok (.int (Int.ofNat (endSkimWadWord σ I vatOut urnOut).toNat)) := by
  simpa [endSkimStoreGapNew, endSkimStoreDiff, endSkimStoreWad] using
    endEvalExpr_varUInt256 (evm := evm)
      (locals := endSkimStoreGapNew σ I vatOut urnOut)
      (name := "wad") (value := endSkimWadWord σ I vatOut urnOut)
      (by
        rw [endSkimStoreGapNew, store_get_ne _ _ (by native_decide),
          endSkimStoreDiff, store_get_ne _ _ (by native_decide),
          endSkimStoreWad, store_get_self])

theorem evalExpr_endSkim_art_afterGapNew (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (vatOut urnOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
      evm (.var "art") =
        .ok (.int (Int.ofNat (endFreeUrnArtWord urnOut).toNat)) := by
  simpa [endSkimStoreGapNew, endSkimStoreDiff, endSkimStoreWad, endSkimStoreOwe,
    endSkimStoreOwe0, endSkimStoreArt] using
    endEvalExpr_varUInt256 (evm := evm)
      (locals := endSkimStoreGapNew σ I vatOut urnOut)
      (name := "art") (value := endFreeUrnArtWord urnOut)
      (by
        rw [endSkimStoreGapNew, store_get_ne _ _ (by native_decide),
          endSkimStoreDiff, store_get_ne _ _ (by native_decide),
          endSkimStoreWad, store_get_ne _ _ (by native_decide),
          endSkimStoreOwe, store_get_ne _ _ (by native_decide),
          endSkimStoreOwe0, store_get_ne _ _ (by native_decide),
          endSkimStoreArt, store_get_self])

theorem evalExpr_endSkim_intLimit (evm : EVM.State) {locals : Store} :
    evalExpr? config { contract := contract, locals := locals } evm (.intLit int256Limit) =
      .ok (.int int256Limit) := by
  simp [evalExpr?, pure]

theorem endSkimEvalExpr_intGuard_true (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (vatOut urnOut : ByteArray)
    (hwad : (endSkimWadWord σ I vatOut urnOut).toNat ≤ 2 ^ 255)
    (hart : (endFreeUrnArtWord urnOut).toNat ≤ 2 ^ 255) :
    evalExpr? config { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
      evm
      (.binary .and
        (.binary .le (.var "wad") (.intLit int256Limit))
        (.binary .le (.var "art") (.intLit int256Limit)) ) = .ok (.bool true) := by
  have hlimit : int256Limit = Int.ofNat (2 ^ 255) := by native_decide
  have hwadExpr := evalExpr_endSkim_wad_afterGapNew evm I σ vatOut urnOut
  have hartExpr := evalExpr_endSkim_art_afterGapNew evm I σ vatOut urnOut
  have hlimitExpr :
      evalExpr? config
        { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut } evm
        (.intLit int256Limit) = .ok (.int int256Limit) :=
    evalExpr_endSkim_intLimit evm
  have hwadLe :
      evalExpr? config { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
        evm (.binary .le (.var "wad") (.intLit int256Limit)) = .ok (.bool true) :=
    endEvalExpr_le_int_true hwadExpr hlimitExpr (by
      rw [hlimit]
      exact Int.ofNat_le.mpr hwad)
  have hartLe :
      evalExpr? config { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
        evm (.binary .le (.var "art") (.intLit int256Limit)) = .ok (.bool true) :=
    endEvalExpr_le_int_true hartExpr hlimitExpr (by
      rw [hlimit]
      exact Int.ofNat_le.mpr hart)
  simp [evalExpr?, EvalResult.bind, bind, hwadLe, hartLe, pure]

theorem endSkimEvalExpr_intGuard_false_wad (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (vatOut urnOut : ByteArray)
    (hwad : 2 ^ 255 < (endSkimWadWord σ I vatOut urnOut).toNat) :
    evalExpr? config { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
      evm
      (.binary .and
        (.binary .le (.var "wad") (.intLit int256Limit))
        (.binary .le (.var "art") (.intLit int256Limit)) ) = .ok (.bool false) := by
  have hlimit : int256Limit = Int.ofNat (2 ^ 255) := by native_decide
  have hwadExpr := evalExpr_endSkim_wad_afterGapNew evm I σ vatOut urnOut
  have hlimitExpr :
      evalExpr? config
        { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut } evm
        (.intLit int256Limit) = .ok (.int int256Limit) :=
    evalExpr_endSkim_intLimit evm
  have hwadLe :
      evalExpr? config { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
        evm (.binary .le (.var "wad") (.intLit int256Limit)) = .ok (.bool false) :=
    endEvalExpr_le_int_false hwadExpr hlimitExpr (by
      rw [hlimit]
      exact Int.ofNat_lt.mpr hwad)
  simp [evalExpr?, EvalResult.bind, bind, hwadLe, pure]

theorem endSkimEvalExpr_intGuard_false_art (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (vatOut urnOut : ByteArray)
    (hwad : (endSkimWadWord σ I vatOut urnOut).toNat ≤ 2 ^ 255)
    (hart : 2 ^ 255 < (endFreeUrnArtWord urnOut).toNat) :
    evalExpr? config { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
      evm
      (.binary .and
        (.binary .le (.var "wad") (.intLit int256Limit))
        (.binary .le (.var "art") (.intLit int256Limit)) ) = .ok (.bool false) := by
  have hlimit : int256Limit = Int.ofNat (2 ^ 255) := by native_decide
  have hwadExpr := evalExpr_endSkim_wad_afterGapNew evm I σ vatOut urnOut
  have hartExpr := evalExpr_endSkim_art_afterGapNew evm I σ vatOut urnOut
  have hlimitExpr :
      evalExpr? config
        { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut } evm
        (.intLit int256Limit) = .ok (.int int256Limit) :=
    evalExpr_endSkim_intLimit evm
  have hwadLe :
      evalExpr? config { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
        evm (.binary .le (.var "wad") (.intLit int256Limit)) = .ok (.bool true) :=
    endEvalExpr_le_int_true hwadExpr hlimitExpr (by
      rw [hlimit]
      exact Int.ofNat_le.mpr hwad)
  have hartLe :
      evalExpr? config { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
        evm (.binary .le (.var "art") (.intLit int256Limit)) = .ok (.bool false) :=
    endEvalExpr_le_int_false hartExpr hlimitExpr (by
      rw [hlimit]
      exact Int.ofNat_lt.mpr hart)
  simp [evalExpr?, EvalResult.bind, bind, hwadLe, hartLe, pure]

theorem endSkimVatReceiver_afterGapNew {σ I vatOut urnOut evm}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    evalExpr? config { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
      evm (.storage vatRef) = .ok (.address (endPackVatAddr σ I)) := by
  have hbase : (endSkimStoreGapNew σ I vatOut urnOut).get? "vat" = none := by
    simp [endSkimStoreGapNew, endSkimStoreDiff, endSkimStoreWad, endSkimStoreOwe,
      endSkimStoreOwe0, endSkimStoreArt, endSkimStoreInk, endSkimStoreVatUrn,
      endSkimStoreRate, endSkimStoreVatIlk, endSkimStore]
  simpa [hmap, howner, Solm.EVM.storageLoad, State.lookupAccount,
    endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
    evalExpr_endPack_vat (locals := endSkimStoreGapNew σ I vatOut urnOut) evm hbase

theorem evalExpr_endSkim_negWad_afterGapNew (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (vatOut urnOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
      evm (.unary .neg (asInt256 (.var "wad"))) =
        .ok (.int (-(Int.ofNat (endSkimWadWord σ I vatOut urnOut).toNat))) := by
  have hwad := evalExpr_endSkim_wad_afterGapNew evm I σ vatOut urnOut
  simp only [asInt256, evalExpr?, hwad, castValue?, evalUnaryOp?, EvalResult.bind, bind,
    int256St, int256Int]
  rfl

theorem evalExpr_endSkim_negArt_afterGapNew (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (vatOut urnOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
      evm (.unary .neg (asInt256 (.var "art"))) =
        .ok (.int (-(Int.ofNat (endFreeUrnArtWord urnOut).toNat))) := by
  have hart := evalExpr_endSkim_art_afterGapNew evm I σ vatOut urnOut
  simp only [asInt256, evalExpr?, hart, castValue?, evalUnaryOp?, EvalResult.bind, bind,
    int256St, int256Int]
  rfl

theorem evalExprs_endSkim_grabArgs (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (vatOut urnOut : ByteArray)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    evalExprs? config { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
      evm
      [.var "ilk", .var "urn", thisAddr, vowAddr,
        .unary .neg (asInt256 (.var "wad")),
        .unary .neg (asInt256 (.var "art"))] =
        .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I),
          .address (endSkimUrnAddr I),
          .address I.codeOwner,
          .address (endPackVowAddr evm.accountMap I),
          .int (-(Int.ofNat (endSkimWadWord σ I vatOut urnOut).toNat)),
          .int (-(Int.ofNat (endFreeUrnArtWord urnOut).toNat))] := by
  have hilk :
      evalExpr? config { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
        evm (.var "ilk") =
          .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((endSkimStoreGapNew σ I vatOut urnOut).get? "ilk") =
        .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I))
    rw [endSkimStoreGapNew, store_get_ne _ _ (by native_decide),
      endSkimStoreDiff, store_get_ne _ _ (by native_decide),
      endSkimStoreWad, store_get_ne _ _ (by native_decide),
      endSkimStoreOwe, store_get_ne _ _ (by native_decide),
      endSkimStoreOwe0, store_get_ne _ _ (by native_decide),
      endSkimStoreArt, store_get_ne _ _ (by native_decide),
      endSkimStoreInk, store_get_ne _ _ (by native_decide),
      endSkimStoreVatUrn, store_get_ne _ _ (by native_decide),
      endSkimStoreRate, store_get_ne _ _ (by native_decide),
      endSkimStoreVatIlk, store_get_ne _ _ (by native_decide),
      endSkimStore_get_ilk]
    rfl
  have hurn :
      evalExpr? config { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
        evm (.var "urn") = .ok (.address (endSkimUrnAddr I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((endSkimStoreGapNew σ I vatOut urnOut).get? "urn") =
        .ok (.address (endSkimUrnAddr I))
    rw [endSkimStoreGapNew, store_get_ne _ _ (by native_decide),
      endSkimStoreDiff, store_get_ne _ _ (by native_decide),
      endSkimStoreWad, store_get_ne _ _ (by native_decide),
      endSkimStoreOwe, store_get_ne _ _ (by native_decide),
      endSkimStoreOwe0, store_get_ne _ _ (by native_decide),
      endSkimStoreArt, store_get_ne _ _ (by native_decide),
      endSkimStoreInk, store_get_ne _ _ (by native_decide),
      endSkimStoreVatUrn, store_get_ne _ _ (by native_decide),
      endSkimStoreRate, store_get_ne _ _ (by native_decide),
      endSkimStoreVatIlk, store_get_ne _ _ (by native_decide),
      endSkimStore, store_get_self]
    rfl
  have hthis :
      evalExpr? config { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
        evm thisAddr = .ok (.address I.codeOwner) := by
    simp [thisAddr, evalExpr?, envValue, howner, pure]
  have hvow :
      evalExpr? config { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
        evm vowAddr = .ok (.address (endPackVowAddr evm.accountMap I)) := by
    have hbase : (endSkimStoreGapNew σ I vatOut urnOut).get? "vow" = none := by
      simp [endSkimStoreGapNew, endSkimStoreDiff, endSkimStoreWad, endSkimStoreOwe,
        endSkimStoreOwe0, endSkimStoreArt, endSkimStoreInk, endSkimStoreVatUrn,
        endSkimStoreRate, endSkimStoreVatIlk, endSkimStore]
    simpa [vowAddr, howner, Solm.EVM.storageLoad, State.lookupAccount,
      endPackVowAddr, endPackVowWord, endSlotWord, solcSlotWord] using
      evalExpr_endPack_vow (locals := endSkimStoreGapNew σ I vatOut urnOut) evm hbase
  have hnegWad := evalExpr_endSkim_negWad_afterGapNew evm I σ vatOut urnOut
  have hnegArt := evalExpr_endSkim_negArt_afterGapNew evm I σ vatOut urnOut
  simp [evalExprs?, hilk, hurn, hthis, hvow, hnegWad, hnegArt,
    EvalResult.bind, bind, pure]

theorem endSkimGrabTailReverts_noCode {σ I} {vatOut urnOut : ByteArray}
    {evm : EVM.State}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) = ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
      evm
      (checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
        [.var "ilk", .var "urn", thisAddr, vowAddr,
          .unary .neg (asInt256 (.var "wad")),
          .unary .neg (asInt256 (.var "art"))]
        "_grab")
      .reverted := by
  have hreceiver := endSkimVatReceiver_afterGapNew
    (σ := σ) (I := I) (vatOut := vatOut) (urnOut := urnOut)
    (evm := evm) hmap howner
  have hcodeZero := endSkimVatCode_zero_afterRate
    (σ := σ) (I := I) (vatOut := vatOut) (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
        evm (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  simpa [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm)
      (locals := endSkimStoreGapNew σ I vatOut urnOut) (receiver := .storage vatRef)
      (retVar := "_grab") (name := "grab") (sendVal := 0)
      (args :=
        [.var "ilk", .var "urn", thisAddr, vowAddr,
          .unary .neg (asInt256 (.var "wad")),
          .unary .neg (asInt256 (.var "art"))])
      (perm := true) hguard

theorem endSkimGrabTailReverts_callFailed {σ I} {vatOut urnOut grabOut : ByteArray}
    {evm evmGrab : EVM.State}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endPackVatAddr σ I)) "grab" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I),
          .address (endSkimUrnAddr I),
          .address I.codeOwner,
          .address (endPackVowAddr σ I),
          .int (-(Int.ofNat (endSkimWadWord σ I vatOut urnOut).toNat)),
          .int (-(Int.ofNat (endFreeUrnArtWord urnOut).toNat))]
        (false, evmGrab, grabOut) true) :
    ExecBlock config { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
      evm
      (checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
        [.var "ilk", .var "urn", thisAddr, vowAddr,
          .unary .neg (asInt256 (.var "wad")),
          .unary .neg (asInt256 (.var "art"))]
        "_grab")
      .reverted := by
  have hreceiver := endSkimVatReceiver_afterGapNew
    (σ := σ) (I := I) (vatOut := vatOut) (urnOut := urnOut)
    (evm := evm) hmap howner
  have hcodePos := endSkimVatCode_pos_afterRate
    (σ := σ) (I := I) (vatOut := vatOut) (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
        evm (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargsRaw := evalExprs_endSkim_grabArgs evm I σ vatOut urnOut howner
  have hargs :
      evalExprs? config { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
        evm
        [.var "ilk", .var "urn", thisAddr, vowAddr,
          .unary .neg (asInt256 (.var "wad")),
          .unary .neg (asInt256 (.var "art"))] =
          .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I),
            .address (endSkimUrnAddr I),
            .address I.codeOwner,
            .address (endPackVowAddr σ I),
            .int (-(Int.ofNat (endSkimWadWord σ I vatOut urnOut).toNat)),
            .int (-(Int.ofNat (endFreeUrnArtWord urnOut).toNat))] := by
    simpa [hmap] using hargsRaw
  simpa [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config) (C := contract) (evm := evm) (evm' := evmGrab)
      (locals := endSkimStoreGapNew σ I vatOut urnOut) (receiver := .storage vatRef)
      (retVar := "_grab") (name := "grab") (target := endPackVatAddr σ I)
      (sendVal := 0)
      (args :=
        [.var "ilk", .var "urn", thisAddr, vowAddr,
          .unary .neg (asInt256 (.var "wad")),
          .unary .neg (asInt256 (.var "art"))])
      (argVals :=
        [.fixedBytes bytes32Width (endBytes32ArgBytes I),
          .address (endSkimUrnAddr I),
          .address I.codeOwner,
          .address (endPackVowAddr σ I),
          .int (-(Int.ofNat (endSkimWadWord σ I vatOut urnOut).toNat)),
          .int (-(Int.ofNat (endFreeUrnArtWord urnOut).toNat))])
      (out := grabOut) (perm := true) hguard hreceiver hargs hcall

theorem endSkimGrabTailReturns_success {σ I} {vatOut urnOut grabOut : ByteArray}
    {evm evmGrab : EVM.State}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endPackVatAddr σ I)) "grab" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I),
          .address (endSkimUrnAddr I),
          .address I.codeOwner,
          .address (endPackVowAddr σ I),
          .int (-(Int.ofNat (endSkimWadWord σ I vatOut urnOut).toNat)),
          .int (-(Int.ofNat (endFreeUrnArtWord urnOut).toNat))]
        (true, evmGrab, grabOut) true) :
    ExecBlock config { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
      evm
      (checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
        [.var "ilk", .var "urn", thisAddr, vowAddr,
          .unary .neg (asInt256 (.var "wad")),
          .unary .neg (asInt256 (.var "art"))]
        "_grab")
      (.ok { contract := contract, locals := endSkimStoreGrab σ I vatOut urnOut }
        evmGrab) := by
  have hreceiver := endSkimVatReceiver_afterGapNew
    (σ := σ) (I := I) (vatOut := vatOut) (urnOut := urnOut)
    (evm := evm) hmap howner
  have hcodePos := endSkimVatCode_pos_afterRate
    (σ := σ) (I := I) (vatOut := vatOut) (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
        evm (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargsRaw := evalExprs_endSkim_grabArgs evm I σ vatOut urnOut howner
  have hargs :
      evalExprs? config { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
        evm
        [.var "ilk", .var "urn", thisAddr, vowAddr,
          .unary .neg (asInt256 (.var "wad")),
          .unary .neg (asInt256 (.var "art"))] =
          .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I),
            .address (endSkimUrnAddr I),
            .address I.codeOwner,
            .address (endPackVowAddr σ I),
            .int (-(Int.ofNat (endSkimWadWord σ I vatOut urnOut).toNat)),
            .int (-(Int.ofNat (endFreeUrnArtWord urnOut).toNat))] := by
    simpa [hmap] using hargsRaw
  have hdec : config.externalABI.decode? "grab" grabOut = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hblock := checkedExternalCallSuccess
    (cfg := config) (C := contract) (evm := evm) (evm' := evmGrab)
    (locals := endSkimStoreGapNew σ I vatOut urnOut) (receiver := .storage vatRef)
    (retVar := "_grab") (name := "grab") (target := endPackVatAddr σ I)
    (sendVal := 0)
    (args :=
      [.var "ilk", .var "urn", thisAddr, vowAddr,
        .unary .neg (asInt256 (.var "wad")),
        .unary .neg (asInt256 (.var "art"))])
    (argVals :=
      [.fixedBytes bytes32Width (endBytes32ArgBytes I),
        .address (endSkimUrnAddr I),
        .address I.codeOwner,
        .address (endPackVowAddr σ I),
        .int (-(Int.ofNat (endSkimWadWord σ I vatOut urnOut).toNat)),
        .int (-(Int.ofNat (endFreeUrnArtWord urnOut).toNat))])
    (out := grabOut) (perm := true) (value := [])
    hguard hreceiver hargs hcall hdec
  simpa [checkedExternalCallStmts, endSkimStoreGrab, collapseReturns] using hblock

theorem endSkimVatReceiver_afterGapNewFor {σCall σLoc I vatOut urnOut evm}
    (hmap : evm.accountMap = σCall)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    evalExpr? config { contract := contract, locals := endSkimStoreGapNew σLoc I vatOut urnOut }
      evm (.storage vatRef) = .ok (.address (endPackVatAddr σCall I)) := by
  have hbase : (endSkimStoreGapNew σLoc I vatOut urnOut).get? "vat" = none := by
    simp [endSkimStoreGapNew, endSkimStoreDiff, endSkimStoreWad, endSkimStoreOwe,
      endSkimStoreOwe0, endSkimStoreArt, endSkimStoreInk, endSkimStoreVatUrn,
      endSkimStoreRate, endSkimStoreVatIlk, endSkimStore]
  simpa [hmap, howner, Solm.EVM.storageLoad, State.lookupAccount,
    endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
    evalExpr_endPack_vat (locals := endSkimStoreGapNew σLoc I vatOut urnOut) evm hbase

theorem endSkimGrabTailReverts_noCodeFor {σCall σLoc I} {vatOut urnOut : ByteArray}
    {evm : EVM.State}
    (hmap : evm.accountMap = σCall) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σCall (endPackVatWord σCall I) = ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endSkimStoreGapNew σLoc I vatOut urnOut }
      evm
      (checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
        [.var "ilk", .var "urn", thisAddr, vowAddr,
          .unary .neg (asInt256 (.var "wad")),
          .unary .neg (asInt256 (.var "art"))]
        "_grab")
      .reverted := by
  have hreceiver := endSkimVatReceiver_afterGapNewFor
    (σCall := σCall) (σLoc := σLoc) (I := I) (vatOut := vatOut) (urnOut := urnOut)
    (evm := evm) hmap howner
  have hcodeZero := endSkimVatCode_zero_afterRate
    (σ := σCall) (I := I) (vatOut := vatOut) (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSkimStoreGapNew σLoc I vatOut urnOut }
        evm (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  simpa [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm)
      (locals := endSkimStoreGapNew σLoc I vatOut urnOut) (receiver := .storage vatRef)
      (retVar := "_grab") (name := "grab") (sendVal := 0)
      (args :=
        [.var "ilk", .var "urn", thisAddr, vowAddr,
          .unary .neg (asInt256 (.var "wad")),
          .unary .neg (asInt256 (.var "art"))])
      (perm := true) hguard

theorem endSkimGrabTailReverts_callFailedFor {σCall σLoc I}
    {vatOut urnOut grabOut : ByteArray} {evm evmGrab : EVM.State}
    (hmap : evm.accountMap = σCall) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σCall (endPackVatWord σCall I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endPackVatAddr σCall I)) "grab" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I),
          .address (endSkimUrnAddr I),
          .address I.codeOwner,
          .address (endPackVowAddr σCall I),
          .int (-(Int.ofNat (endSkimWadWord σLoc I vatOut urnOut).toNat)),
          .int (-(Int.ofNat (endFreeUrnArtWord urnOut).toNat))]
        (false, evmGrab, grabOut) true) :
    ExecBlock config { contract := contract, locals := endSkimStoreGapNew σLoc I vatOut urnOut }
      evm
      (checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
        [.var "ilk", .var "urn", thisAddr, vowAddr,
          .unary .neg (asInt256 (.var "wad")),
          .unary .neg (asInt256 (.var "art"))]
        "_grab")
      .reverted := by
  have hreceiver := endSkimVatReceiver_afterGapNewFor
    (σCall := σCall) (σLoc := σLoc) (I := I) (vatOut := vatOut) (urnOut := urnOut)
    (evm := evm) hmap howner
  have hcodePos := endSkimVatCode_pos_afterRate
    (σ := σCall) (I := I) (vatOut := vatOut) (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSkimStoreGapNew σLoc I vatOut urnOut }
        evm (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargsRaw := evalExprs_endSkim_grabArgs evm I σLoc vatOut urnOut howner
  have hargs :
      evalExprs? config { contract := contract, locals := endSkimStoreGapNew σLoc I vatOut urnOut }
        evm
        [.var "ilk", .var "urn", thisAddr, vowAddr,
          .unary .neg (asInt256 (.var "wad")),
          .unary .neg (asInt256 (.var "art"))] =
          .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I),
            .address (endSkimUrnAddr I),
            .address I.codeOwner,
            .address (endPackVowAddr σCall I),
            .int (-(Int.ofNat (endSkimWadWord σLoc I vatOut urnOut).toNat)),
            .int (-(Int.ofNat (endFreeUrnArtWord urnOut).toNat))] := by
    simpa [hmap] using hargsRaw
  simpa [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config) (C := contract) (evm := evm) (evm' := evmGrab)
      (locals := endSkimStoreGapNew σLoc I vatOut urnOut) (receiver := .storage vatRef)
      (retVar := "_grab") (name := "grab") (target := endPackVatAddr σCall I)
      (sendVal := 0)
      (args :=
        [.var "ilk", .var "urn", thisAddr, vowAddr,
          .unary .neg (asInt256 (.var "wad")),
          .unary .neg (asInt256 (.var "art"))])
      (argVals :=
        [.fixedBytes bytes32Width (endBytes32ArgBytes I),
          .address (endSkimUrnAddr I),
          .address I.codeOwner,
          .address (endPackVowAddr σCall I),
          .int (-(Int.ofNat (endSkimWadWord σLoc I vatOut urnOut).toNat)),
          .int (-(Int.ofNat (endFreeUrnArtWord urnOut).toNat))])
      (out := grabOut) (perm := true) hguard hreceiver hargs hcall

theorem endSkimGrabTailReturns_successFor {σCall σLoc I}
    {vatOut urnOut grabOut : ByteArray} {evm evmGrab : EVM.State}
    (hmap : evm.accountMap = σCall) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σCall (endPackVatWord σCall I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endPackVatAddr σCall I)) "grab" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I),
          .address (endSkimUrnAddr I),
          .address I.codeOwner,
          .address (endPackVowAddr σCall I),
          .int (-(Int.ofNat (endSkimWadWord σLoc I vatOut urnOut).toNat)),
          .int (-(Int.ofNat (endFreeUrnArtWord urnOut).toNat))]
        (true, evmGrab, grabOut) true) :
    ExecBlock config { contract := contract, locals := endSkimStoreGapNew σLoc I vatOut urnOut }
      evm
      (checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
        [.var "ilk", .var "urn", thisAddr, vowAddr,
          .unary .neg (asInt256 (.var "wad")),
          .unary .neg (asInt256 (.var "art"))]
        "_grab")
      (.ok { contract := contract, locals := endSkimStoreGrab σLoc I vatOut urnOut }
        evmGrab) := by
  have hreceiver := endSkimVatReceiver_afterGapNewFor
    (σCall := σCall) (σLoc := σLoc) (I := I) (vatOut := vatOut) (urnOut := urnOut)
    (evm := evm) hmap howner
  have hcodePos := endSkimVatCode_pos_afterRate
    (σ := σCall) (I := I) (vatOut := vatOut) (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSkimStoreGapNew σLoc I vatOut urnOut }
        evm (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargsRaw := evalExprs_endSkim_grabArgs evm I σLoc vatOut urnOut howner
  have hargs :
      evalExprs? config { contract := contract, locals := endSkimStoreGapNew σLoc I vatOut urnOut }
        evm
        [.var "ilk", .var "urn", thisAddr, vowAddr,
          .unary .neg (asInt256 (.var "wad")),
          .unary .neg (asInt256 (.var "art"))] =
          .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I),
            .address (endSkimUrnAddr I),
            .address I.codeOwner,
            .address (endPackVowAddr σCall I),
            .int (-(Int.ofNat (endSkimWadWord σLoc I vatOut urnOut).toNat)),
            .int (-(Int.ofNat (endFreeUrnArtWord urnOut).toNat))] := by
    simpa [hmap] using hargsRaw
  have hdec : config.externalABI.decode? "grab" grabOut = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hblock := checkedExternalCallSuccess
    (cfg := config) (C := contract) (evm := evm) (evm' := evmGrab)
    (locals := endSkimStoreGapNew σLoc I vatOut urnOut) (receiver := .storage vatRef)
    (retVar := "_grab") (name := "grab") (target := endPackVatAddr σCall I)
    (sendVal := 0)
    (args :=
      [.var "ilk", .var "urn", thisAddr, vowAddr,
        .unary .neg (asInt256 (.var "wad")),
        .unary .neg (asInt256 (.var "art"))])
    (argVals :=
      [.fixedBytes bytes32Width (endBytes32ArgBytes I),
        .address (endSkimUrnAddr I),
        .address I.codeOwner,
        .address (endPackVowAddr σCall I),
        .int (-(Int.ofNat (endSkimWadWord σLoc I vatOut urnOut).toNat)),
        .int (-(Int.ofNat (endFreeUrnArtWord urnOut).toNat))])
    (out := grabOut) (perm := true) (value := [])
    hguard hreceiver hargs hcall hdec
  simpa [checkedExternalCallStmts, endSkimStoreGrab, collapseReturns] using hblock

theorem endSkimTailAfterArtReturns (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (vatOut urnOut : ByteArray)
    (hsz68 : 68 ≤ I.calldata.size)
    (hTagLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endSkimTagSlot I) =
        endSkimTagWord σ I)
    (hGapLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endSkimGapSlot I) =
        endSkimGapWord σ I)
    (hfitOwe0 :
      (endFreeUrnArtWord urnOut).toNat * (endFlowVatIlkRateWord vatOut).toNat <
        UInt256.size)
    (hfitOwe :
      (endSkimOwe0Word vatOut urnOut).toNat * (endSkimTagWord σ I).toNat <
        UInt256.size)
    (hfitGap :
      (endSkimGapWord σ I).toNat + (endSkimDiffWord σ I vatOut urnOut).toNat <
        UInt256.size)
    (hwadLimit : (endSkimWadWord σ I vatOut urnOut).toNat ≤ 2 ^ 255)
    (hartLimit : (endFreeUrnArtWord urnOut).toNat ≤ 2 ^ 255) :
    ExecBlock config { contract := contract, locals := endSkimStoreArt I vatOut urnOut } evm
      [ .internalCall "rmul" [.var "art", .var "rate"] "owe0",
        .internalCall "rmul" [.var "owe0", .storage (tagRef (.var "ilk"))] "owe",
        .internalCall "min" [.var "ink", .var "owe"] "wad",
        .internalCall "sub" [.var "owe", .var "wad"] "diff",
        .internalCall "add" [.storage (gapRef (.var "ilk")), .var "diff"] "gapNew",
        .assign .storage (gapRef (.var "ilk")) (.var "gapNew"),
        .require
          (.binary .and
            (.binary .le (.var "wad") (.intLit int256Limit))
            (.binary .le (.var "art") (.intLit int256Limit))) ]
      (.ok { contract := contract, locals := endSkimStoreGapNew σ I vatOut urnOut }
        (endSkimPostGapState evm I (endSkimGapNewWord σ I vatOut urnOut))) := by
  refine ExecBlock.consNormal (endSkimStmtOwe0RmulReturns evm I vatOut urnOut hfitOwe0) ?_
  refine ExecBlock.consNormal
    (endSkimStmtOweRmulReturns evm I σ vatOut urnOut hsz68 hTagLoad hfitOwe) ?_
  refine ExecBlock.consNormal (endSkimStmtWadMinReturns evm I σ vatOut urnOut) ?_
  refine ExecBlock.consNormal (endSkimStmtDiffSubReturns evm I σ vatOut urnOut) ?_
  refine ExecBlock.consNormal
    (endSkimStmtGapNewAddReturns evm I σ vatOut urnOut hsz68 hGapLoad hfitGap) ?_
  refine ExecBlock.consNormal (endSkimStmtGapAssign evm I σ vatOut urnOut hsz68) ?_
  exact ExecBlock.consNormal
    (ExecStmt.requireTrue
      (endSkimEvalExpr_intGuard_true
        (endSkimPostGapState evm I (endSkimGapNewWord σ I vatOut urnOut))
        I σ vatOut urnOut hwadLimit hartLimit))
    ExecBlock.nil

theorem endSkimTailReverts_owe0RmulOverflow (evm : EVM.State) (I : ExecutionEnv)
    (vatOut urnOut : ByteArray)
    (hover :
      UInt256.size ≤
        (endFreeUrnArtWord urnOut).toNat * (endFlowVatIlkRateWord vatOut).toNat) :
    ExecBlock config { contract := contract, locals := endSkimStoreArt I vatOut urnOut } evm
      [ .internalCall "rmul" [.var "art", .var "rate"] "owe0",
        .internalCall "rmul" [.var "owe0", .storage (tagRef (.var "ilk"))] "owe",
        .internalCall "min" [.var "ink", .var "owe"] "wad",
        .internalCall "sub" [.var "owe", .var "wad"] "diff",
        .internalCall "add" [.storage (gapRef (.var "ilk")), .var "diff"] "gapNew",
        .assign .storage (gapRef (.var "ilk")) (.var "gapNew"),
        .require
          (.binary .and
            (.binary .le (.var "wad") (.intLit int256Limit))
            (.binary .le (.var "art") (.intLit int256Limit))) ]
      .reverted := by
  exact ExecBlock.consRevert (endSkimStmtOwe0RmulReverts evm I vatOut urnOut hover)

theorem endSkimTailReverts_oweRmulOverflow (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (vatOut urnOut : ByteArray)
    (hsz68 : 68 ≤ I.calldata.size)
    (hTagLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endSkimTagSlot I) =
        endSkimTagWord σ I)
    (hfitOwe0 :
      (endFreeUrnArtWord urnOut).toNat * (endFlowVatIlkRateWord vatOut).toNat <
        UInt256.size)
    (hover :
      UInt256.size ≤ (endSkimOwe0Word vatOut urnOut).toNat * (endSkimTagWord σ I).toNat) :
    ExecBlock config { contract := contract, locals := endSkimStoreArt I vatOut urnOut } evm
      [ .internalCall "rmul" [.var "art", .var "rate"] "owe0",
        .internalCall "rmul" [.var "owe0", .storage (tagRef (.var "ilk"))] "owe",
        .internalCall "min" [.var "ink", .var "owe"] "wad",
        .internalCall "sub" [.var "owe", .var "wad"] "diff",
        .internalCall "add" [.storage (gapRef (.var "ilk")), .var "diff"] "gapNew",
        .assign .storage (gapRef (.var "ilk")) (.var "gapNew"),
        .require
          (.binary .and
            (.binary .le (.var "wad") (.intLit int256Limit))
            (.binary .le (.var "art") (.intLit int256Limit))) ]
      .reverted := by
  refine ExecBlock.consNormal (endSkimStmtOwe0RmulReturns evm I vatOut urnOut hfitOwe0) ?_
  exact ExecBlock.consRevert
    (endSkimStmtOweRmulReverts evm I σ vatOut urnOut hsz68 hTagLoad hover)

theorem endSkimTailReverts_gapAddOverflow (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (vatOut urnOut : ByteArray)
    (hsz68 : 68 ≤ I.calldata.size)
    (hTagLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endSkimTagSlot I) =
        endSkimTagWord σ I)
    (hGapLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endSkimGapSlot I) =
        endSkimGapWord σ I)
    (hfitOwe0 :
      (endFreeUrnArtWord urnOut).toNat * (endFlowVatIlkRateWord vatOut).toNat <
        UInt256.size)
    (hfitOwe :
      (endSkimOwe0Word vatOut urnOut).toNat * (endSkimTagWord σ I).toNat <
        UInt256.size)
    (hover :
      UInt256.size ≤
        (endSkimGapWord σ I).toNat + (endSkimDiffWord σ I vatOut urnOut).toNat) :
    ExecBlock config { contract := contract, locals := endSkimStoreArt I vatOut urnOut } evm
      [ .internalCall "rmul" [.var "art", .var "rate"] "owe0",
        .internalCall "rmul" [.var "owe0", .storage (tagRef (.var "ilk"))] "owe",
        .internalCall "min" [.var "ink", .var "owe"] "wad",
        .internalCall "sub" [.var "owe", .var "wad"] "diff",
        .internalCall "add" [.storage (gapRef (.var "ilk")), .var "diff"] "gapNew",
        .assign .storage (gapRef (.var "ilk")) (.var "gapNew"),
        .require
          (.binary .and
            (.binary .le (.var "wad") (.intLit int256Limit))
            (.binary .le (.var "art") (.intLit int256Limit))) ]
      .reverted := by
  refine ExecBlock.consNormal (endSkimStmtOwe0RmulReturns evm I vatOut urnOut hfitOwe0) ?_
  refine ExecBlock.consNormal
    (endSkimStmtOweRmulReturns evm I σ vatOut urnOut hsz68 hTagLoad hfitOwe) ?_
  refine ExecBlock.consNormal (endSkimStmtWadMinReturns evm I σ vatOut urnOut) ?_
  refine ExecBlock.consNormal (endSkimStmtDiffSubReturns evm I σ vatOut urnOut) ?_
  exact ExecBlock.consRevert
    (endSkimStmtGapNewAddReverts evm I σ vatOut urnOut hsz68 hGapLoad hover)

theorem endSkimTailReverts_intGuardWad (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (vatOut urnOut : ByteArray)
    (hsz68 : 68 ≤ I.calldata.size)
    (hTagLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endSkimTagSlot I) =
        endSkimTagWord σ I)
    (hGapLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endSkimGapSlot I) =
        endSkimGapWord σ I)
    (hfitOwe0 :
      (endFreeUrnArtWord urnOut).toNat * (endFlowVatIlkRateWord vatOut).toNat <
        UInt256.size)
    (hfitOwe :
      (endSkimOwe0Word vatOut urnOut).toNat * (endSkimTagWord σ I).toNat <
        UInt256.size)
    (hfitGap :
      (endSkimGapWord σ I).toNat + (endSkimDiffWord σ I vatOut urnOut).toNat <
        UInt256.size)
    (hwad : 2 ^ 255 < (endSkimWadWord σ I vatOut urnOut).toNat) :
    ExecBlock config { contract := contract, locals := endSkimStoreArt I vatOut urnOut } evm
      [ .internalCall "rmul" [.var "art", .var "rate"] "owe0",
        .internalCall "rmul" [.var "owe0", .storage (tagRef (.var "ilk"))] "owe",
        .internalCall "min" [.var "ink", .var "owe"] "wad",
        .internalCall "sub" [.var "owe", .var "wad"] "diff",
        .internalCall "add" [.storage (gapRef (.var "ilk")), .var "diff"] "gapNew",
        .assign .storage (gapRef (.var "ilk")) (.var "gapNew"),
        .require
          (.binary .and
            (.binary .le (.var "wad") (.intLit int256Limit))
            (.binary .le (.var "art") (.intLit int256Limit))) ]
      .reverted := by
  refine ExecBlock.consNormal (endSkimStmtOwe0RmulReturns evm I vatOut urnOut hfitOwe0) ?_
  refine ExecBlock.consNormal
    (endSkimStmtOweRmulReturns evm I σ vatOut urnOut hsz68 hTagLoad hfitOwe) ?_
  refine ExecBlock.consNormal (endSkimStmtWadMinReturns evm I σ vatOut urnOut) ?_
  refine ExecBlock.consNormal (endSkimStmtDiffSubReturns evm I σ vatOut urnOut) ?_
  refine ExecBlock.consNormal
    (endSkimStmtGapNewAddReturns evm I σ vatOut urnOut hsz68 hGapLoad hfitGap) ?_
  refine ExecBlock.consNormal (endSkimStmtGapAssign evm I σ vatOut urnOut hsz68) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (endSkimEvalExpr_intGuard_false_wad
        (endSkimPostGapState evm I (endSkimGapNewWord σ I vatOut urnOut))
        I σ vatOut urnOut hwad))

theorem endSkimTailReverts_intGuardArt (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (vatOut urnOut : ByteArray)
    (hsz68 : 68 ≤ I.calldata.size)
    (hTagLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endSkimTagSlot I) =
        endSkimTagWord σ I)
    (hGapLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endSkimGapSlot I) =
        endSkimGapWord σ I)
    (hfitOwe0 :
      (endFreeUrnArtWord urnOut).toNat * (endFlowVatIlkRateWord vatOut).toNat <
        UInt256.size)
    (hfitOwe :
      (endSkimOwe0Word vatOut urnOut).toNat * (endSkimTagWord σ I).toNat <
        UInt256.size)
    (hfitGap :
      (endSkimGapWord σ I).toNat + (endSkimDiffWord σ I vatOut urnOut).toNat <
        UInt256.size)
    (hwad : (endSkimWadWord σ I vatOut urnOut).toNat ≤ 2 ^ 255)
    (hart : 2 ^ 255 < (endFreeUrnArtWord urnOut).toNat) :
    ExecBlock config { contract := contract, locals := endSkimStoreArt I vatOut urnOut } evm
      [ .internalCall "rmul" [.var "art", .var "rate"] "owe0",
        .internalCall "rmul" [.var "owe0", .storage (tagRef (.var "ilk"))] "owe",
        .internalCall "min" [.var "ink", .var "owe"] "wad",
        .internalCall "sub" [.var "owe", .var "wad"] "diff",
        .internalCall "add" [.storage (gapRef (.var "ilk")), .var "diff"] "gapNew",
        .assign .storage (gapRef (.var "ilk")) (.var "gapNew"),
        .require
          (.binary .and
            (.binary .le (.var "wad") (.intLit int256Limit))
            (.binary .le (.var "art") (.intLit int256Limit))) ]
      .reverted := by
  refine ExecBlock.consNormal (endSkimStmtOwe0RmulReturns evm I vatOut urnOut hfitOwe0) ?_
  refine ExecBlock.consNormal
    (endSkimStmtOweRmulReturns evm I σ vatOut urnOut hsz68 hTagLoad hfitOwe) ?_
  refine ExecBlock.consNormal (endSkimStmtWadMinReturns evm I σ vatOut urnOut) ?_
  refine ExecBlock.consNormal (endSkimStmtDiffSubReturns evm I σ vatOut urnOut) ?_
  refine ExecBlock.consNormal
    (endSkimStmtGapNewAddReturns evm I σ vatOut urnOut hsz68 hGapLoad hfitGap) ?_
  refine ExecBlock.consNormal (endSkimStmtGapAssign evm I σ vatOut urnOut hsz68) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (endSkimEvalExpr_intGuard_false_art
        (endSkimPostGapState evm I (endSkimGapNewWord σ I vatOut urnOut))
        I σ vatOut urnOut hwad hart))

theorem endSkimBodyReverts_afterArtTailReverted {I} {vatOut urnOut : ByteArray}
    {evm0 evmArt : EVM.State}
    (hprefixArt :
      ExecBlock config { contract := contract, locals := endSkimStore I } evm0
        (nonpayable ++
          [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
          checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
            "vatIlk" ++
          [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
          checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0)
            [.var "ilk", .var "urn"] "vatUrn" ++
          [ .letDecl "ink" (some uint256) (.tupleGet (.var "vatUrn") 0),
            .letDecl "art" (some uint256) (.tupleGet (.var "vatUrn") 1) ])
        (.ok { contract := contract, locals := endSkimStoreArt I vatOut urnOut } evmArt))
    (htail :
      ExecBlock config { contract := contract, locals := endSkimStoreArt I vatOut urnOut } evmArt
        [ .internalCall "rmul" [.var "art", .var "rate"] "owe0",
          .internalCall "rmul" [.var "owe0", .storage (tagRef (.var "ilk"))] "owe",
          .internalCall "min" [.var "ink", .var "owe"] "wad",
          .internalCall "sub" [.var "owe", .var "wad"] "diff",
          .internalCall "add" [.storage (gapRef (.var "ilk")), .var "diff"] "gapNew",
          .assign .storage (gapRef (.var "ilk")) (.var "gapNew"),
          .require
            (.binary .and
              (.binary .le (.var "wad") (.intLit int256Limit))
              (.binary .le (.var "art") (.intLit int256Limit))) ]
        .reverted) :
    ExecTransitionBody config contract evm0 (endSkimStore I) skimTransition.body .reverted := by
  let grabTail :=
    checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
      [.var "ilk", .var "urn", thisAddr, vowAddr,
       .unary .neg (asInt256 (.var "wad")), .unary .neg (asInt256 (.var "art"))]
      "_grab"
  have htailWithGrab :
      ExecBlock config { contract := contract, locals := endSkimStoreArt I vatOut urnOut } evmArt
        ([ .internalCall "rmul" [.var "art", .var "rate"] "owe0",
          .internalCall "rmul" [.var "owe0", .storage (tagRef (.var "ilk"))] "owe",
          .internalCall "min" [.var "ink", .var "owe"] "wad",
          .internalCall "sub" [.var "owe", .var "wad"] "diff",
          .internalCall "add" [.storage (gapRef (.var "ilk")), .var "diff"] "gapNew",
          .assign .storage (gapRef (.var "ilk")) (.var "gapNew"),
          .require
            (.binary .and
              (.binary .le (.var "wad") (.intLit int256Limit))
              (.binary .le (.var "art") (.intLit int256Limit))) ] ++ grabTail)
        .reverted := by
    exact Reasoning.Refinement.execBlock_append_term htail (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := endSkimStore I } evm0
        skimTransition.body .reverted := by
    have hseq := Reasoning.Refinement.execBlock_append hprefixArt htailWithGrab
    simpa [skimTransition, grabTail, List.append_assoc] using hseq
  exact ExecFuncBody.execBlockRevert hblock

theorem endSkimBodyReverts_afterArtTailGrabReverted {I σLoc}
    {vatOut urnOut : ByteArray} {evm0 evmArt evmPost : EVM.State}
    (hprefixArt :
      ExecBlock config { contract := contract, locals := endSkimStore I } evm0
        (nonpayable ++
          [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
          checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
            "vatIlk" ++
          [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
          checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0)
            [.var "ilk", .var "urn"] "vatUrn" ++
          [ .letDecl "ink" (some uint256) (.tupleGet (.var "vatUrn") 0),
            .letDecl "art" (some uint256) (.tupleGet (.var "vatUrn") 1) ])
        (.ok { contract := contract, locals := endSkimStoreArt I vatOut urnOut } evmArt))
    (htail :
      ExecBlock config { contract := contract, locals := endSkimStoreArt I vatOut urnOut } evmArt
        [ .internalCall "rmul" [.var "art", .var "rate"] "owe0",
          .internalCall "rmul" [.var "owe0", .storage (tagRef (.var "ilk"))] "owe",
          .internalCall "min" [.var "ink", .var "owe"] "wad",
          .internalCall "sub" [.var "owe", .var "wad"] "diff",
          .internalCall "add" [.storage (gapRef (.var "ilk")), .var "diff"] "gapNew",
          .assign .storage (gapRef (.var "ilk")) (.var "gapNew"),
          .require
            (.binary .and
              (.binary .le (.var "wad") (.intLit int256Limit))
              (.binary .le (.var "art") (.intLit int256Limit))) ]
        (.ok { contract := contract, locals := endSkimStoreGapNew σLoc I vatOut urnOut }
          evmPost))
    (hgrab :
      ExecBlock config
        { contract := contract, locals := endSkimStoreGapNew σLoc I vatOut urnOut }
        evmPost
        (checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
          [.var "ilk", .var "urn", thisAddr, vowAddr,
            .unary .neg (asInt256 (.var "wad")),
            .unary .neg (asInt256 (.var "art"))]
          "_grab")
        .reverted) :
    ExecTransitionBody config contract evm0 (endSkimStore I) skimTransition.body
      .reverted := by
  let grabTail :=
    checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
      [.var "ilk", .var "urn", thisAddr, vowAddr,
        .unary .neg (asInt256 (.var "wad")),
        .unary .neg (asInt256 (.var "art"))]
      "_grab"
  have htailWithGrab :
      ExecBlock config { contract := contract, locals := endSkimStoreArt I vatOut urnOut }
        evmArt
        ([ .internalCall "rmul" [.var "art", .var "rate"] "owe0",
          .internalCall "rmul" [.var "owe0", .storage (tagRef (.var "ilk"))] "owe",
          .internalCall "min" [.var "ink", .var "owe"] "wad",
          .internalCall "sub" [.var "owe", .var "wad"] "diff",
          .internalCall "add" [.storage (gapRef (.var "ilk")), .var "diff"] "gapNew",
          .assign .storage (gapRef (.var "ilk")) (.var "gapNew"),
          .require
            (.binary .and
              (.binary .le (.var "wad") (.intLit int256Limit))
              (.binary .le (.var "art") (.intLit int256Limit))) ] ++ grabTail)
        .reverted := by
    exact Reasoning.Refinement.execBlock_append htail hgrab
  have hblock :
      ExecBlock config { contract := contract, locals := endSkimStore I } evm0
        skimTransition.body .reverted := by
    have hseq := Reasoning.Refinement.execBlock_append hprefixArt htailWithGrab
    simpa [skimTransition, grabTail, List.append_assoc] using hseq
  exact ExecFuncBody.execBlockRevert hblock

theorem endSkimBodyReturns_afterArtTailGrabSuccess {I σLoc}
    {vatOut urnOut : ByteArray} {evm0 evmArt evmPost evmGrab : EVM.State}
    (hprefixArt :
      ExecBlock config { contract := contract, locals := endSkimStore I } evm0
        (nonpayable ++
          [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
          checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
            "vatIlk" ++
          [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
          checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0)
            [.var "ilk", .var "urn"] "vatUrn" ++
          [ .letDecl "ink" (some uint256) (.tupleGet (.var "vatUrn") 0),
            .letDecl "art" (some uint256) (.tupleGet (.var "vatUrn") 1) ])
        (.ok { contract := contract, locals := endSkimStoreArt I vatOut urnOut } evmArt))
    (htail :
      ExecBlock config { contract := contract, locals := endSkimStoreArt I vatOut urnOut } evmArt
        [ .internalCall "rmul" [.var "art", .var "rate"] "owe0",
          .internalCall "rmul" [.var "owe0", .storage (tagRef (.var "ilk"))] "owe",
          .internalCall "min" [.var "ink", .var "owe"] "wad",
          .internalCall "sub" [.var "owe", .var "wad"] "diff",
          .internalCall "add" [.storage (gapRef (.var "ilk")), .var "diff"] "gapNew",
          .assign .storage (gapRef (.var "ilk")) (.var "gapNew"),
          .require
            (.binary .and
              (.binary .le (.var "wad") (.intLit int256Limit))
              (.binary .le (.var "art") (.intLit int256Limit))) ]
        (.ok { contract := contract, locals := endSkimStoreGapNew σLoc I vatOut urnOut }
          evmPost))
    (hgrab :
      ExecBlock config
        { contract := contract, locals := endSkimStoreGapNew σLoc I vatOut urnOut }
        evmPost
        (checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
          [.var "ilk", .var "urn", thisAddr, vowAddr,
            .unary .neg (asInt256 (.var "wad")),
            .unary .neg (asInt256 (.var "art"))]
          "_grab")
        (.ok { contract := contract, locals := endSkimStoreGrab σLoc I vatOut urnOut }
          evmGrab)) :
    ExecTransitionBody config contract evm0 (endSkimStore I) skimTransition.body
      (.returned { contract := contract, locals := endSkimStoreGrab σLoc I vatOut urnOut }
        evmGrab none) := by
  let grabTail :=
    checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
      [.var "ilk", .var "urn", thisAddr, vowAddr,
        .unary .neg (asInt256 (.var "wad")),
        .unary .neg (asInt256 (.var "art"))]
      "_grab"
  have htailWithGrab :
      ExecBlock config { contract := contract, locals := endSkimStoreArt I vatOut urnOut }
        evmArt
        ([ .internalCall "rmul" [.var "art", .var "rate"] "owe0",
          .internalCall "rmul" [.var "owe0", .storage (tagRef (.var "ilk"))] "owe",
          .internalCall "min" [.var "ink", .var "owe"] "wad",
          .internalCall "sub" [.var "owe", .var "wad"] "diff",
          .internalCall "add" [.storage (gapRef (.var "ilk")), .var "diff"] "gapNew",
          .assign .storage (gapRef (.var "ilk")) (.var "gapNew"),
          .require
            (.binary .and
              (.binary .le (.var "wad") (.intLit int256Limit))
              (.binary .le (.var "art") (.intLit int256Limit))) ] ++ grabTail)
        (.ok { contract := contract, locals := endSkimStoreGrab σLoc I vatOut urnOut }
          evmGrab) := by
    exact Reasoning.Refinement.execBlock_append htail hgrab
  have hblock :
      ExecBlock config { contract := contract, locals := endSkimStore I } evm0
        skimTransition.body
        (.ok { contract := contract, locals := endSkimStoreGrab σLoc I vatOut urnOut }
          evmGrab) := by
    have hseq := Reasoning.Refinement.execBlock_append hprefixArt htailWithGrab
    simpa [skimTransition, grabTail, List.append_assoc] using hseq
  exact ExecFuncBody.execBlockOK hblock

theorem endSkimBodyReverts_vatIlksBlock {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSkimTagWord σ I ≠ ⟨0⟩)
    (hvatBlock :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      ExecBlock config { contract := contract, locals := endSkimStore I } evm0
        (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk") .reverted) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endSkimStore I) skimTransition.body .reverted := by
  intro evm0
  have htagLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (endSkimTagSlot I) ≠ ⟨0⟩ := by
    intro hbad
    apply htag
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endSkimTagWord, endSlotWord, solcSlotWord] using hbad
  have hguard :
      evalExpr? config { contract := contract, locals := endSkimStore I } evm0
        (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_endSkim_tag_ne_true evm0 I hsz68 htagLoad
  have hvat :
      ExecBlock config { contract := contract, locals := endSkimStore I } evm0
        (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk") .reverted := by
    simpa [evm0] using hvatBlock
  have hvatWithTail :
      ExecBlock config { contract := contract, locals := endSkimStore I } evm0
        (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk" ++
          [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
          checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0)
            [.var "ilk", .var "urn"] "vatUrn" ++
          [ .letDecl "ink" (some uint256) (.tupleGet (.var "vatUrn") 0),
            .letDecl "art" (some uint256) (.tupleGet (.var "vatUrn") 1),
            .internalCall "rmul" [.var "art", .var "rate"] "owe0",
            .internalCall "rmul" [.var "owe0", .storage (tagRef (.var "ilk"))] "owe",
            .internalCall "min" [.var "ink", .var "owe"] "wad",
            .internalCall "sub" [.var "owe", .var "wad"] "diff",
            .internalCall "add" [.storage (gapRef (.var "ilk")), .var "diff"] "gapNew",
            .assign .storage (gapRef (.var "ilk")) (.var "gapNew"),
            .require
              (.binary .and
              (.binary .le (.var "wad") (.intLit int256Limit))
              (.binary .le (.var "art") (.intLit int256Limit))) ] ++
          checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
            [.var "ilk", .var "urn", thisAddr, vowAddr,
             .unary .neg (asInt256 (.var "wad")), .unary .neg (asInt256 (.var "art"))]
            "_grab")
        .reverted := by
    exact Reasoning.Refinement.execBlock_append_term
      (s2 :=
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
        checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0)
          [.var "ilk", .var "urn"] "vatUrn" ++
        [ .letDecl "ink" (some uint256) (.tupleGet (.var "vatUrn") 0),
          .letDecl "art" (some uint256) (.tupleGet (.var "vatUrn") 1),
          .internalCall "rmul" [.var "art", .var "rate"] "owe0",
          .internalCall "rmul" [.var "owe0", .storage (tagRef (.var "ilk"))] "owe",
          .internalCall "min" [.var "ink", .var "owe"] "wad",
          .internalCall "sub" [.var "owe", .var "wad"] "diff",
          .internalCall "add" [.storage (gapRef (.var "ilk")), .var "diff"] "gapNew",
          .assign .storage (gapRef (.var "ilk")) (.var "gapNew"),
          .require
            (.binary .and
              (.binary .le (.var "wad") (.intLit int256Limit))
              (.binary .le (.var "art") (.intLit int256Limit))) ] ++
        checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
          [.var "ilk", .var "urn", thisAddr, vowAddr,
           .unary .neg (asInt256 (.var "wad")), .unary .neg (asInt256 (.var "art"))]
          "_grab")
      hvat (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := endSkimStore I } evm0
        skimTransition.body .reverted := by
    simp only [skimTransition, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    simpa [List.append_assoc] using hvatWithTail
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endSkimBodyReverts_vatIlksNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSkimTagWord σ I ≠ ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endSkimStore I) skimTransition.body .reverted := by
  intro evm0
  exact endSkimBodyReverts_vatIlksBlock
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) hwv hsz68 htag
    (by
      simpa using
        (endSkimCheckedVatIlksNoCode
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hcodeSize))

theorem endSkimBodyReverts_vatIlksCallFailed {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSkimTagWord σ I ≠ ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "vatIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (false, evmVat, out) true) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endSkimStore I) skimTransition.body .reverted := by
  intro evm0
  exact endSkimBodyReverts_vatIlksBlock
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) hwv hsz68 htag
    (by
      simpa using
        (endSkimCheckedVatIlksFailure
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) (evmVat := evmVat) (out := out)
          hcodeSize hcall))

theorem endSkimBodyReverts_vatIlksDecodeShort {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSkimTagWord σ I ≠ ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "vatIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmVat, out) true)
    (hshort : out.size < 160) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endSkimStore I) skimTransition.body .reverted := by
  intro evm0
  exact endSkimBodyReverts_vatIlksBlock
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) hwv hsz68 htag
    (by
      simpa using
        (endSkimCheckedVatIlksDecodeRevert
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) (evmVat := evmVat) (out := out)
          hcodeSize hcall hshort))

theorem endSkimPrefixRateSuccess {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSkimTagWord σ I ≠ ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "vatIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmVat, out) true)
    (hlo : 160 ≤ out.size) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := endSkimStore I } evm0
      (nonpayable ++
        [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
        checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk" ++
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ])
      (.ok { contract := contract, locals := endSkimStoreRate I out } evmVat) := by
  intro evm0
  have htagLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (endSkimTagSlot I) ≠ ⟨0⟩ := by
    intro hbad
    apply htag
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endSkimTagWord, endSlotWord, solcSlotWord] using hbad
  have hguard :
      evalExpr? config { contract := contract, locals := endSkimStore I } evm0
        (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_endSkim_tag_ne_true evm0 I hsz68 htagLoad
  have hvat :
      ExecBlock config { contract := contract, locals := endSkimStore I } evm0
        (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk")
        (.ok { contract := contract, locals := endSkimStoreVatIlk I out } evmVat) := by
    simpa [evm0] using
      endSkimCheckedVatIlksSuccess
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (evmVat := evmVat) (out := out)
        hcodeSize hcall hlo
  have hrate :
      ExecBlock config { contract := contract, locals := endSkimStoreVatIlk I out } evmVat
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ]
        (.ok { contract := contract, locals := endSkimStoreRate I out } evmVat) := by
    exact ExecBlock.consNormal (endSkimStmtRate evmVat I out) ExecBlock.nil
  have hvatRate :
      ExecBlock config { contract := contract, locals := endSkimStore I } evm0
        (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk" ++
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ])
        (.ok { contract := contract, locals := endSkimStoreRate I out } evmVat) := by
    exact Reasoning.Refinement.execBlock_append hvat hrate
  simp only [nonpayable, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
  simpa [List.append_assoc] using hvatRate

theorem endSkimBodyReverts_afterRateUrnsBlock {I} {vatOut : ByteArray}
    {evm0 evmRate : EVM.State}
    (hprefix :
      ExecBlock config { contract := contract, locals := endSkimStore I } evm0
        (nonpayable ++
          [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
          checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
            "vatIlk" ++
          [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ])
        (.ok { contract := contract, locals := endSkimStoreRate I vatOut } evmRate))
    (hurns :
      ExecBlock config { contract := contract, locals := endSkimStoreRate I vatOut } evmRate
        (checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0)
          [.var "ilk", .var "urn"] "vatUrn") .reverted) :
    ExecTransitionBody config contract evm0 (endSkimStore I) skimTransition.body .reverted := by
  let afterUrns : List Stmt :=
    [ .letDecl "ink" (some uint256) (.tupleGet (.var "vatUrn") 0),
      .letDecl "art" (some uint256) (.tupleGet (.var "vatUrn") 1),
      .internalCall "rmul" [.var "art", .var "rate"] "owe0",
      .internalCall "rmul" [.var "owe0", .storage (tagRef (.var "ilk"))] "owe",
      .internalCall "min" [.var "ink", .var "owe"] "wad",
      .internalCall "sub" [.var "owe", .var "wad"] "diff",
      .internalCall "add" [.storage (gapRef (.var "ilk")), .var "diff"] "gapNew",
      .assign .storage (gapRef (.var "ilk")) (.var "gapNew"),
      .require
        (.binary .and
          (.binary .le (.var "wad") (.intLit int256Limit))
          (.binary .le (.var "art") (.intLit int256Limit))) ] ++
    checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
      [.var "ilk", .var "urn", thisAddr, vowAddr,
       .unary .neg (asInt256 (.var "wad")), .unary .neg (asInt256 (.var "art"))]
      "_grab"
  have hurnsWithTail :
      ExecBlock config { contract := contract, locals := endSkimStoreRate I vatOut } evmRate
        (checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0)
          [.var "ilk", .var "urn"] "vatUrn" ++ afterUrns) .reverted := by
    exact Reasoning.Refinement.execBlock_append_term
      (s2 := afterUrns) hurns (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := endSkimStore I } evm0
        skimTransition.body .reverted := by
    have hseq := Reasoning.Refinement.execBlock_append hprefix hurnsWithTail
    simpa [skimTransition, afterUrns, List.append_assoc] using hseq
  exact ExecFuncBody.execBlockRevert hblock

theorem endSkimBodyReverts_tagZero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSkimTagWord σ I = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endSkimStore I) skimTransition.body .reverted := by
  intro evm0
  have htagLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (endSkimTagSlot I) = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endSkimTagWord, endSlotWord, solcSlotWord] using htag
  have hguard :
      evalExpr? config { contract := contract, locals := endSkimStore I } evm0
        (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_endSkim_tag_ne_false evm0 I hsz68 htagLoad
  refine ExecFuncBody.execBlockRevert ?_
  simpa [skimTransition, nonpayable, checkedExternalCallStmts] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := endSkimStore I })
      (evm := evm0)
      (guard := .binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0))
      (rest :=
        checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk" ++
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
        checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0)
          [.var "ilk", .var "urn"] "vatUrn" ++
        [ .letDecl "ink" (some uint256) (.tupleGet (.var "vatUrn") 0),
          .letDecl "art" (some uint256) (.tupleGet (.var "vatUrn") 1),
          .internalCall "rmul" [.var "art", .var "rate"] "owe0",
          .internalCall "rmul" [.var "owe0", .storage (tagRef (.var "ilk"))] "owe",
          .internalCall "min" [.var "ink", .var "owe"] "wad",
          .internalCall "sub" [.var "owe", .var "wad"] "diff",
          .internalCall "add" [.storage (gapRef (.var "ilk")), .var "diff"] "gapNew",
          .assign .storage (gapRef (.var "ilk")) (.var "gapNew"),
          .require
            (.binary .and
              (.binary .le (.var "wad") (.intLit int256Limit))
              (.binary .le (.var "art") (.intLit int256Limit))) ] ++
        checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
          [.var "ilk", .var "urn", thisAddr, vowAddr,
           .unary .neg (asInt256 (.var "wad")), .unary .neg (asInt256 (.var "art"))]
          "_grab")
      (by simp only [evm0, initState]; exact hwv)
      hguard

theorem endSkimX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endSkimEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := endBytecode) (sel := sel)
    (entry := endSkimEntryPc) (ret := endSkimReturnPc)
    (decoded := endSkimDecodedPc) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem endSkimBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endSkimEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (endSkimX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (endDecode_skim_none_short hsz4 hshort)

theorem endSkimBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf skimTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endSkimConcreteSelector := by
    simpa [endSkimSelectorBytes, endSkimConcreteSelector] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endSkimConcreteSelector (by rfl) hsel'
  have hdispatch : dispatchMsg contract I.calldata = some skimTransition :=
    endDispatchSkim hsel
  have hreach := endReachSkimBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel'
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdecode := endDecode_skim_ok (I := I) hsz68
    obtain ⟨_, _, hbodyReach⟩ :=
      endSkimX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have htagCouple : endSkimTagWord σ_evm I = endSkimTagWord σ_solm I := by
      simpa [endSkimTagWord, endSlotWord] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner (endSkimTagSlot I) ⟨0⟩
    by_cases htag : endSkimTagWord σ_evm I = ⟨0⟩
    · have htagSolm : endSkimTagWord σ_solm I = ⟨0⟩ := by
        rw [← htagCouple]
        exact htag
      have hbody :
          ExecTransitionBody config contract evmSolm (endSkimStore I)
            skimTransition.body .reverted := by
        simpa [evmSolm] using
          endSkimBodyReverts_tagZero
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hwv hsz68 htagSolm
      exact (endSkimX_tagZero (g := Sat256.ofUInt256 g) hsz68 htag hbodyReach)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have htagNE : endSkimTagWord σ_evm I ≠ ⟨0⟩ := htag
      have htagSolmNE : endSkimTagWord σ_solm I ≠ ⟨0⟩ := by
        intro hbad
        exact htagNE (by rw [htagCouple, hbad])
      obtain ⟨kTag, CTag, htagPcRaw⟩ :=
        endSkimX_tagNonzero (g := Sat256.ofUInt256 g) hsz68 htagNE hbodyReach
      have htagPc :
          RD endBytecode I (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨6795⟩
            [endSkimUrnKey I, endSkimIlkWord I, endSkimReturnPc, endSelWord I]
            (endSkimVatIlksBaseMem I) (UInt256.ofNat 3) ByteArray.empty
            (cA, σ_evm) kTag CTag := by
        simpa [endSkimVatIlksBaseMem] using htagPcRaw
      by_cases hvatCode :
          Reasoning.Theory.extCodeSizeWord σ_evm (endPackVatWord σ_evm I) = ⟨0⟩
      · have hvatCodeSolm :
            Reasoning.Theory.extCodeSizeWord σ_solm (endPackVatWord σ_solm I) =
              ⟨0⟩ :=
          endPackVatCodeSize_zero_accountMapEquiv hAccounts hvatCode
        have hbody :
            ExecTransitionBody config contract evmSolm (endSkimStore I)
              skimTransition.body .reverted := by
          simpa [evmSolm] using
            endSkimBodyReverts_vatIlksNoCode
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
              (A := A) (I := I) (g := g) hwv hsz68 htagSolmNE hvatCodeSolm
        exact (endSkimX_vatIlksNoCode (g := Sat256.ofUInt256 g) htagPc hvatCode)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hvatCodeNE :
            Reasoning.Theory.extCodeSizeWord σ_evm (endPackVatWord σ_evm I) ≠
              ⟨0⟩ := hvatCode
        have hvatCodeSolmNE :
            Reasoning.Theory.extCodeSizeWord σ_solm (endPackVatWord σ_solm I) ≠
              ⟨0⟩ :=
          endPackVatCodeSize_ne_accountMapEquiv hAccounts hvatCodeNE
        obtain ⟨gasWord, _, _, hcallReady⟩ :=
          endSkimX_vatIlksCallReady
            (g := Sat256.ofUInt256 g) htagPc hvatCodeNE
        by_cases hdepthLt : I.depth.val < 1024
        · obtain ⟨cA_vat, σ_vat, zVat, vatOut, AinVat, callGasVat, _, _, hΘVat,
              rd6876, hvatOutSize⟩ :=
            endSkimX_vatIlksPostCall hcallReady hdepthLt
          rcases hΘVat with ⟨gVat'', AVat, hΘVatEq⟩
          have hdepthNe :
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.depth ≠
              1024 := by
            intro hbad
            have hbadI : I.depth = 1024 := by
              simpa [initState] using hbad
            have hbadVal : I.depth.val = 1024 := congrArg Fin.val hbadI
            omega
          have htgtVat :
              EVM.address (endPackVatAddr σ_evm I) =
              AccountAddress.ofUInt256 (endPackVatWord σ_evm I) := by
            have hAddressId (a : AccountAddress) : EVM.address a = a := by
              apply Fin.ext
              show ↑a % EVM.twoPow 160 = ↑a
              rw [Nat.mod_eq_of_lt]
              exact a.isLt
            calc
              EVM.address (endPackVatAddr σ_evm I)
                = EVM.address (AccountAddress.ofUInt256 (endPackVatWord σ_evm I)) := by
                  rw [endPackVatAddr_eq_ofUInt256]
              _ = AccountAddress.ofUInt256 (endPackVatWord σ_evm I) :=
                  hAddressId (AccountAddress.ofUInt256 (endPackVatWord σ_evm I))
          obtain ⟨σ_vat_solm, A_vat_solm, hcallSolmRaw, hAccountsVat, hSubstateVat⟩ :=
            endCallMade_accountMapEquiv_with_substate
              (cfg := config)
              (evm_evm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (evm_solm := evmSolm)
              (tgt := EVM.address (endPackVatAddr σ_evm I))
              (targetWord := endPackVatWord σ_evm I)
              (name := "vatIlks")
              (args := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
              (cA' := cA_vat) (σ' := σ_vat) (A' := AVat) (A_in := AinVat)
              (z := zVat) (out := vatOut) (g'' := gVat'') (callGas := callGasVat)
              (mem := endSkimVatIlksCalldataMem I)
              (inOff := endFlowVatIlksOutPtr) (inSize := endFlowVatIlksInSize)
              (callPerm := true)
              hdepthNe htgtVat
              (endSkimVatIlksEncode_eq I hsz68)
              (by simpa [initState, hperm] using hΘVatEq)
              (by simpa [initState] using hAccounts)
              (by simp [evmSolm, initState])
              (by simp [evmSolm, initState])
              (by simp [evmSolm, initState])
              (by simp [evmSolm, initState])
              (by simp [evmSolm, initState])
          have hVatAddr : endPackVatAddr σ_evm I = endPackVatAddr σ_solm I := by
            simp [endPackVatAddr, endPackVatWord_accountMapEquiv hAccounts]
          have hcallSolm :
              typedCallViaEVM config evmSolm
              (EVM.address (endPackVatAddr σ_solm I)) "vatIlks" 0
              [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
              (zVat,
                { evmSolm with
                  accountMap := σ_vat_solm
                  substate := A_vat_solm
                  createdAccounts := cA_vat },
                vatOut) true := by
            simpa [evmSolm, hVatAddr] using hcallSolmRaw
          cases zVat
          · have hbody :
              ExecTransitionBody config contract evmSolm (endSkimStore I)
                skimTransition.body .reverted := by
              simpa [evmSolm] using
                endSkimBodyReverts_vatIlksCallFailed
                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                  (A := A) (I := I) (g := g)
                  (evmVat :=
                    { evmSolm with
                      accountMap := σ_vat_solm
                      substate := A_vat_solm
                      createdAccounts := cA_vat })
                  (out := vatOut)
                  hwv hsz68 htagSolmNE hvatCodeSolmNE
                  (by simpa [evmSolm] using hcallSolm)
            exact (endSkimX_vatIlksCallFailed rd6876 hvatOutSize)
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · let evmVatEvm :=
              { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ_vat
              substate := AVat
              createdAccounts := cA_vat }
            let evmVatSolm :=
              { evmSolm with
              accountMap := σ_vat_solm
              substate := A_vat_solm
              createdAccounts := cA_vat }
            obtain ⟨_, _, rd6894⟩ :=
              endSkimX_vatIlksCallSucceeded (g := Sat256.ofUInt256 g) rd6876
            by_cases hshortVat : vatOut.size < 160
            · have hbody :
                ExecTransitionBody config contract evmSolm (endSkimStore I)
                  skimTransition.body .reverted := by
                simpa [evmVatSolm, evmSolm] using
                  endSkimBodyReverts_vatIlksDecodeShort
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                    (A := A) (I := I) (g := g)
                    (evmVat := evmVatSolm) (out := vatOut)
                    hwv hsz68 htagSolmNE hvatCodeSolmNE
                    (by simpa [evmVatSolm, evmSolm] using hcallSolm)
                    hshortVat
              exact (endSkimX_vatIlksReturnDecodeShort rd6894 hshortVat hvatOutSize)
                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · have hloVat : 160 ≤ vatOut.size := Nat.le_of_not_gt hshortVat
              obtain ⟨_, _, rd6920⟩ :=
                endSkimX_vatIlksReturnDecodeOk rd6894 hloVat hvatOutSize
              have hprefix :
                ExecBlock config { contract := contract, locals := endSkimStore I }
                  evmSolm
                  (nonpayable ++
                    [ .require
                        (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
                    checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0)
                      [.var "ilk"] "vatIlk" ++
                    [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ])
                  (.ok { contract := contract, locals := endSkimStoreRate I vatOut }
                    evmVatSolm) := by
                simpa [evmVatSolm, evmSolm] using
                  endSkimPrefixRateSuccess
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                    (A := A) (I := I) (g := g)
                    (evmVat := evmVatSolm) (out := vatOut)
                    hwv hsz68 htagSolmNE hvatCodeSolmNE
                      (by simpa [evmVatSolm, evmSolm] using hcallSolm)
                      hloVat
              by_cases hurnsCode :
                  Reasoning.Theory.extCodeSizeWord σ_vat
                    (endPackVatWord σ_vat I) = ⟨0⟩
              · have hurnsCodeSolm :
                    Reasoning.Theory.extCodeSizeWord σ_vat_solm
                      (endPackVatWord σ_vat_solm I) = ⟨0⟩ :=
                  endPackVatCodeSize_zero_accountMapEquiv hAccountsVat hurnsCode
                have hurnsBlock :
                    ExecBlock config
                      { contract := contract, locals := endSkimStoreRate I vatOut }
                      evmVatSolm
                      (checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0)
                        [.var "ilk", .var "urn"] "vatUrn") .reverted := by
                  exact endSkimCheckedUrnsNoCode
                    (σ := σ_vat_solm) (I := I) (vatOut := vatOut) (evm := evmVatSolm)
                    (by simp [evmVatSolm])
                    (by simp [evmVatSolm, evmSolm, initState])
                    hurnsCodeSolm
                have hbody :
                    ExecTransitionBody config contract evmSolm (endSkimStore I)
                      skimTransition.body .reverted := by
                  exact endSkimBodyReverts_afterRateUrnsBlock hprefix hurnsBlock
                exact (endSkimX_urnsNoCode rd6920 hloVat hurnsCode)
                  |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · have hurnsCodeNE :
                    Reasoning.Theory.extCodeSizeWord σ_vat
                      (endPackVatWord σ_vat I) ≠ ⟨0⟩ := hurnsCode
                have hurnsCodeSolmNE :
                    Reasoning.Theory.extCodeSizeWord σ_vat_solm
                      (endPackVatWord σ_vat_solm I) ≠ ⟨0⟩ :=
                  endPackVatCodeSize_ne_accountMapEquiv hAccountsVat hurnsCodeNE
                obtain ⟨gasWordUrns, _, _, hurnsReady⟩ :=
                  endSkimX_urnsCallReady rd6920 hloVat hurnsCodeNE
                obtain ⟨cA_urns, σ_urns, zUrns, urnOut, AinUrns, callGasUrns, _, _,
                    hΘUrns, rd7012, hurnOutSize⟩ :=
                  endSkimX_urnsPostCall hurnsReady hdepthLt
                rcases hΘUrns with ⟨gUrns'', AUrns, hΘUrnsEq⟩
                have htgtUrns :
                    EVM.address (endPackVatAddr σ_vat I) =
                      AccountAddress.ofUInt256 (endPackVatWord σ_vat I) := by
                  have hAddressId (a : AccountAddress) : EVM.address a = a := by
                    apply Fin.ext
                    show ↑a % EVM.twoPow 160 = ↑a
                    rw [Nat.mod_eq_of_lt]
                    exact a.isLt
                  calc
                    EVM.address (endPackVatAddr σ_vat I)
                        = EVM.address (AccountAddress.ofUInt256 (endPackVatWord σ_vat I)) := by
                          rw [endPackVatAddr_eq_ofUInt256]
                    _ = AccountAddress.ofUInt256 (endPackVatWord σ_vat I) :=
                          hAddressId (AccountAddress.ofUInt256 (endPackVatWord σ_vat I))
                obtain ⟨σ_urns_solm, A_urns_solm, hcallUrnsSolmRaw, hAccountsUrns,
                    hSubstateUrns⟩ :=
                  endCallMade_accountMapEquiv_with_substate
                    (cfg := config)
                    (evm_evm := evmVatEvm)
                    (evm_solm := evmVatSolm)
                    (tgt := EVM.address (endPackVatAddr σ_vat I))
                    (targetWord := endPackVatWord σ_vat I)
                    (name := "urns")
                    (args := [.fixedBytes bytes32Width (endBytes32ArgBytes I),
                      .address (endSkimUrnAddr I)])
                    (cA' := cA_urns) (σ' := σ_urns) (A' := AUrns) (A_in := AinUrns)
                    (z := zUrns) (out := urnOut) (g'' := gUrns'')
                    (callGas := callGasUrns)
                    (mem := endSkimUrnsCalldataMem I vatOut)
                    (inOff := endFreeUrnsOutPtr) (inSize := endFreeUrnsInSize)
                    (callPerm := true)
                    (by simpa [evmVatEvm, initState] using hdepthNe)
                    htgtUrns
                    (endSkimUrnsEncode_eq I vatOut hsz68 hloVat)
                    (by simpa [evmVatEvm, initState, hperm] using hΘUrnsEq)
                    (by simpa [evmVatEvm, evmVatSolm] using hAccountsVat)
                    (by simp [evmVatEvm, evmVatSolm, evmSolm, initState])
                    (by simp [evmVatEvm, evmVatSolm, evmSolm, initState])
                    (by simp [evmVatEvm, evmVatSolm, evmSolm, initState])
                    (by simp [evmVatEvm, evmVatSolm, evmSolm, initState])
                    (by simp [evmVatEvm, evmVatSolm, evmSolm, initState])
                have hVatAddrUrns :
                    endPackVatAddr σ_vat I = endPackVatAddr σ_vat_solm I := by
                  simp [endPackVatAddr, endPackVatWord_accountMapEquiv hAccountsVat]
                have hcallUrnsSolm :
                    typedCallViaEVM config evmVatSolm
                      (EVM.address (endPackVatAddr σ_vat_solm I)) "urns" 0
                      [.fixedBytes bytes32Width (endBytes32ArgBytes I),
                        .address (endSkimUrnAddr I)]
                      (zUrns,
                        { evmVatSolm with
                          accountMap := σ_urns_solm
                          substate := A_urns_solm
                          createdAccounts := cA_urns },
                        urnOut) true := by
                  simpa [hVatAddrUrns] using hcallUrnsSolmRaw
                cases zUrns
                · have hurnsBlock :
                      ExecBlock config
                        { contract := contract, locals := endSkimStoreRate I vatOut }
                        evmVatSolm
                        (checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0)
                          [.var "ilk", .var "urn"] "vatUrn") .reverted := by
                    exact endSkimCheckedUrnsFailure
                      (σ := σ_vat_solm) (I := I) (vatOut := vatOut) (urnOut := urnOut)
                      (evm := evmVatSolm)
                      (evmUrns :=
                        { evmVatSolm with
                          accountMap := σ_urns_solm
                          substate := A_urns_solm
                          createdAccounts := cA_urns })
                      (by simp [evmVatSolm])
                      (by simp [evmVatSolm, evmSolm, initState])
                      hurnsCodeSolmNE
                      (by simpa using hcallUrnsSolm)
                  have hbody :
                      ExecTransitionBody config contract evmSolm (endSkimStore I)
                        skimTransition.body .reverted := by
                    exact endSkimBodyReverts_afterRateUrnsBlock hprefix hurnsBlock
                  exact (endSkimX_urnsCallFailed rd7012 hurnOutSize)
                    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                · let evmUrnsSolm :=
                    { evmVatSolm with
                      accountMap := σ_urns_solm
                      substate := A_urns_solm
                      createdAccounts := cA_urns }
                  obtain ⟨_, _, rd7030⟩ :=
                    endSkimX_urnsCallSucceeded rd7012
                  by_cases hshortUrn : urnOut.size < 64
                  · have hurnsBlock :
                        ExecBlock config
                          { contract := contract, locals := endSkimStoreRate I vatOut }
                          evmVatSolm
                          (checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0)
                            [.var "ilk", .var "urn"] "vatUrn") .reverted := by
                      exact endSkimCheckedUrnsDecodeRevert
                        (σ := σ_vat_solm) (I := I) (vatOut := vatOut)
                        (urnOut := urnOut) (evm := evmVatSolm) (evmUrns := evmUrnsSolm)
                        (by simp [evmVatSolm])
                        (by simp [evmVatSolm, evmSolm, initState])
                        hurnsCodeSolmNE
                        (by simpa [evmUrnsSolm] using hcallUrnsSolm)
                        hshortUrn
                    have hbody :
                        ExecTransitionBody config contract evmSolm (endSkimStore I)
                          skimTransition.body .reverted := by
                      exact endSkimBodyReverts_afterRateUrnsBlock hprefix hurnsBlock
                    exact (endSkimX_urnsReturnDecodeShort rd7030 hloVat hshortUrn
                      hurnOutSize)
                      |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                  · have hloUrn : 64 ≤ urnOut.size := Nat.le_of_not_gt hshortUrn
                    obtain ⟨_, _, rd7065⟩ :=
                      endSkimX_urnsReturnDecodeOk rd7030 hloVat hloUrn hurnOutSize
                    have hurnsBlock :
                        ExecBlock config
                          { contract := contract, locals := endSkimStoreRate I vatOut }
                          evmVatSolm
                          (checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0)
                            [.var "ilk", .var "urn"] "vatUrn")
                          (.ok
                            { contract := contract
                              locals := endSkimStoreVatUrn I vatOut urnOut }
                            evmUrnsSolm) := by
                      exact endSkimCheckedUrnsSuccess
                        (σ := σ_vat_solm) (I := I) (vatOut := vatOut)
                        (urnOut := urnOut) (evm := evmVatSolm) (evmUrns := evmUrnsSolm)
                        (by simp [evmVatSolm])
                        (by simp [evmVatSolm, evmSolm, initState])
                        hurnsCodeSolmNE
                        (by simpa [evmUrnsSolm] using hcallUrnsSolm)
                        hloUrn
                    have hinkArt :
                        ExecBlock config
                          { contract := contract,
                            locals := endSkimStoreVatUrn I vatOut urnOut }
                          evmUrnsSolm
                          [ .letDecl "ink" (some uint256)
                              (.tupleGet (.var "vatUrn") 0),
                            .letDecl "art" (some uint256)
                              (.tupleGet (.var "vatUrn") 1) ]
                          (.ok
                            { contract := contract,
                              locals := endSkimStoreArt I vatOut urnOut }
                            evmUrnsSolm) := by
                      exact ExecBlock.consNormal
                        (endSkimStmtInk evmUrnsSolm I vatOut urnOut)
                        (ExecBlock.consNormal
                          (endSkimStmtArt evmUrnsSolm I vatOut urnOut) ExecBlock.nil)
                    have hprefixArt :
                        ExecBlock config { contract := contract, locals := endSkimStore I }
                          evmSolm
                          (nonpayable ++
                            [ .require
                                (.binary .ne (.storage (tagRef (.var "ilk")))
                                  (.intLit 0)) ] ++
                            checkedExternalCallStmts (.storage vatRef) "vatIlks"
                              (.intLit 0) [.var "ilk"] "vatIlk" ++
                            [ .letDecl "rate" (some uint256)
                                (.tupleGet (.var "vatIlk") 1) ] ++
                            checkedExternalCallStmts (.storage vatRef) "urns"
                              (.intLit 0) [.var "ilk", .var "urn"] "vatUrn" ++
                            [ .letDecl "ink" (some uint256)
                                (.tupleGet (.var "vatUrn") 0),
                              .letDecl "art" (some uint256)
                                (.tupleGet (.var "vatUrn") 1) ])
                          (.ok
                            { contract := contract,
                              locals := endSkimStoreArt I vatOut urnOut }
                            evmUrnsSolm) := by
                      have hurnsInkArt :=
                        Reasoning.Refinement.execBlock_append hurnsBlock hinkArt
                      simpa [List.append_assoc] using
                        Reasoning.Refinement.execBlock_append hprefix hurnsInkArt
                    have hTagCoupleUrns :
                        endSkimTagWord σ_urns I = endSkimTagWord σ_urns_solm I := by
                      simpa [endSkimTagWord, endSlotWord] using
                        accountMapEquiv_storage_findD hAccountsUrns I.codeOwner
                          (endSkimTagSlot I) ⟨0⟩
                    have hGapCoupleUrns :
                        endSkimGapWord σ_urns I = endSkimGapWord σ_urns_solm I := by
                      simpa [endSkimGapWord, endSlotWord] using
                        accountMapEquiv_storage_findD hAccountsUrns I.codeOwner
                          (endSkimGapSlot I) ⟨0⟩
                    have hTagLoadSolm :
                        Solm.EVM.storageLoad evmUrnsSolm evmUrnsSolm.executionEnv.codeOwner
                          (endSkimTagSlot I) = endSkimTagWord σ_urns_solm I := by
                      simp [evmUrnsSolm, Solm.EVM.storageLoad, State.lookupAccount,
                        evmVatSolm, evmSolm, initState, endSkimTagWord, endSlotWord,
                        solcSlotWord, Account.lookupStorage]
                    have hGapLoadSolm :
                        Solm.EVM.storageLoad evmUrnsSolm evmUrnsSolm.executionEnv.codeOwner
                          (endSkimGapSlot I) = endSkimGapWord σ_urns_solm I := by
                      simp [evmUrnsSolm, Solm.EVM.storageLoad, State.lookupAccount,
                        evmVatSolm, evmSolm, initState, endSkimGapWord, endSlotWord,
                        solcSlotWord, Account.lookupStorage]
                    obtain ⟨_, _, rdOwe0Entry⟩ :=
                      endSkimX_owe0RmulEntry (g := Sat256.ofUInt256 g) rd7065
                    by_cases hoverOwe0 :
                        UInt256.size ≤
                          (endFreeUrnArtWord urnOut).toNat *
                            (endFlowVatIlkRateWord vatOut).toNat
                    · have htail :=
                        endSkimTailReverts_owe0RmulOverflow evmUrnsSolm I vatOut urnOut
                          hoverOwe0
                      have hbody :
                          ExecTransitionBody config contract evmSolm (endSkimStore I)
                            skimTransition.body .reverted := by
                        exact endSkimBodyReverts_afterArtTailReverted hprefixArt htail
                      exact
                        (endFlowX_rmulOverflow
                          (x := endFreeUrnArtWord urnOut)
                          (y := endFlowVatIlkRateWord vatOut)
                          (ret := ⟨7079⟩)
                          (R := [⟨7099⟩, ⟨0⟩, endFreeUrnArtWord urnOut,
                            endFreeUrnInkWord urnOut, endFlowVatIlkRateWord vatOut,
                            endSkimUrnKey I, endSkimIlkWord I, endSkimReturnPc,
                            endSelWord I])
                          hoverOwe0 rdOwe0Entry
                          (by simp only [List.length_cons, List.length_nil]; omega))
                          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                    · have hfitOwe0 :
                        (endFreeUrnArtWord urnOut).toNat *
                            (endFlowVatIlkRateWord vatOut).toNat <
                          UInt256.size :=
                        Nat.lt_of_not_ge hoverOwe0
                      obtain ⟨_, _, rd7079⟩ : ∃ k' C',
                          RD endBytecode I (Sat256.ofUInt256 g)
                            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                            ⟨7079⟩
                            (endSkimOwe0Word vatOut urnOut :: ⟨7099⟩ :: ⟨0⟩ ::
                              endFreeUrnArtWord urnOut :: endFreeUrnInkWord urnOut ::
                              endFlowVatIlkRateWord vatOut :: endSkimUrnKey I ::
                              endSkimIlkWord I :: endSkimReturnPc :: endSelWord I :: [])
                            (endSkimUrnsPostCallMem I vatOut urnOut) (UInt256.ofNat 9)
                            urnOut (cA_urns, σ_urns) k' C' := by
                        by_cases hrateZero : endFlowVatIlkRateWord vatOut = ⟨0⟩
                        · obtain ⟨_, _, rd7079raw⟩ :=
                            endFlowX_rmulReturnsZero
                              (x := endFreeUrnArtWord urnOut)
                              (y := endFlowVatIlkRateWord vatOut)
                              (ret := ⟨7079⟩)
                              (R := [⟨7099⟩, ⟨0⟩, endFreeUrnArtWord urnOut,
                                endFreeUrnInkWord urnOut, endFlowVatIlkRateWord vatOut,
                                endSkimUrnKey I, endSkimIlkWord I, endSkimReturnPc,
                                endSelWord I])
                              hrateZero rdOwe0Entry (by jump_dest)
                              (by simp only [List.length_cons, List.length_nil]; omega)
                          exact ⟨_, _, by simpa [endSkimOwe0Word] using rd7079raw⟩
                        · obtain ⟨_, _, rd7079raw⟩ :=
                            endFlowX_rmulReturns
                              (x := endFreeUrnArtWord urnOut)
                              (y := endFlowVatIlkRateWord vatOut)
                              (ret := ⟨7079⟩)
                              (R := [⟨7099⟩, ⟨0⟩, endFreeUrnArtWord urnOut,
                                endFreeUrnInkWord urnOut, endFlowVatIlkRateWord vatOut,
                                endSkimUrnKey I, endSkimIlkWord I, endSkimReturnPc,
                                endSelWord I])
                              hfitOwe0 hrateZero rdOwe0Entry (by jump_dest)
                              (by simp only [List.length_cons, List.length_nil]; omega)
                          exact ⟨_, _, by simpa [endSkimOwe0Word] using rd7079raw⟩
                      obtain ⟨_, _, rdOweEntry⟩ :=
                        endSkimX_oweRmulEntry (g := Sat256.ofUInt256 g)
                          hsz68 hloVat rd7079
                      by_cases hoverOwe :
                          UInt256.size ≤
                            (endSkimOwe0Word vatOut urnOut).toNat *
                              (endSkimTagWord σ_urns I).toNat
                      · have hoverOweSolm :
                            UInt256.size ≤
                              (endSkimOwe0Word vatOut urnOut).toNat *
                                (endSkimTagWord σ_urns_solm I).toNat := by
                          simpa [hTagCoupleUrns] using hoverOwe
                        have htail :=
                          endSkimTailReverts_oweRmulOverflow evmUrnsSolm I
                            σ_urns_solm vatOut urnOut hsz68 hTagLoadSolm
                            hfitOwe0 hoverOweSolm
                        have hbody :
                            ExecTransitionBody config contract evmSolm (endSkimStore I)
                              skimTransition.body .reverted := by
                          exact endSkimBodyReverts_afterArtTailReverted hprefixArt htail
                        exact
                          (endFlowX_rmulOverflow
                            (x := endSkimOwe0Word vatOut urnOut)
                            (y := endSkimTagWord σ_urns I)
                            (ret := ⟨7099⟩)
                            (R := [⟨0⟩, endFreeUrnArtWord urnOut,
                              endFreeUrnInkWord urnOut, endFlowVatIlkRateWord vatOut,
                              endSkimUrnKey I, endSkimIlkWord I, endSkimReturnPc,
                              endSelWord I])
                            hoverOwe rdOweEntry
                            (by simp only [List.length_cons, List.length_nil]; omega))
                            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                      · have hfitOwe :
                            (endSkimOwe0Word vatOut urnOut).toNat *
                                (endSkimTagWord σ_urns I).toNat <
                              UInt256.size :=
                          Nat.lt_of_not_ge hoverOwe
                        have hfitOweSolm :
                            (endSkimOwe0Word vatOut urnOut).toNat *
                                (endSkimTagWord σ_urns_solm I).toNat <
                              UInt256.size := by
                          simpa [hTagCoupleUrns] using hfitOwe
                        obtain ⟨_, _, rd7099⟩ : ∃ k' C',
                            RD endBytecode I (Sat256.ofUInt256 g)
                              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                              ⟨7099⟩
                              (endSkimOweWord σ_urns I vatOut urnOut :: ⟨0⟩ ::
                                endFreeUrnArtWord urnOut :: endFreeUrnInkWord urnOut ::
                                endFlowVatIlkRateWord vatOut :: endSkimUrnKey I ::
                                endSkimIlkWord I :: endSkimReturnPc :: endSelWord I :: [])
                              (endSkimTagHashMem I vatOut urnOut) (UInt256.ofNat 9)
                              urnOut (cA_urns, σ_urns) k' C' := by
                          by_cases htagZero : endSkimTagWord σ_urns I = ⟨0⟩
                          · obtain ⟨_, _, rd7099raw⟩ :=
                              endFlowX_rmulReturnsZero
                                (x := endSkimOwe0Word vatOut urnOut)
                                (y := endSkimTagWord σ_urns I)
                                (ret := ⟨7099⟩)
                                (R := [⟨0⟩, endFreeUrnArtWord urnOut,
                                  endFreeUrnInkWord urnOut, endFlowVatIlkRateWord vatOut,
                                  endSkimUrnKey I, endSkimIlkWord I, endSkimReturnPc,
                                  endSelWord I])
                                htagZero rdOweEntry (by jump_dest)
                                (by simp only [List.length_cons, List.length_nil]; omega)
                            exact ⟨_, _, by simpa [endSkimOweWord] using rd7099raw⟩
                          · obtain ⟨_, _, rd7099raw⟩ :=
                              endFlowX_rmulReturns
                                (x := endSkimOwe0Word vatOut urnOut)
                                (y := endSkimTagWord σ_urns I)
                                (ret := ⟨7099⟩)
                                (R := [⟨0⟩, endFreeUrnArtWord urnOut,
                                  endFreeUrnInkWord urnOut, endFlowVatIlkRateWord vatOut,
                                  endSkimUrnKey I, endSkimIlkWord I, endSkimReturnPc,
                                  endSelWord I])
                                hfitOwe htagZero rdOweEntry (by jump_dest)
                                (by simp only [List.length_cons, List.length_nil]; omega)
                            exact ⟨_, _, by simpa [endSkimOweWord] using rd7099raw⟩
                        obtain ⟨_, _, rdMinEntry⟩ :=
                          endSkimX_minEntry (g := Sat256.ofUInt256 g) rd7099
                        obtain ⟨_, _, rd7113raw⟩ :=
                          endSkimX_minReturns
                            (x := endFreeUrnInkWord urnOut)
                            (y := endSkimOweWord σ_urns I vatOut urnOut)
                            (ret := ⟨7113⟩)
                            (R := [⟨0⟩, endSkimOweWord σ_urns I vatOut urnOut,
                              endFreeUrnArtWord urnOut, endFreeUrnInkWord urnOut,
                              endFlowVatIlkRateWord vatOut, endSkimUrnKey I,
                              endSkimIlkWord I, endSkimReturnPc, endSelWord I])
                            rdMinEntry (by jump_dest)
                            (by simp only [List.length_cons, List.length_nil]; omega)
                        obtain ⟨_, _, rd7113⟩ : ∃ k' C',
                            RD endBytecode I (Sat256.ofUInt256 g)
                              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                              ⟨7113⟩
                              (endSkimWadWord σ_urns I vatOut urnOut :: ⟨0⟩ ::
                                endSkimOweWord σ_urns I vatOut urnOut ::
                                endFreeUrnArtWord urnOut :: endFreeUrnInkWord urnOut ::
                                endFlowVatIlkRateWord vatOut :: endSkimUrnKey I ::
                                endSkimIlkWord I :: endSkimReturnPc :: endSelWord I :: [])
                              (endSkimTagHashMem I vatOut urnOut) (UInt256.ofNat 9)
                              urnOut (cA_urns, σ_urns) k' C' := by
                          exact ⟨_, _, by simpa [endSkimWadWord] using rd7113raw⟩
                        by_cases hoverGap :
                            UInt256.size ≤
                              (endSkimGapWord σ_urns I).toNat +
                                (endSkimDiffWord σ_urns I vatOut urnOut).toNat
                        · have hoverGapSolm :
                              UInt256.size ≤
                                (endSkimGapWord σ_urns_solm I).toNat +
                                  (endSkimDiffWord σ_urns_solm I vatOut urnOut).toNat := by
                            simpa [hGapCoupleUrns, hTagCoupleUrns, endSkimDiffWord,
                              endSkimWadWord, endSkimOweWord] using hoverGap
                          have htail :=
                            endSkimTailReverts_gapAddOverflow evmUrnsSolm I
                              σ_urns_solm vatOut urnOut hsz68 hTagLoadSolm
                              hGapLoadSolm hfitOwe0 hfitOweSolm hoverGapSolm
                          have hbody :
                              ExecTransitionBody config contract evmSolm (endSkimStore I)
                                skimTransition.body .reverted := by
                            exact endSkimBodyReverts_afterArtTailReverted hprefixArt htail
                          exact
                            (endSkimX_gapAddOverflow (g := Sat256.ofUInt256 g)
                              hsz68 hloVat hoverGap rd7113)
                              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                        · have hfitGap :
                              (endSkimGapWord σ_urns I).toNat +
                                  (endSkimDiffWord σ_urns I vatOut urnOut).toNat <
                                UInt256.size :=
                            Nat.lt_of_not_ge hoverGap
                          have hfitGapSolm :
                              (endSkimGapWord σ_urns_solm I).toNat +
                                  (endSkimDiffWord σ_urns_solm I vatOut urnOut).toNat <
                                UInt256.size := by
                            simpa [hGapCoupleUrns, hTagCoupleUrns, endSkimDiffWord,
                              endSkimWadWord, endSkimOweWord] using hfitGap
                          obtain ⟨_, _, rd7150⟩ :=
                            endSkimX_gapAddReturns (g := Sat256.ofUInt256 g)
                              hsz68 hloVat hfitGap rd7113
                          by_cases hwadLimit :
                              (endSkimWadWord σ_urns I vatOut urnOut).toNat ≤ 2 ^ 255
                          · by_cases hartLimit :
                                (endFreeUrnArtWord urnOut).toNat ≤ 2 ^ 255
                            · have hwadLimitSolm :
                                  (endSkimWadWord σ_urns_solm I vatOut urnOut).toNat ≤
                                    2 ^ 255 := by
                                simpa [hTagCoupleUrns, endSkimWadWord, endSkimOweWord]
                                  using hwadLimit
                              obtain ⟨_, _, rd7253⟩ :=
                                endSkimX_gapStoreIntGuardOk (g := Sat256.ofUInt256 g)
                                  hperm hsz68 hloVat hwadLimit hartLimit rd7150
                              have htailOk :=
                                endSkimTailAfterArtReturns evmUrnsSolm I σ_urns_solm
                                  vatOut urnOut hsz68 hTagLoadSolm hGapLoadSolm
                                  hfitOwe0 hfitOweSolm hfitGapSolm hwadLimitSolm
                                  hartLimit
                              let evmUrnsEvm :=
                                { evmVatEvm with
                                  accountMap := σ_urns
                                  substate := AUrns
                                  createdAccounts := cA_urns }
                              let σ_post :=
                                endSkimPostGapAccountMap σ_urns I
                                  (endSkimGapNewWord σ_urns I vatOut urnOut)
                              let σ_post_solm :=
                                endSkimPostGapAccountMap σ_urns_solm I
                                  (endSkimGapNewWord σ_urns_solm I vatOut urnOut)
                              let evmPostEvm :=
                                endSkimPostGapState evmUrnsEvm I
                                  (endSkimGapNewWord σ_urns I vatOut urnOut)
                              let evmPostSolm :=
                                endSkimPostGapState evmUrnsSolm I
                                  (endSkimGapNewWord σ_urns_solm I vatOut urnOut)
                              have hStateUrns : EVMStateEquiv evmUrnsEvm evmUrnsSolm := by
                                refine ⟨?_, ?_, ?_⟩
                                · simp [evmUrnsEvm, evmUrnsSolm, evmVatEvm, evmVatSolm,
                                    evmSolm, initState]
                                · simp [evmUrnsEvm, evmUrnsSolm]
                                · simpa [evmUrnsEvm, evmUrnsSolm] using hAccountsUrns
                              have hGapNewCouple :
                                  endSkimGapNewWord σ_urns I vatOut urnOut =
                                    endSkimGapNewWord σ_urns_solm I vatOut urnOut := by
                                simp [endSkimGapNewWord, endSkimDiffWord, endSkimWadWord,
                                  endSkimOweWord, hGapCoupleUrns, hTagCoupleUrns]
                              have hAccountsPost :
                                  accountMapEquiv σ_post σ_post_solm := by
                                have hStatePost :
                                    EVMStateEquiv evmPostEvm evmPostSolm := by
                                  simpa [evmPostEvm, evmPostSolm, endSkimPostGapState] using
                                    hStateUrns.storageStore_codeOwner (endSkimGapSlot I)
                                      hGapNewCouple
                                simpa [evmPostEvm, evmPostSolm, σ_post, σ_post_solm,
                                  endSkimPostGapState, endSkimPostGapAccountMap,
                                  storageStore_accountMap] using hStatePost.accountMap
                              have hmapPostSolm : evmPostSolm.accountMap = σ_post_solm := by
                                simp [evmPostSolm, σ_post_solm, endSkimPostGapState,
                                  endSkimPostGapAccountMap, storageStore_accountMap,
                                  evmUrnsSolm, evmVatSolm, evmSolm, initState]
                              have hownerPostSolm :
                                  evmPostSolm.executionEnv.codeOwner = I.codeOwner := by
                                simp [evmPostSolm, endSkimPostGapState,
                                  storageStore_executionEnv, evmUrnsSolm, evmVatSolm,
                                  evmSolm, initState]
                              by_cases hgrabCode :
                                  Reasoning.Theory.extCodeSizeWord σ_post
                                    (endPackVatWord σ_post I) = ⟨0⟩
                              · have hgrabCodeSolm :
                                    Reasoning.Theory.extCodeSizeWord σ_post_solm
                                      (endPackVatWord σ_post_solm I) = ⟨0⟩ :=
                                  endPackVatCodeSize_zero_accountMapEquiv hAccountsPost
                                    hgrabCode
                                have hgrab :=
                                  endSkimGrabTailReverts_noCodeFor
                                    (σCall := σ_post_solm) (σLoc := σ_urns_solm)
                                    (I := I) (vatOut := vatOut) (urnOut := urnOut)
                                    (evm := evmPostSolm) hmapPostSolm hownerPostSolm
                                    hgrabCodeSolm
                                have hbody :
                                    ExecTransitionBody config contract evmSolm
                                      (endSkimStore I) skimTransition.body .reverted := by
                                  exact endSkimBodyReverts_afterArtTailGrabReverted
                                    hprefixArt htailOk hgrab
                                exact
                                  (endSkimX_grabNoCode
                                    (g := Sat256.ofUInt256 g) (σCall := σ_post)
                                    (σLoc := σ_urns) hloVat rd7253 hgrabCode)
                                    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                              · have hgrabCodeNE :
                                    Reasoning.Theory.extCodeSizeWord σ_post
                                      (endPackVatWord σ_post I) ≠ ⟨0⟩ := hgrabCode
                                have hgrabCodeSolmNE :
                                    Reasoning.Theory.extCodeSizeWord σ_post_solm
                                      (endPackVatWord σ_post_solm I) ≠ ⟨0⟩ :=
                                  endPackVatCodeSize_ne_accountMapEquiv hAccountsPost
                                    hgrabCodeNE
                                obtain ⟨grabGasWord, _, _, rdGrabReady⟩ :=
                                  endSkimX_grabCallReady
                                    (g := Sat256.ofUInt256 g) (σCall := σ_post)
                                    (σLoc := σ_urns) hloVat rd7253 hgrabCodeNE
                                by_cases hgrabDepthLt : I.depth.val < 1024
                                · obtain ⟨cA_grab, σ_grab, zGrab, ret, AinGrab,
                                      callGasGrab, _, _, hΘGrab, rd7373, hretSize⟩ :=
                                    endSkimX_grabPostCall
                                      (g := Sat256.ofUInt256 g) (σCall := σ_post)
                                      (σLoc := σ_urns) rdGrabReady hgrabDepthLt
                                  rcases hΘGrab with ⟨gGrab'', AGrab, hΘGrabEq⟩
                                  have hStatePost :
                                      EVMStateEquiv evmPostEvm evmPostSolm := by
                                    simpa [evmPostEvm, evmPostSolm,
                                      endSkimPostGapState] using
                                      hStateUrns.storageStore_codeOwner (endSkimGapSlot I)
                                        hGapNewCouple
                                  have hdepthNeGrab :
                                      evmPostEvm.executionEnv.depth ≠ 1024 := by
                                    intro hbad
                                    have hbadI : I.depth = 1024 := by
                                      simpa [evmPostEvm, endSkimPostGapState,
                                        storageStore_executionEnv, evmUrnsEvm, evmVatEvm,
                                        initState] using hbad
                                    have hbadVal : I.depth.val = 1024 :=
                                      congrArg Fin.val hbadI
                                    omega
                                  have hAddressId (a : AccountAddress) : EVM.address a = a := by
                                    apply Fin.ext
                                    show ↑a % EVM.twoPow 160 = ↑a
                                    rw [Nat.mod_eq_of_lt]
                                    exact a.isLt
                                  have htgtGrab :
                                      EVM.address (endPackVatAddr σ_post I) =
                                        AccountAddress.ofUInt256
                                          (endPackVatWord σ_post I) := by
                                    calc
                                      EVM.address (endPackVatAddr σ_post I)
                                          = EVM.address
                                              (AccountAddress.ofUInt256
                                                (endPackVatWord σ_post I)) := by
                                            rw [endPackVatAddr_eq_ofUInt256]
                                      _ = AccountAddress.ofUInt256
                                            (endPackVatWord σ_post I) :=
                                            hAddressId
                                              (AccountAddress.ofUInt256
                                                (endPackVatWord σ_post I))
                                  obtain ⟨σ_grab_solm, A_grab_solm, hgrabCallSolmRaw,
                                      hAccountsGrab, hSubstateGrab⟩ :=
                                    endCallMade_accountMapEquiv_with_substate
                                      (cfg := config) (evm_evm := evmPostEvm)
                                      (evm_solm := evmPostSolm)
                                      (tgt := EVM.address (endPackVatAddr σ_post I))
                                      (targetWord := endPackVatWord σ_post I)
                                      (name := "grab")
                                      (args :=
                                        [.fixedBytes bytes32Width (endBytes32ArgBytes I),
                                          .address (endSkimUrnAddr I),
                                          .address I.codeOwner,
                                          .address (endPackVowAddr σ_post I),
                                          .int (-(Int.ofNat
                                            (endSkimWadWord σ_urns I vatOut urnOut).toNat)),
                                          .int (-(Int.ofNat
                                            (endFreeUrnArtWord urnOut).toNat))])
                                      (cA' := cA_grab) (σ' := σ_grab) (A' := AGrab)
                                      (A_in := AinGrab) (z := zGrab) (out := ret)
                                      (g'' := gGrab'') (callGas := callGasGrab)
                                      (mem := endSkimGrabCalldataMemFor σ_post σ_urns I
                                        vatOut urnOut)
                                      (inOff := endFreeGrabOutPtr)
                                      (inSize := endFreeGrabInSize) (callPerm := true)
                                      hdepthNeGrab htgtGrab
                                      (endSkimGrabEncodeFor_eq σ_post σ_urns I vatOut
                                        urnOut hsz68 hloVat hwadLimit hartLimit)
                                      (by simpa [evmPostEvm, endSkimPostGapState,
                                        storageStore_executionEnv, storageStore_createdAccounts,
                                        storageStore_accountMap, endSkim_storageStore_σ₀,
                                        endSkim_storageStore_genesisBlockHeader,
                                        endSkim_storageStore_blocks, σ_post,
                                        endSkimPostGapAccountMap, evmUrnsEvm, evmVatEvm,
                                        initState, hperm] using hΘGrabEq)
                                      hStatePost.accountMap
                                      (by simp [evmPostEvm, evmPostSolm, endSkimPostGapState,
                                        endSkim_storageStore_σ₀,
                                        evmUrnsEvm, evmUrnsSolm, evmVatEvm, evmVatSolm,
                                        evmSolm, initState])
                                      (by simpa [evmPostEvm, evmPostSolm] using
                                        hStatePost.createdAccounts.symm)
                                      (by simp [evmPostEvm, evmPostSolm, endSkimPostGapState,
                                        endSkim_storageStore_genesisBlockHeader,
                                        evmUrnsEvm, evmUrnsSolm, evmVatEvm, evmVatSolm,
                                        evmSolm, initState])
                                      (by simp [evmPostEvm, evmPostSolm, endSkimPostGapState,
                                        endSkim_storageStore_blocks,
                                        evmUrnsEvm, evmUrnsSolm, evmVatEvm, evmVatSolm,
                                        evmSolm, initState])
                                      (by simpa [evmPostEvm, evmPostSolm] using
                                        hStatePost.executionEnv.symm)
                                  have hVatWordGrab :
                                      endPackVatWord σ_post I =
                                        endPackVatWord σ_post_solm I :=
                                    endPackVatWord_accountMapEquiv hAccountsPost
                                  have hVatAddrGrab :
                                      endPackVatAddr σ_post I =
                                        endPackVatAddr σ_post_solm I := by
                                    simp [endPackVatAddr, hVatWordGrab]
                                  have hVowWordGrab :
                                      endPackVowWord σ_post I =
                                        endPackVowWord σ_post_solm I := by
                                    have hslot :
                                        endSlotWord ⟨4⟩ σ_post I =
                                          endSlotWord ⟨4⟩ σ_post_solm I := by
                                      simpa [endSlotWord, solcSlotWord] using
                                        accountMapEquiv_storage_findD hAccountsPost
                                          I.codeOwner ⟨4⟩ ⟨0⟩
                                    simpa [endPackVowWord] using
                                      congrArg (fun w => UInt256.land w solcAddrMask) hslot
                                  have hVowAddrGrab :
                                      endPackVowAddr σ_post I =
                                        endPackVowAddr σ_post_solm I := by
                                    simp [endPackVowAddr, hVowWordGrab]
                                  have hWadWordGrab :
                                      endSkimWadWord σ_urns I vatOut urnOut =
                                        endSkimWadWord σ_urns_solm I vatOut urnOut := by
                                    simp [endSkimWadWord, endSkimOweWord, hTagCoupleUrns]
                                  have hgrabCallSolm :
                                      typedCallViaEVM config evmPostSolm
                                        (EVM.address (endPackVatAddr σ_post_solm I))
                                        "grab" 0
                                        [.fixedBytes bytes32Width (endBytes32ArgBytes I),
                                          .address (endSkimUrnAddr I),
                                          .address I.codeOwner,
                                          .address (endPackVowAddr σ_post_solm I),
                                          .int (-(Int.ofNat
                                            (endSkimWadWord σ_urns_solm I vatOut urnOut).toNat)),
                                          .int (-(Int.ofNat
                                            (endFreeUrnArtWord urnOut).toNat))]
                                        (zGrab,
                                          { evmPostSolm with
                                            accountMap := σ_grab_solm
                                            substate := A_grab_solm
                                            createdAccounts := cA_grab },
                                          ret) true := by
                                    simpa [hVatAddrGrab, hVowAddrGrab, hWadWordGrab] using
                                      hgrabCallSolmRaw
                                  cases zGrab
                                  · have hgrab :=
                                      endSkimGrabTailReverts_callFailedFor
                                        (σCall := σ_post_solm) (σLoc := σ_urns_solm)
                                        (I := I) (vatOut := vatOut) (urnOut := urnOut)
                                        (grabOut := ret) (evm := evmPostSolm)
                                        (evmGrab :=
                                          { evmPostSolm with
                                            accountMap := σ_grab_solm
                                            substate := A_grab_solm
                                            createdAccounts := cA_grab })
                                        hmapPostSolm hownerPostSolm hgrabCodeSolmNE
                                        (by simpa using hgrabCallSolm)
                                    have hbody :
                                        ExecTransitionBody config contract evmSolm
                                          (endSkimStore I) skimTransition.body
                                          .reverted := by
                                      exact endSkimBodyReverts_afterArtTailGrabReverted
                                        hprefixArt htailOk hgrab
                                    have rd7373Fail := rd7373
                                    simp at rd7373Fail
                                    exact
                                      (endSkimX_grabCallFailed rd7373Fail hretSize)
                                        |>.reEquivExecutionRevert hcode hdispatch hdecode
                                          hbody
                                  · let evmGrabEvm :=
                                      { evmPostEvm with
                                        accountMap := σ_grab
                                        substate := AGrab
                                        createdAccounts := cA_grab }
                                    let evmGrabSolm :=
                                      { evmPostSolm with
                                        accountMap := σ_grab_solm
                                        substate := A_grab_solm
                                        createdAccounts := cA_grab }
                                    have hStateGrab :
                                        EVMStateEquiv evmGrabEvm evmGrabSolm := by
                                      refine ⟨?_, ?_, ?_⟩
                                      · simpa [evmGrabEvm, evmGrabSolm] using
                                          hStatePost.executionEnv
                                      · simp [evmGrabEvm, evmGrabSolm]
                                      · simpa [evmGrabEvm, evmGrabSolm] using hAccountsGrab
                                    have rd7373Succ := rd7373
                                    simp at rd7373Succ
                                    obtain ⟨_, _, rd7391⟩ :=
                                      endSkimX_grabCallSucceeded rd7373Succ
                                    have hretEvm :=
                                      endSkimX_grabLogReturn
                                        (σCall := σ_post) (σLoc := σ_urns)
                                        (vatOut := vatOut) (urnOut := urnOut)
                                        (ret := ret) hperm hloVat rd7391
                                    have hgrab :=
                                      endSkimGrabTailReturns_successFor
                                        (σCall := σ_post_solm) (σLoc := σ_urns_solm)
                                        (I := I) (vatOut := vatOut) (urnOut := urnOut)
                                        (grabOut := ret) (evm := evmPostSolm)
                                        (evmGrab := evmGrabSolm)
                                        hmapPostSolm hownerPostSolm hgrabCodeSolmNE
                                        (by simpa [evmGrabSolm] using hgrabCallSolm)
                                    have hbody :
                                        ExecTransitionBody config contract evmSolm
                                          (endSkimStore I) skimTransition.body
                                          (.returned
                                            { contract := contract,
                                              locals :=
                                                endSkimStoreGrab σ_urns_solm I vatOut
                                                  urnOut }
                                            evmGrabSolm none) := by
                                      exact endSkimBodyReturns_afterArtTailGrabSuccess
                                        hprefixArt htailOk hgrab
                                    exact hretEvm.reEquivExecutionGenEVMStateEquiv
                                      (evm'_evm := evmGrabEvm)
                                      (evm'_solm := evmGrabSolm)
                                      hcode hdispatch hdecode hbody
                                      (by simp [evmGrabEvm])
                                      (by
                                        simpa [evmGrabEvm] using
                                          accountMapEquiv.refl σ_grab)
                                      hStateGrab
                                      (by
                                        simpa [skimTransition] using
                                          (returnEquiv.fallthrough
                                            (o := ByteArray.empty) (r := none)
                                            (t := []) (dvs := []) rfl
                                            (by native_decide) (by native_decide)))
                                · rw [not_lt] at hgrabDepthLt
                                  have hgrabDepthEq : I.depth = 1024 :=
                                    Fin.ext (by have := I.depth.isLt; omega)
                                  obtain ⟨_, _, rd7373⟩ :=
                                    endSkimX_grabCallDepthLimit
                                      (g := Sat256.ofUInt256 g) (σCall := σ_post)
                                      (σLoc := σ_urns) rdGrabReady hgrabDepthEq
                                  let A_grab :=
                                    (evmPostSolm.addAccessedAccount
                                      (EVM.address (endPackVatAddr σ_post_solm I))).substate
                                  have hgrabCallSolm :
                                      typedCallViaEVM config evmPostSolm
                                        (EVM.address (endPackVatAddr σ_post_solm I))
                                        "grab" 0
                                        [.fixedBytes bytes32Width (endBytes32ArgBytes I),
                                          .address (endSkimUrnAddr I),
                                          .address I.codeOwner,
                                          .address (endPackVowAddr σ_post_solm I),
                                          .int (-(Int.ofNat
                                            (endSkimWadWord σ_urns_solm I vatOut urnOut).toNat)),
                                          .int (-(Int.ofNat
                                            (endFreeUrnArtWord urnOut).toNat))]
                                        (false, { evmPostSolm with substate := A_grab },
                                          ByteArray.empty) true := by
                                    simpa [A_grab] using
                                      (callNotMade_depthLimit (cfg := config)
                                        (evm := evmPostSolm)
                                        (tgt :=
                                          EVM.address (endPackVatAddr σ_post_solm I))
                                        (name := "grab")
                                        (args :=
                                          [.fixedBytes bytes32Width (endBytes32ArgBytes I),
                                            .address (endSkimUrnAddr I),
                                            .address I.codeOwner,
                                            .address (endPackVowAddr σ_post_solm I),
                                            .int (-(Int.ofNat
                                              (endSkimWadWord σ_urns_solm I vatOut
                                                urnOut).toNat)),
                                            .int (-(Int.ofNat
                                              (endFreeUrnArtWord urnOut).toNat))])
                                        (callPerm := true)
                                        (endSkimGrabEncodeFor_eq σ_post_solm
                                          σ_urns_solm I vatOut urnOut hsz68 hloVat
                                          hwadLimitSolm hartLimit)
                                        (by simpa [evmPostSolm, endSkimPostGapState,
                                          storageStore_executionEnv,
                                          evmUrnsSolm, evmVatSolm, evmSolm, initState]
                                          using hgrabDepthEq))
                                  have hgrab :=
                                    endSkimGrabTailReverts_callFailedFor
                                      (σCall := σ_post_solm) (σLoc := σ_urns_solm)
                                      (I := I) (vatOut := vatOut) (urnOut := urnOut)
                                      (grabOut := ByteArray.empty) (evm := evmPostSolm)
                                      (evmGrab := { evmPostSolm with substate := A_grab })
                                      hmapPostSolm hownerPostSolm hgrabCodeSolmNE
                                      (by simpa using hgrabCallSolm)
                                  have hbody :
                                      ExecTransitionBody config contract evmSolm
                                        (endSkimStore I) skimTransition.body
                                        .reverted := by
                                    exact endSkimBodyReverts_afterArtTailGrabReverted
                                      hprefixArt htailOk hgrab
                                  exact (endSkimX_grabCallFailed rd7373 (by native_decide))
                                    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                            · have hartOverflow : 2 ^ 255 < (endFreeUrnArtWord urnOut).toNat :=
                                Nat.lt_of_not_ge hartLimit
                              have hwadLimitSolm :
                                  (endSkimWadWord σ_urns_solm I vatOut urnOut).toNat ≤
                                    2 ^ 255 := by
                                simpa [hTagCoupleUrns, endSkimWadWord, endSkimOweWord]
                                  using hwadLimit
                              have htail :=
                                endSkimTailReverts_intGuardArt evmUrnsSolm I
                                  σ_urns_solm vatOut urnOut hsz68 hTagLoadSolm
                                  hGapLoadSolm hfitOwe0 hfitOweSolm hfitGapSolm
                                  hwadLimitSolm hartOverflow
                              have hbody :
                                  ExecTransitionBody config contract evmSolm (endSkimStore I)
                                    skimTransition.body .reverted := by
                                exact endSkimBodyReverts_afterArtTailReverted hprefixArt htail
                              exact
                                (endSkimX_gapStoreIntGuardArtOverflow
                                  (g := Sat256.ofUInt256 g) hperm hsz68 hloVat hwadLimit
                                  hartOverflow rd7150)
                                  |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                          · have hwadOverflow :
                                2 ^ 255 < (endSkimWadWord σ_urns I vatOut urnOut).toNat :=
                              Nat.lt_of_not_ge hwadLimit
                            have hwadOverflowSolm :
                                2 ^ 255 <
                                  (endSkimWadWord σ_urns_solm I vatOut urnOut).toNat := by
                              simpa [hTagCoupleUrns, endSkimWadWord, endSkimOweWord]
                                using hwadOverflow
                            have htail :=
                              endSkimTailReverts_intGuardWad evmUrnsSolm I
                                σ_urns_solm vatOut urnOut hsz68 hTagLoadSolm
                                hGapLoadSolm hfitOwe0 hfitOweSolm hfitGapSolm
                                hwadOverflowSolm
                            have hbody :
                                ExecTransitionBody config contract evmSolm (endSkimStore I)
                                  skimTransition.body .reverted := by
                              exact endSkimBodyReverts_afterArtTailReverted hprefixArt htail
                            exact
                              (endSkimX_gapStoreIntGuardWadOverflow
                                (g := Sat256.ofUInt256 g) hperm hsz68 hloVat
                                hwadOverflow rd7150)
                                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · rw [not_lt] at hdepthLt
          have hdepthEq : I.depth = 1024 :=
            Fin.ext (by have := I.depth.isLt; omega)
          obtain ⟨_, _, rd6876⟩ :=
            endSkimX_vatIlksCallDepthLimit
              (g := Sat256.ofUInt256 g) hcallReady hdepthEq
          let A_vat :=
            (evmSolm.addAccessedAccount (EVM.address (endPackVatAddr σ_solm I))).substate
          have hcallSolm :
              typedCallViaEVM config evmSolm
              (EVM.address (endPackVatAddr σ_solm I)) "vatIlks" 0
              [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
              (false, { evmSolm with substate := A_vat }, ByteArray.empty) true := by
            simpa [evmSolm, A_vat] using
              (callNotMade_depthLimit (cfg := config) (evm := evmSolm)
              (tgt := EVM.address (endPackVatAddr σ_solm I)) (name := "vatIlks")
              (args := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
              (callPerm := true)
              (endSkimVatIlksEncode_eq I hsz68)
              (by simpa [evmSolm, initState] using hdepthEq))
          have hbody :
              ExecTransitionBody config contract evmSolm (endSkimStore I)
                skimTransition.body .reverted := by
            simpa [evmSolm] using
              endSkimBodyReverts_vatIlksCallFailed
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                (A := A) (I := I) (g := g)
                (evmVat := { evmSolm with substate := A_vat })
                (out := ByteArray.empty)
                hwv hsz68 htagSolmNE hvatCodeSolmNE
                (by simpa [evmSolm] using hcallSolm)
          exact (endSkimX_vatIlksCallFailed (g := Sat256.ofUInt256 g) rd6876
            (by native_decide))
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · exact endSkimBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.End
