import Benchmarks.Dss.End.Dispatch
import Benchmarks.Dss.End.Cage
import Benchmarks.Dss.End.Flow

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `cage(bytes32)` transition -/

abbrev endCageIlkConcreteSelector : ByteArray := selectorBytes 0xe2 0x70 0x2f 0xdc

abbrev endCageIlkIlkWord (I : ExecutionEnv) : UInt256 := endBytes32ArgWord I

abbrev endCageIlkIlkValue (I : ExecutionEnv) : Value := endBytes32ArgValue I

abbrev endCageIlkStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "ilk" (endCageIlkIlkValue I)

abbrev endCageIlkIlkKey (I : ExecutionEnv) : KeyValue := endBytes32ArgKey I

abbrev endCageIlkTagEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "tag", steps := [.mindex (endCageIlkIlkKey I)] }

abbrev endCageIlkTagSlot (I : ExecutionEnv) : UInt256 := tagSlot (endCageIlkIlkKey I)

abbrev endCageIlkTagWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (endCageIlkTagSlot I) σ I

abbrev endCageIlkLiveWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord ⟨8⟩ σ I

abbrev endCageIlkLiveEvaledRef : EvaledStorageRef :=
  { base := "live", steps := [] }

abbrev endCageIlkEntryPc : UInt256 := ⟨1171⟩
abbrev endCageIlkReturnPc : UInt256 := ⟨562⟩
abbrev endCageIlkDecodedPc : UInt256 := ⟨1193⟩
abbrev endCageIlkBodyPc : UInt256 := ⟨8832⟩
abbrev endCageIlkTagDefinedRawWord : UInt256 :=
  ⟨0x456e642f7461672d696c6b2d616c72656164792d646566696e65640000000000⟩

abbrev endCageIlkStoreVatIlk (I : ExecutionEnv) (out : ByteArray) : Store :=
  (endCageIlkStore I).insert "vatIlk"
    (.tuple [.int (Int.ofNat (endFlowVatIlkArtWord out).toNat),
      .int (Int.ofNat (endFlowVatIlkRateWord out).toNat),
      .int (Int.ofNat (endFlowVatIlkSpotWord out).toNat),
      .int (Int.ofNat (endFlowVatIlkLineWord out).toNat),
      .int (Int.ofNat (endFlowVatIlkDustWord out).toNat)])

abbrev endCageIlkArtSlot (I : ExecutionEnv) : UInt256 := ArtSlot (endCageIlkIlkKey I)

abbrev endCageIlkArtEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "Art", steps := [.mindex (endCageIlkIlkKey I)] }

abbrev endCageIlkSpotIlkPipWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

abbrev endCageIlkSpotIlkPipAddr (out : ByteArray) : AccountAddress :=
  AccountAddress.ofNat (endCageIlkSpotIlkPipWord out).toNat

abbrev endCageIlkSpotIlkMatWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 32 64))

abbrev endCageIlkStoreSpotIlk (I : ExecutionEnv) (vatOut spotOut : ByteArray) : Store :=
  (endCageIlkStoreVatIlk I vatOut).insert "spotIlk"
    (.tuple [.address (endCageIlkSpotIlkPipAddr spotOut),
      .int (Int.ofNat (endCageIlkSpotIlkMatWord spotOut).toNat)])

abbrev endCageIlkStorePip (I : ExecutionEnv) (vatOut spotOut : ByteArray) : Store :=
  (endCageIlkStoreSpotIlk I vatOut spotOut).insert "pip"
    (.address (endCageIlkSpotIlkPipAddr spotOut))

abbrev endCageIlkReturnWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

abbrev endCageIlkReadBytes (out : ByteArray) : List UInt8 :=
  (out.toList.drop 0).take 32

abbrev endCageIlkStorePar (I : ExecutionEnv) (vatOut spotOut parOut : ByteArray) : Store :=
  (endCageIlkStorePip I vatOut spotOut).insert "parV"
    (.int (Int.ofNat (endCageIlkReturnWord parOut).toNat))

abbrev endCageIlkStoreRead (I : ExecutionEnv)
    (vatOut spotOut parOut readOut : ByteArray) : Store :=
  (endCageIlkStorePar I vatOut spotOut parOut).insert "pipRead"
    (.fixedBytes bytes32Width (endCageIlkReadBytes readOut))

abbrev endCageIlkWdivProductWord (parOut : ByteArray) : UInt256 :=
  endCageIlkReturnWord parOut * endWadWord

abbrev endCageIlkTagVWord (parOut readOut : ByteArray) : UInt256 :=
  UInt256.div (endCageIlkWdivProductWord parOut) (endCageIlkReturnWord readOut)

abbrev endCageIlkPipCallWord (spotOut : ByteArray) : UInt256 :=
  UInt256.land (endCageIlkSpotIlkPipWord spotOut) solcAddrMask

abbrev endCageIlkParSelectorWord : UInt256 := ⟨0x495d32cb⟩
abbrev endCageIlkReadSelectorRaw : UInt256 := ⟨0x15f789a9⟩
abbrev endCageIlkReadSelectorWord : UInt256 := ⟨0x57de26a4⟩
abbrev endCageIlkNoArgInSize : UInt256 := ⟨4⟩
abbrev endCageIlkNoArgOutSize : UInt256 := ⟨32⟩
abbrev endCageIlkNoArgEndPtr : UInt256 := ⟨132⟩

abbrev endCageIlkCageIlkLogTopic : UInt256 :=
  ⟨0x4a9efa0a0e3f548761a6924fe06ac5cb94ecdbc08b10d855bbcc04e37c4910db⟩

abbrev endCageIlkStoreTagV (I : ExecutionEnv)
    (vatOut spotOut parOut readOut : ByteArray) : Store :=
  (endCageIlkStoreRead I vatOut spotOut parOut readOut).insert "tagV"
    (.int (Int.ofNat (endCageIlkTagVWord parOut readOut).toNat))

abbrev endCageIlkPostArtState (evm : EVM.State) (I : ExecutionEnv)
    (vatOut : ByteArray) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (endCageIlkArtSlot I)
    (endFlowVatIlkArtWord vatOut)

abbrev endCageIlkPostArtAccountMap (σ : AccountMap) (I : ExecutionEnv)
    (vatOut : ByteArray) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (endCageIlkArtSlot I) (endFlowVatIlkArtWord vatOut)

abbrev endCageIlkSpotWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endAddressReturnWord ⟨6⟩ σ I

abbrev endCageIlkPostTagState (evm : EVM.State) (I : ExecutionEnv)
    (tagV : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (endCageIlkTagSlot I) tagV

abbrev endCageIlkPostTagAccountMap (σ : AccountMap) (I : ExecutionEnv)
    (tagV : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (endCageIlkTagSlot I) tagV

noncomputable def endCageIlkTagHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (endCageIlkIlkWord I) ⟨12⟩ solcFreePtrMem

noncomputable def endCageIlkVatIlksCalldataMem (I : ExecutionEnv) : ByteArray :=
  endFlowVatIlksCalldataMem I (endCageIlkTagHashMem I)

noncomputable def endCageIlkVatIlksPostCallMem (I : ExecutionEnv) (out : ByteArray) :
    ByteArray :=
  out.write 0 (endCageIlkVatIlksCalldataMem I) endFlowVatIlksOutPtr.toNat
    (min endFlowVatIlksOutSize.toNat out.size)

noncomputable def endCageIlkArtHashMem (I : ExecutionEnv) (vatOut : ByteArray) :
    ByteArray :=
  twoWordHashMem (endCageIlkIlkWord I) ⟨14⟩ (endCageIlkVatIlksPostCallMem I vatOut)

noncomputable def endCageIlkSpotIlksCalldataMem (I : ExecutionEnv) (vatOut : ByteArray) :
    ByteArray :=
  endFlowVatIlksCalldataMem I (endCageIlkArtHashMem I vatOut)

noncomputable def endCageIlkSpotIlksPostCallMem (I : ExecutionEnv)
    (vatOut spotOut : ByteArray) : ByteArray :=
  spotOut.write 0 (endCageIlkSpotIlksCalldataMem I vatOut)
    endFlowVatIlksOutPtr.toNat
    (min (⟨64⟩ : UInt256) (UInt256.ofNat spotOut.size)).toNat

noncomputable def endCageIlkNoArgCalldataMem (selectorShifted mem : ByteArray) :
    ByteArray :=
  selectorShifted.write 0 mem endFlowVatIlksOutPtr.toNat 32

noncomputable def endCageIlkParCalldataMem (I : ExecutionEnv)
    (vatOut spotOut : ByteArray) : ByteArray :=
  endCageIlkNoArgCalldataMem
    (UInt256.shiftLeft endCageIlkParSelectorWord ⟨224⟩).toByteArray
    (endCageIlkSpotIlksPostCallMem I vatOut spotOut)

noncomputable def endCageIlkNoArgPostCallMem (selectorShifted mem out : ByteArray) :
    ByteArray :=
  out.write 0 (endCageIlkNoArgCalldataMem selectorShifted mem)
    endFlowVatIlksOutPtr.toNat
    (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat

noncomputable def endCageIlkParPostCallMem (I : ExecutionEnv)
    (vatOut spotOut parOut : ByteArray) : ByteArray :=
  endCageIlkNoArgPostCallMem
    (UInt256.shiftLeft endCageIlkParSelectorWord ⟨224⟩).toByteArray
    (endCageIlkSpotIlksPostCallMem I vatOut spotOut) parOut

noncomputable def endCageIlkReadCalldataMem (I : ExecutionEnv)
    (vatOut spotOut parOut : ByteArray) : ByteArray :=
  endCageIlkNoArgCalldataMem
    (UInt256.shiftLeft endCageIlkReadSelectorRaw ⟨226⟩).toByteArray
    (endCageIlkParPostCallMem I vatOut spotOut parOut)

noncomputable def endCageIlkReadPostCallMem (I : ExecutionEnv)
    (vatOut spotOut parOut readOut : ByteArray) : ByteArray :=
  endCageIlkNoArgPostCallMem
    (UInt256.shiftLeft endCageIlkReadSelectorRaw ⟨226⟩).toByteArray
    (endCageIlkParPostCallMem I vatOut spotOut parOut) readOut

theorem endCageIlkVatIlksPostCallMem_size_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 160 ≤ out.size) :
    (endCageIlkVatIlksPostCallMem I out).size = 288 := by
  unfold endCageIlkVatIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    show endFlowVatIlksOutSize.toNat = 160 by native_decide]
  rw [Nat.min_eq_left hlo]
  rw [write_eq_gen_extend out (endCageIlkVatIlksCalldataMem I) 128 160
    (by omega) (by omega)
    (by
      rw [endCageIlkVatIlksCalldataMem, endCageIlkTagHashMem]
      rw [endFlowVatIlksCalldataMem_size I
        (twoWordHashMem_size_96 (endCageIlkIlkWord I) ⟨12⟩ solcFreePtrMem_size)]
      omega)
    (by
      rw [endCageIlkVatIlksCalldataMem, endCageIlkTagHashMem]
      rw [endFlowVatIlksCalldataMem_size I
        (twoWordHashMem_size_96 (endCageIlkIlkWord I) ⟨12⟩ solcFreePtrMem_size)]
      omega)]
  rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
  rw [endCageIlkVatIlksCalldataMem, endCageIlkTagHashMem]
  rw [endFlowVatIlksCalldataMem_size I
    (twoWordHashMem_size_96 (endCageIlkIlkWord I) ⟨12⟩ solcFreePtrMem_size)]
  omega

theorem endCageIlkVatIlksPostCallMem_read64_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 160 ≤ out.size) :
    (endCageIlkVatIlksPostCallMem I out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endCageIlkVatIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    show endFlowVatIlksOutSize.toNat = 160 by native_decide]
  rw [Nat.min_eq_left hlo]
  rw [write_read_below_gen_extend out (endCageIlkVatIlksCalldataMem I)
    128 160 64 (by omega) (by omega)
    (by
      rw [endCageIlkVatIlksCalldataMem, endCageIlkTagHashMem]
      rw [endFlowVatIlksCalldataMem_size I
        (twoWordHashMem_size_96 (endCageIlkIlkWord I) ⟨12⟩ solcFreePtrMem_size)]
      omega)
    (by omega)]
  rw [endCageIlkVatIlksCalldataMem, endCageIlkTagHashMem]
  exact endFlowVatIlksCalldataMem_read64 I
    (twoWordHashMem_size_96 (endCageIlkIlkWord I) ⟨12⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 (endCageIlkIlkWord I) ⟨12⟩ solcFreePtrMem_size
      solcFreePtrMem_read64)

theorem endCageIlkVatIlksPostCallMem_mload64_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 160 ≤ out.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (endCageIlkVatIlksPostCallMem I out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((endCageIlkVatIlksPostCallMem I out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [endCageIlkVatIlksPostCallMem_size_long I out hlo]; decide)
    (by decide)
    (endCageIlkVatIlksPostCallMem_read64_long I out hlo)

theorem endCageIlkVatIlksPostCallMem_size_gt64 (I : ExecutionEnv) (out : ByteArray) :
    64 < (endCageIlkVatIlksPostCallMem I out).size := by
  unfold endCageIlkVatIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    show endFlowVatIlksOutSize.toNat = 160 by native_decide]
  by_cases hlen0 : min 160 out.size = 0
  · rw [hlen0, byteArray_write_len_zero]
    rw [endCageIlkVatIlksCalldataMem, endCageIlkTagHashMem]
    rw [endFlowVatIlksCalldataMem_size I
      (twoWordHashMem_size_96 (endCageIlkIlkWord I) ⟨12⟩ solcFreePtrMem_size)]
    omega
  · by_cases hext : (endCageIlkVatIlksCalldataMem I).size < 128 + min 160 out.size
    · rw [write_eq_gen_extend out (endCageIlkVatIlksCalldataMem I)
        128 (min 160 out.size) hlen0 (Nat.min_le_right _ _)
        (by
          rw [endCageIlkVatIlksCalldataMem, endCageIlkTagHashMem]
          rw [endFlowVatIlksCalldataMem_size I
            (twoWordHashMem_size_96 (endCageIlkIlkWord I) ⟨12⟩ solcFreePtrMem_size)]
          omega)
        hext]
      have hbaseSize : (endCageIlkVatIlksCalldataMem I).size = 164 := by
        rw [endCageIlkVatIlksCalldataMem, endCageIlkTagHashMem]
        exact endFlowVatIlksCalldataMem_size I
          (twoWordHashMem_size_96 (endCageIlkIlkWord I) ⟨12⟩ solcFreePtrMem_size)
      have hprefix : ((endCageIlkVatIlksCalldataMem I).extract 0 128).size = 128 := by
        rw [ByteArray.size_extract, hbaseSize]
        omega
      have hsrc : (out.extract 0 (min 160 out.size)).size = min 160 out.size := by
        rw [ByteArray.size_extract]
        omega
      rw [ByteArray.size_append, hprefix, hsrc]
      have hleout : min 160 out.size ≤ out.size := Nat.min_le_right _ _
      omega
    · have hin : 128 + min 160 out.size ≤ (endCageIlkVatIlksCalldataMem I).size := by
        omega
      rw [write_eq_gen out (endCageIlkVatIlksCalldataMem I)
        128 (min 160 out.size) hlen0 (Nat.min_le_right _ _) hin]
      have hbaseSize : (endCageIlkVatIlksCalldataMem I).size = 164 := by
        rw [endCageIlkVatIlksCalldataMem, endCageIlkTagHashMem]
        exact endFlowVatIlksCalldataMem_size I
          (twoWordHashMem_size_96 (endCageIlkIlkWord I) ⟨12⟩ solcFreePtrMem_size)
      have hprefix : ((endCageIlkVatIlksCalldataMem I).extract 0 128).size = 128 := by
        rw [ByteArray.size_extract, hbaseSize]
        omega
      have hsrc : (out.extract 0 (min 160 out.size)).size = min 160 out.size := by
        rw [ByteArray.size_extract]
        omega
      have htail :
          ((endCageIlkVatIlksCalldataMem I).extract
            (128 + min 160 out.size) (endCageIlkVatIlksCalldataMem I).size).size =
              164 - (128 + min 160 out.size) := by
        rw [ByteArray.size_extract, hbaseSize]
        omega
      rw [ByteArray.size_append, ByteArray.size_append, hprefix, hsrc, htail]
      have hleout : min 160 out.size ≤ out.size := Nat.min_le_right _ _
      omega

theorem endCageIlkVatIlksPostCallMem_read64 (I : ExecutionEnv) (out : ByteArray) :
    (endCageIlkVatIlksPostCallMem I out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endCageIlkVatIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    show endFlowVatIlksOutSize.toNat = 160 by native_decide]
  by_cases hlen0 : min 160 out.size = 0
  · rw [hlen0, byteArray_write_len_zero]
    rw [endCageIlkVatIlksCalldataMem, endCageIlkTagHashMem]
    exact endFlowVatIlksCalldataMem_read64 I
      (twoWordHashMem_size_96 (endCageIlkIlkWord I) ⟨12⟩ solcFreePtrMem_size)
      (twoWordHashMem_read64 (endCageIlkIlkWord I) ⟨12⟩ solcFreePtrMem_size
        solcFreePtrMem_read64)
  · rw [write_read_below_gen_extend out (endCageIlkVatIlksCalldataMem I)
      128 (min 160 out.size) 64 hlen0 (Nat.min_le_right _ _)
      (by
        rw [endCageIlkVatIlksCalldataMem, endCageIlkTagHashMem]
        rw [endFlowVatIlksCalldataMem_size I
          (twoWordHashMem_size_96 (endCageIlkIlkWord I) ⟨12⟩ solcFreePtrMem_size)]
        omega)
      (by native_decide)]
    rw [endCageIlkVatIlksCalldataMem, endCageIlkTagHashMem]
    exact endFlowVatIlksCalldataMem_read64 I
      (twoWordHashMem_size_96 (endCageIlkIlkWord I) ⟨12⟩ solcFreePtrMem_size)
      (twoWordHashMem_read64 (endCageIlkIlkWord I) ⟨12⟩ solcFreePtrMem_size
        solcFreePtrMem_read64)

theorem endCageIlkVatIlksPostCallMem_mload64 (I : ExecutionEnv) (out : ByteArray) :
    (if (⟨64⟩ : UInt256).toNat ≥ (endCageIlkVatIlksPostCallMem I out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((endCageIlkVatIlksPostCallMem I out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by exact endCageIlkVatIlksPostCallMem_size_gt64 I out)
    (by decide)
    (endCageIlkVatIlksPostCallMem_read64 I out)

theorem endCageIlkVatIlksPostCallMem_read128_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 160 ≤ out.size) :
    (endCageIlkVatIlksPostCallMem I out).readWithPadding 128 32 = out.extract 0 32 := by
  unfold endCageIlkVatIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    show endFlowVatIlksOutSize.toNat = 160 by native_decide]
  rw [Nat.min_eq_left hlo]
  rw [write_eq_gen_extend out (endCageIlkVatIlksCalldataMem I) 128 160
    (by omega) (by omega)
    (by
      rw [endCageIlkVatIlksCalldataMem, endCageIlkTagHashMem]
      rw [endFlowVatIlksCalldataMem_size I
        (twoWordHashMem_size_96 (endCageIlkIlkWord I) ⟨12⟩ solcFreePtrMem_size)]
      omega)
    (by
      rw [endCageIlkVatIlksCalldataMem, endCageIlkTagHashMem]
      rw [endFlowVatIlksCalldataMem_size I
        (twoWordHashMem_size_96 (endCageIlkIlkWord I) ⟨12⟩ solcFreePtrMem_size)]
      omega)]
  have hprefix : ((endCageIlkVatIlksCalldataMem I).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract]
    rw [endCageIlkVatIlksCalldataMem, endCageIlkTagHashMem]
    rw [endFlowVatIlksCalldataMem_size I
      (twoWordHashMem_size_96 (endCageIlkIlkWord I) ⟨12⟩ solcFreePtrMem_size)]
    omega
  have hsrc : (out.extract 0 160).size = 160 := by
    rw [ByteArray.size_extract]
    omega
  have hmemSize :
      ((endCageIlkVatIlksCalldataMem I).extract 0 128 ++ out.extract 0 160).size =
        288 := by
    rw [ByteArray.size_append, hprefix, hsrc]
  have hreadIn :
      128 + 32 ≤ ((endCageIlkVatIlksCalldataMem I).extract 0 128 ++
        out.extract 0 160).size := by
    rw [hmemSize]
    norm_num
  rw [readWithPadding_eq_extract _ 128 hreadIn]
  rw [show 128 + 32 = 160 by omega]
  rw [extract_append_right_window _ _ 128 160 (by omega)]
  rw [hprefix]
  norm_num
  rw [extract_extract_BA]
  norm_num

theorem endCageIlkVatIlksPostCallMem_mload128_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 160 ≤ out.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (endCageIlkVatIlksPostCallMem I out).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((endCageIlkVatIlksPostCallMem I out).readWithPadding
          (⟨128⟩ : UInt256).toNat 32))) =
      endFlowVatIlkArtWord out := by
  unfold endFlowVatIlkArtWord
  rw [if_neg]
  · change UInt256.ofNat
      (fromByteArrayBigEndian ((endCageIlkVatIlksPostCallMem I out).readWithPadding
        128 32)) = UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))
    rw [endCageIlkVatIlksPostCallMem_read128_long I out hlo]
  · exact not_or.mpr
      ⟨by rw [endCageIlkVatIlksPostCallMem_size_long I out hlo]; decide, by native_decide⟩

theorem endCageIlkArtHashMem_size_long (I : ExecutionEnv) (vatOut : ByteArray)
    (hlo : 160 ≤ vatOut.size) :
    (endCageIlkArtHashMem I vatOut).size = 288 := by
  unfold endCageIlkArtHashMem
  rw [endFlow_twoWordHashMem_size_of_ge64 (endCageIlkIlkWord I) ⟨14⟩
    (by rw [endCageIlkVatIlksPostCallMem_size_long I vatOut hlo]; omega)]
  exact endCageIlkVatIlksPostCallMem_size_long I vatOut hlo

theorem endCageIlkArtHashMem_read64_long (I : ExecutionEnv) (vatOut : ByteArray)
    (hlo : 160 ≤ vatOut.size) :
    (endCageIlkArtHashMem I vatOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endCageIlkArtHashMem
  have hmem64 : 64 ≤ (endCageIlkVatIlksPostCallMem I vatOut).size := by
    rw [endCageIlkVatIlksPostCallMem_size_long I vatOut hlo]
    omega
  have hword0 :
      (wordAt0Mem (endCageIlkIlkWord I) (endCageIlkVatIlksPostCallMem I vatOut)).size =
        (endCageIlkVatIlksPostCallMem I vatOut).size :=
    endFlow_wordAt0Mem_size_of_ge64 (endCageIlkIlkWord I) hmem64
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [hword0, endCageIlkVatIlksPostCallMem_size_long I vatOut hlo]; omega)
      (by omega)
      (by rw [hword0, endCageIlkVatIlksPostCallMem_size_long I vatOut hlo]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by omega) (by omega)
      (by rw [endCageIlkVatIlksPostCallMem_size_long I vatOut hlo]; omega)]
  exact endCageIlkVatIlksPostCallMem_read64_long I vatOut hlo

theorem endCageIlkSpotIlksCalldataMem_size_long (I : ExecutionEnv) (vatOut : ByteArray)
    (hlo : 160 ≤ vatOut.size) :
    (endCageIlkSpotIlksCalldataMem I vatOut).size = 288 := by
  have hhashSize := endCageIlkArtHashMem_size_long I vatOut hlo
  have hselectorSize :
      (endFlowVatIlksSelectorMem (endCageIlkArtHashMem I vatOut)).size = 288 := by
    unfold endFlowVatIlksSelectorMem
    exact toByteArray_write32_size_of_le (endCageIlkArtHashMem I vatOut)
      endFlowVatIlksSelectorShifted 128 288 288 hhashSize (by omega) (by omega)
  unfold endCageIlkSpotIlksCalldataMem endFlowVatIlksCalldataMem endFlowVatIlksArg0Mem
  exact toByteArray_write32_size_of_le
    (endFlowVatIlksSelectorMem (endCageIlkArtHashMem I vatOut))
    (endFlowIlkWord I) 132 288 288 hselectorSize (by omega) (by omega)

theorem endCageIlkSpotIlksCalldataMem_read64_long (I : ExecutionEnv) (vatOut : ByteArray)
    (hlo : 160 ≤ vatOut.size) :
    (endCageIlkSpotIlksCalldataMem I vatOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hhashSize := endCageIlkArtHashMem_size_long I vatOut hlo
  have hselectorSize :
      (endFlowVatIlksSelectorMem (endCageIlkArtHashMem I vatOut)).size = 288 := by
    unfold endFlowVatIlksSelectorMem
    exact toByteArray_write32_size_of_le (endCageIlkArtHashMem I vatOut)
      endFlowVatIlksSelectorShifted 128 288 288 hhashSize (by omega) (by omega)
  unfold endCageIlkSpotIlksCalldataMem endFlowVatIlksCalldataMem endFlowVatIlksArg0Mem
  rw [show (endFlowVatIlksOutPtr + ⟨4⟩).toNat = 132 by native_decide]
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [hselectorSize]; omega) (by omega)]
  unfold endFlowVatIlksSelectorMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide]
  rw [toByteArray_write_read_below_of_gap endFlowVatIlksSelectorShifted
    (endCageIlkArtHashMem I vatOut) 128 64
    (by rw [hhashSize]; norm_num) (by omega) (by rw [hhashSize]; norm_num)]
  exact endCageIlkArtHashMem_read64_long I vatOut hlo

theorem endCageIlkSpotIlksCalldataMem_read128_4
    (I : ExecutionEnv) (vatOut : ByteArray) (hlo : 160 ≤ vatOut.size) :
    (endCageIlkSpotIlksCalldataMem I vatOut).readWithPadding 128 4 = ilksSelector := by
  have hhashSize := endCageIlkArtHashMem_size_long I vatOut hlo
  have hselectorSize :
      (endFlowVatIlksSelectorMem (endCageIlkArtHashMem I vatOut)).size = 288 := by
    unfold endFlowVatIlksSelectorMem
    exact toByteArray_write32_size_of_le (endCageIlkArtHashMem I vatOut)
      endFlowVatIlksSelectorShifted 128 288 288 hhashSize (by omega) (by omega)
  unfold endCageIlkSpotIlksCalldataMem endFlowVatIlksCalldataMem endFlowVatIlksArg0Mem
  rw [show (endFlowVatIlksOutPtr + ⟨4⟩).toNat = 132 by native_decide]
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by rw [hselectorSize]; omega) (by omega) (by rw [hselectorSize]; omega)
    (by omega) (by norm_num)]
  unfold endFlowVatIlksSelectorMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide]
  rw [write32_read_prefix_len _ _ 128 4 (by rw [toByteArray_size])
    (by rw [hhashSize]; omega) (by omega) (by omega) (by norm_num)]
  unfold endFlowVatIlksSelectorShifted ilksSelector selectorBytes
  native_decide

theorem endCageIlkSpotIlksCalldataMem_read132_32
    (I : ExecutionEnv) (vatOut : ByteArray) (hlo : 160 ≤ vatOut.size) :
    (endCageIlkSpotIlksCalldataMem I vatOut).readWithPadding 132 32 =
      (endFlowIlkWord I).toByteArray := by
  have hhashSize := endCageIlkArtHashMem_size_long I vatOut hlo
  have hselectorSize :
      (endFlowVatIlksSelectorMem (endCageIlkArtHashMem I vatOut)).size = 288 := by
    unfold endFlowVatIlksSelectorMem
    exact toByteArray_write32_size_of_le (endCageIlkArtHashMem I vatOut)
      endFlowVatIlksSelectorShifted 128 288 288 hhashSize (by omega) (by omega)
  unfold endCageIlkSpotIlksCalldataMem endFlowVatIlksCalldataMem endFlowVatIlksArg0Mem
  rw [show (endFlowVatIlksOutPtr + ⟨4⟩).toNat = 132 by native_decide]
  rw [write32_read_back _ _ 132 (by rw [toByteArray_size])
    (by rw [hselectorSize]; omega)]
  rw [toByteArray_extract_all]

theorem endCageIlkSpotIlksCalldataMem_read128_36
    (I : ExecutionEnv) (vatOut : ByteArray) (hlo : 160 ≤ vatOut.size) :
    (endCageIlkSpotIlksCalldataMem I vatOut).readWithPadding 128 36 =
      ilksSelector ++ (endFlowIlkWord I).toByteArray := by
  have hsize := endCageIlkSpotIlksCalldataMem_size_long I vatOut hlo
  rw [show 36 = 4 + 32 from rfl,
    byteArray_readWithPadding_split (endCageIlkSpotIlksCalldataMem I vatOut) 128 4 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  rw [endCageIlkSpotIlksCalldataMem_read128_4 I vatOut hlo,
    endCageIlkSpotIlksCalldataMem_read132_32 I vatOut hlo]

theorem endCageIlkSpotIlksCalldataMem_mload64_long (I : ExecutionEnv) (vatOut : ByteArray)
    (hlo : 160 ≤ vatOut.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (endCageIlkSpotIlksCalldataMem I vatOut).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((endCageIlkSpotIlksCalldataMem I vatOut).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [endCageIlkSpotIlksCalldataMem_size_long I vatOut hlo]; decide)
    (by decide)
    (endCageIlkSpotIlksCalldataMem_read64_long I vatOut hlo)

theorem endCageIlkSpotIlksWriteLen_eq {out : ByteArray}
    (hout : out.size < UInt256.size) :
    (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = min 64 out.size := by
  by_cases hle : 64 ≤ out.size
  · rw [Nat.min_eq_left hle]
    exact umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hle hout
  · have hlt : out.size < 64 := by omega
    rw [Nat.min_eq_right (by omega : out.size ≤ 64)]
    exact umin_ofNat_right_toNat_of_lt (c := 64) (n := out.size) (by decide) hlt hout

theorem endCageIlkSpotIlksPostCallMem_size (I : ExecutionEnv)
    (vatOut spotOut : ByteArray) (hvat : 160 ≤ vatOut.size)
    (hout : spotOut.size < UInt256.size) :
    (endCageIlkSpotIlksPostCallMem I vatOut spotOut).size = 288 := by
  unfold endCageIlkSpotIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    endCageIlkSpotIlksWriteLen_eq hout]
  by_cases hlen0 : min 64 spotOut.size = 0
  · rw [hlen0, byteArray_write_len_zero, endCageIlkSpotIlksCalldataMem_size_long I vatOut hvat]
  · rw [write_eq_gen spotOut (endCageIlkSpotIlksCalldataMem I vatOut)
      128 (min 64 spotOut.size) hlen0 (Nat.min_le_right _ _)
      (by rw [endCageIlkSpotIlksCalldataMem_size_long I vatOut hvat]; omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract,
      endCageIlkSpotIlksCalldataMem_size_long I vatOut hvat]
    have hleout : min 64 spotOut.size ≤ spotOut.size := Nat.min_le_right _ _
    omega

theorem endCageIlkSpotIlksPostCallMem_read64 (I : ExecutionEnv)
    (vatOut spotOut : ByteArray) (hvat : 160 ≤ vatOut.size)
    (hout : spotOut.size < UInt256.size) :
    (endCageIlkSpotIlksPostCallMem I vatOut spotOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endCageIlkSpotIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    endCageIlkSpotIlksWriteLen_eq hout]
  by_cases hlen0 : min 64 spotOut.size = 0
  · rw [hlen0, byteArray_write_len_zero]
    exact endCageIlkSpotIlksCalldataMem_read64_long I vatOut hvat
  · rw [write_read_below_gen spotOut (endCageIlkSpotIlksCalldataMem I vatOut)
      128 (min 64 spotOut.size) 64 hlen0 (Nat.min_le_right _ _)
      (by rw [endCageIlkSpotIlksCalldataMem_size_long I vatOut hvat]; omega)
      (by native_decide)]
    exact endCageIlkSpotIlksCalldataMem_read64_long I vatOut hvat

theorem endCageIlkSpotIlksPostCallMem_read128 (I : ExecutionEnv)
    (vatOut spotOut : ByteArray) (hvat : 160 ≤ vatOut.size)
    (hout : spotOut.size < UInt256.size) (hlo : 64 ≤ spotOut.size) :
    (endCageIlkSpotIlksPostCallMem I vatOut spotOut).readWithPadding 128 32 =
      spotOut.extract 0 32 := by
  unfold endCageIlkSpotIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    endCageIlkSpotIlksWriteLen_eq hout, show min 64 spotOut.size = 64 from Nat.min_eq_left hlo]
  rw [write_eq_gen spotOut (endCageIlkSpotIlksCalldataMem I vatOut) 128 64
    (by decide) (by omega)
    (by rw [endCageIlkSpotIlksCalldataMem_size_long I vatOut hvat]; omega)]
  rw [readWithPadding_eq_extract _ 128 (by
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract,
      endCageIlkSpotIlksCalldataMem_size_long I vatOut hvat]
    omega)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
      endCageIlkSpotIlksCalldataMem_size_long I vatOut hvat]
    omega)]
  rw [extract_append_right_window _ _ _ _ (by rw [ByteArray.size_extract]; omega)]
  rw [ByteArray.size_extract]
  rw [show min 128 (endCageIlkSpotIlksCalldataMem I vatOut).size - 0 = 128 by
    rw [endCageIlkSpotIlksCalldataMem_size_long I vatOut hvat]
    omega]
  rw [show 128 - 128 = 0 by omega, show 160 - 128 = 32 by omega]
  rw [extract_extract_BA]
  rw [show 0 + 0 = 0 by omega, show min (0 + 32) 64 = 32 by omega]

theorem endCageIlkSpotIlksPostCallMem_mload64 (I : ExecutionEnv)
    (vatOut spotOut : ByteArray) (hvat : 160 ≤ vatOut.size)
    (hout : spotOut.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (endCageIlkSpotIlksPostCallMem I vatOut spotOut).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((endCageIlkSpotIlksPostCallMem I vatOut spotOut).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [endCageIlkSpotIlksPostCallMem_size I vatOut spotOut hvat hout]; decide)
    (by decide)
    (endCageIlkSpotIlksPostCallMem_read64 I vatOut spotOut hvat hout)

theorem endCageIlkSpotIlksPostCallMem_mload128 (I : ExecutionEnv)
    (vatOut spotOut : ByteArray) (hvat : 160 ≤ vatOut.size)
    (hout : spotOut.size < UInt256.size) (hlo : 64 ≤ spotOut.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (endCageIlkSpotIlksPostCallMem I vatOut spotOut).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((endCageIlkSpotIlksPostCallMem I vatOut spotOut).readWithPadding
          (⟨128⟩ : UInt256).toNat 32))) =
      endCageIlkSpotIlkPipWord spotOut := by
  rw [show (⟨128⟩ : UInt256).toNat = 128 by decide]
  rw [endCageIlkSpotIlksPostCallMem_size I vatOut spotOut hvat hout,
    endCageIlkSpotIlksPostCallMem_read128 I vatOut spotOut hvat hout hlo]
  change (if False ∨ False then (⟨0⟩ : UInt256) else
      endCageIlkSpotIlkPipWord spotOut) = endCageIlkSpotIlkPipWord spotOut
  simp

theorem endCageIlkNoArgCalldataMem_size {selectorShifted mem : ByteArray}
    (hselector : selectorShifted.size = 32) (hmem : mem.size = 288) :
    (endCageIlkNoArgCalldataMem selectorShifted mem).size = 288 := by
  unfold endCageIlkNoArgCalldataMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide]
  rw [write_eq_gen selectorShifted mem 128 32 (by decide)
    (by rw [hselector]) (by rw [hmem]; decide)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hselector, hmem]
  omega

theorem endCageIlkNoArgCalldataMem_read64 {selectorShifted mem : ByteArray}
    (hselector : selectorShifted.size = 32) (hmem : mem.size = 288)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (endCageIlkNoArgCalldataMem selectorShifted mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endCageIlkNoArgCalldataMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide]
  rw [write32_read_below selectorShifted mem 128 64 (by rw [hselector])
    (by rw [hmem]; omega) (by omega), hread64]

theorem endCageIlkNoArgCalldataMem_read128_4 {selectorShifted mem : ByteArray}
    (hselector : selectorShifted.size = 32) (hmem : mem.size = 288) :
    (endCageIlkNoArgCalldataMem selectorShifted mem).readWithPadding 128 4 =
      selectorShifted.extract 0 4 := by
  unfold endCageIlkNoArgCalldataMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide]
  exact write32_read_prefix_len selectorShifted mem 128 4
    (by rw [hselector]) (by rw [hmem]; omega) (by omega) (by omega) (by omega)

theorem endCageIlkSpotIlksEncode_eq (I : ExecutionEnv) (vatOut : ByteArray)
    (hsz36 : 36 ≤ I.calldata.size) (hvat : 160 ≤ vatOut.size) :
    config.externalABI.encode? "spotIlks" [.fixedBytes bytes32Width (endBytes32ArgBytes I)] =
      some ((endCageIlkSpotIlksCalldataMem I vatOut).readWithPadding
        endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat) := by
  change config.externalABI.encode? "spotIlks" [.fixedBytes bytes32Width (endBytes32ArgBytes I)] =
    some ((endFlowVatIlksCalldataMem I
      (twoWordHashMem (endCageIlkIlkWord I) ⟨14⟩
        (endCageIlkVatIlksPostCallMem I vatOut))).readWithPadding 128 36)
  rw [← endCageIlkArtHashMem, ← endCageIlkSpotIlksCalldataMem,
    endCageIlkSpotIlksCalldataMem_read128_36 I vatOut hvat]
  have hbytes : endBytes32ArgBytes I = EVM.Word.toBytesBE (endFlowIlkWord I) := by
    have hlen32 : (endBytes32ArgBytes I).length = 32 :=
      endBytes32ArgBytes_len32 (I := I) hsz36
    have hword : ABI.bytesToWord (endBytes32ArgBytes I) = endFlowIlkWord I := by
      simpa [endBytes32ArgBytes, endFlowIlkWord, endBytes32ArgWord] using
        (decode_word_at_eq_any I.calldata 4 (by simpa using hsz36))
    have hto := toBytesBE_bytesToWord_of_length (bs := endBytes32ArgBytes I) hlen32
    rw [hword] at hto
    exact hto.symm
  have hlen : (EVM.Word.toBytesBE (endFlowIlkWord I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (endFlowIlkWord I)
  simp [config, externalABI, ilksEncode?, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, bytes32, bytes32Width, ilksSelector,
    selectorBytes, hbytes, hlen, ABI.zeroBytes, word_toBytesBE_toByteArray_eq_toByteArray]

theorem endCageIlkParCalldataMem_read128_4 (I : ExecutionEnv)
    (vatOut spotOut : ByteArray) (hvat : 160 ≤ vatOut.size)
    (hspot : spotOut.size < UInt256.size) :
    (endCageIlkParCalldataMem I vatOut spotOut).readWithPadding 128 4 = parSelector := by
  have hselector :
      (UInt256.shiftLeft endCageIlkParSelectorWord ⟨224⟩).toByteArray.size = 32 := by
    rw [toByteArray_size]
  have hmem : (endCageIlkSpotIlksPostCallMem I vatOut spotOut).size = 288 :=
    endCageIlkSpotIlksPostCallMem_size I vatOut spotOut hvat hspot
  unfold endCageIlkParCalldataMem
  rw [endCageIlkNoArgCalldataMem_read128_4 hselector hmem]
  unfold endCageIlkParSelectorWord parSelector selectorBytes
  native_decide

theorem endCageIlkParEncode_eq (I : ExecutionEnv) (vatOut spotOut : ByteArray)
    (hvat : 160 ≤ vatOut.size) (hspot : spotOut.size < UInt256.size) :
    config.externalABI.encode? "par" [] =
      some ((endCageIlkParCalldataMem I vatOut spotOut).readWithPadding
        endFlowVatIlksOutPtr.toNat endCageIlkNoArgInSize.toNat) := by
  change config.externalABI.encode? "par" [] =
    some ((endCageIlkParCalldataMem I vatOut spotOut).readWithPadding 128 4)
  rw [endCageIlkParCalldataMem_read128_4 I vatOut spotOut hvat hspot]
  simp [config, externalABI, parSelector]

theorem endCageIlkNoArgCalldataMem_mload64 {selectorShifted mem : ByteArray}
    (hselector : selectorShifted.size = 32) (hmem : mem.size = 288)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (endCageIlkNoArgCalldataMem selectorShifted mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((endCageIlkNoArgCalldataMem selectorShifted mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [endCageIlkNoArgCalldataMem_size hselector hmem]; decide)
    (by decide)
    (endCageIlkNoArgCalldataMem_read64 hselector hmem hread64)

theorem endCageIlkNoArgWriteLen_eq {out : ByteArray}
    (hout : out.size < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = min 32 out.size := by
  by_cases hle : 32 ≤ out.size
  · rw [Nat.min_eq_left hle]
    exact umin_ofNat_right_toNat_of_ge (c := 32) (n := out.size) (by decide) hle hout
  · have hlt : out.size < 32 := by omega
    rw [Nat.min_eq_right (by omega : out.size ≤ 32)]
    exact umin_ofNat_right_toNat_of_lt (c := 32) (n := out.size) (by decide) hlt hout

theorem endCageIlkNoArgPostCallMem_size {selectorShifted mem out : ByteArray}
    (hselector : selectorShifted.size = 32) (hmem : mem.size = 288)
    (hout : out.size < UInt256.size) :
    (endCageIlkNoArgPostCallMem selectorShifted mem out).size = 288 := by
  unfold endCageIlkNoArgPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    endCageIlkNoArgWriteLen_eq hout]
  by_cases hlen0 : min 32 out.size = 0
  · rw [hlen0, byteArray_write_len_zero,
      endCageIlkNoArgCalldataMem_size hselector hmem]
  · rw [write_eq_gen out (endCageIlkNoArgCalldataMem selectorShifted mem)
      128 (min 32 out.size) hlen0 (Nat.min_le_right _ _)
      (by rw [endCageIlkNoArgCalldataMem_size hselector hmem]; omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract,
      endCageIlkNoArgCalldataMem_size hselector hmem]
    have hleout : min 32 out.size ≤ out.size := Nat.min_le_right _ _
    omega

theorem endCageIlkNoArgPostCallMem_read64 {selectorShifted mem out : ByteArray}
    (hselector : selectorShifted.size = 32) (hmem : mem.size = 288)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hout : out.size < UInt256.size) :
    (endCageIlkNoArgPostCallMem selectorShifted mem out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endCageIlkNoArgPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    endCageIlkNoArgWriteLen_eq hout]
  by_cases hlen0 : min 32 out.size = 0
  · rw [hlen0, byteArray_write_len_zero]
    exact endCageIlkNoArgCalldataMem_read64 hselector hmem hread64
  · rw [write_read_below_gen out (endCageIlkNoArgCalldataMem selectorShifted mem)
      128 (min 32 out.size) 64 hlen0 (Nat.min_le_right _ _)
      (by rw [endCageIlkNoArgCalldataMem_size hselector hmem]; omega)
      (by native_decide)]
    exact endCageIlkNoArgCalldataMem_read64 hselector hmem hread64

theorem endCageIlkReadCalldataMem_read128_4 (I : ExecutionEnv)
    (vatOut spotOut parOut : ByteArray) (hvat : 160 ≤ vatOut.size)
    (hspot : spotOut.size < UInt256.size) (hpar : parOut.size < UInt256.size) :
    (endCageIlkReadCalldataMem I vatOut spotOut parOut).readWithPadding 128 4 =
      readSelector := by
  have hspotMemSize :
      (endCageIlkSpotIlksPostCallMem I vatOut spotOut).size = 288 :=
    endCageIlkSpotIlksPostCallMem_size I vatOut spotOut hvat hspot
  have hparSelectorSize :
      (UInt256.shiftLeft endCageIlkParSelectorWord ⟨224⟩).toByteArray.size = 32 := by
    rw [toByteArray_size]
  have hreadSelectorSize :
      (UInt256.shiftLeft endCageIlkReadSelectorRaw ⟨226⟩).toByteArray.size = 32 := by
    rw [toByteArray_size]
  have hbaseSize :
      (endCageIlkParPostCallMem I vatOut spotOut parOut).size = 288 := by
    unfold endCageIlkParPostCallMem
    exact endCageIlkNoArgPostCallMem_size hparSelectorSize hspotMemSize hpar
  unfold endCageIlkReadCalldataMem
  rw [endCageIlkNoArgCalldataMem_read128_4 hreadSelectorSize hbaseSize]
  unfold endCageIlkReadSelectorRaw readSelector selectorBytes
  native_decide

theorem endCageIlkReadEncode_eq (I : ExecutionEnv)
    (vatOut spotOut parOut : ByteArray) (hvat : 160 ≤ vatOut.size)
    (hspot : spotOut.size < UInt256.size) (hpar : parOut.size < UInt256.size) :
    config.externalABI.encode? "read" [] =
      some ((endCageIlkReadCalldataMem I vatOut spotOut parOut).readWithPadding
        endFlowVatIlksOutPtr.toNat endCageIlkNoArgInSize.toNat) := by
  change config.externalABI.encode? "read" [] =
    some ((endCageIlkReadCalldataMem I vatOut spotOut parOut).readWithPadding 128 4)
  rw [endCageIlkReadCalldataMem_read128_4 I vatOut spotOut parOut hvat hspot hpar]
  simp [config, externalABI, readSelector]

theorem endCageIlkNoArgPostCallMem_read128 {selectorShifted mem out : ByteArray}
    (hselector : selectorShifted.size = 32) (hmem : mem.size = 288)
    (hout : out.size < UInt256.size) (hlo : 32 ≤ out.size) :
    (endCageIlkNoArgPostCallMem selectorShifted mem out).readWithPadding 128 32 =
      out.extract 0 32 := by
  unfold endCageIlkNoArgPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    endCageIlkNoArgWriteLen_eq hout, show min 32 out.size = 32 from Nat.min_eq_left hlo]
  rw [write_eq_gen out (endCageIlkNoArgCalldataMem selectorShifted mem) 128 32
    (by decide) (by omega)
    (by rw [endCageIlkNoArgCalldataMem_size hselector hmem]; omega)]
  rw [readWithPadding_eq_extract _ 128 (by
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract,
      endCageIlkNoArgCalldataMem_size hselector hmem]
    omega)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
      endCageIlkNoArgCalldataMem_size hselector hmem]
    omega)]
  rw [extract_append_right_window _ _ _ _ (by rw [ByteArray.size_extract]; omega)]
  rw [ByteArray.size_extract]
  rw [show min 128 (endCageIlkNoArgCalldataMem selectorShifted mem).size - 0 = 128 by
    rw [endCageIlkNoArgCalldataMem_size hselector hmem]
    omega]
  rw [show 128 - 128 = 0 by omega, show 160 - 128 = 32 by omega]
  rw [extract_extract_BA]
  rw [show 0 + 0 = 0 by omega, show min (0 + 32) 32 = 32 by omega]

theorem endCageIlkNoArgPostCallMem_mload64 {selectorShifted mem out : ByteArray}
    (hselector : selectorShifted.size = 32) (hmem : mem.size = 288)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hout : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (endCageIlkNoArgPostCallMem selectorShifted mem out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((endCageIlkNoArgPostCallMem selectorShifted mem out).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [endCageIlkNoArgPostCallMem_size hselector hmem hout]; decide)
    (by decide)
    (endCageIlkNoArgPostCallMem_read64 hselector hmem hread64 hout)

theorem endCageIlk_twoWordHashMem_read64_of_ge96 {mem : ByteArray} (key slot : UInt256)
    (hmem : 96 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hmem64 : 64 ≤ mem.size := by omega
  have hword0 : (wordAt0Mem key mem).size = mem.size :=
    endFlow_wordAt0Mem_size_of_ge64 key hmem64
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [hword0]; omega) (by omega) (by rw [hword0]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by omega) (by omega)
    (by omega)]
  exact hread64

theorem endCageIlkNoArgPostCallMem_mload128 {selectorShifted mem out : ByteArray}
    (hselector : selectorShifted.size = 32) (hmem : mem.size = 288)
    (hout : out.size < UInt256.size) (hlo : 32 ≤ out.size) :
    (if (⟨128⟩ : UInt256).toNat ≥
          (endCageIlkNoArgPostCallMem selectorShifted mem out).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((endCageIlkNoArgPostCallMem selectorShifted mem out).readWithPadding
          (⟨128⟩ : UInt256).toNat 32))) =
      endCageIlkReturnWord out := by
  rw [show (⟨128⟩ : UInt256).toNat = 128 by decide]
  rw [endCageIlkNoArgPostCallMem_size hselector hmem hout,
    endCageIlkNoArgPostCallMem_read128 hselector hmem hout hlo]
  change (if False ∨ False then (⟨0⟩ : UInt256) else
      endCageIlkReturnWord out) = endCageIlkReturnWord out
  simp

theorem endCageIlkTagSlot_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    endCageIlkTagSlot I = solcMappingSlot ⟨12⟩ (endCageIlkIlkWord I) := by
  unfold endCageIlkTagSlot endCageIlkIlkKey tagSlot mapSlot solcMappingSlot
  rw [endKeyValueToWord_bytes32ArgKey (by omega)]

theorem endCageIlkArtSlot_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    endCageIlkArtSlot I = solcMappingSlot ⟨14⟩ (endCageIlkIlkWord I) := by
  unfold endCageIlkArtSlot endCageIlkIlkKey ArtSlot mapSlot solcMappingSlot
  rw [endKeyValueToWord_bytes32ArgKey (by omega)]

theorem endCageIlk_bytesToWord_drop_take32_eq_extract (out : ByteArray) (start : ℕ) :
    ABI.bytesToWord ((out.toList.drop start).take 32) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract start (start + 32))) := by
  unfold ABI.bytesToWord fromByteArrayBigEndian
  congr 1
  rw [byteArray_toList_eq (out.extract start (start + 32)), ByteArray.data_extract,
    Array.toList_extract, List.extract_eq_take_drop, byteArray_toList_eq]
  rw [byteArray_toList_eq]
  simp

theorem endCageIlkSpotIlksDecode_ok {out : ByteArray} (hlo : 64 ≤ out.size) :
    config.externalABI.decode? "spotIlks" out =
      some [.address (endCageIlkSpotIlkPipAddr out),
        .int (Int.ofNat (endCageIlkSpotIlkMatWord out).toNat)] := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0 : ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have htake32 : ((out.toList.drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have hword0 := endCageIlk_bytesToWord_drop_take32_eq_extract out 0
  have hword32 := endCageIlk_bytesToWord_drop_take32_eq_extract out 32
  change ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [addr, uint256] out =
    some [.address (endCageIlkSpotIlkPipAddr out),
      .int (Int.ofNat (endCageIlkSpotIlkMatWord out).toNat)]
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq (types := [addr, uint256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [addr, uint256]) (bytes := out.toList) (cursor := 0)
    (total := 32 * [addr, uint256].length) (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  have haddrDec :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 addr out.toList 0 =
        some (.address (AccountAddress.ofNat
          (ABI.bytesToWord ((out.toList.drop 0).take 32)).toNat), 0 + 32) := by
    simpa [addr, abiAddress] using
      decodeScalarWord_legacyAddress_ok (bytes := out.toList) (start := 0) htake0
  rw [haddrDec]
  simp only [Option.bind_eq_bind, Option.bind_some]
  have huintDec :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList (0 + 32) =
        some (.int (Int.ofNat
          (ABI.bytesToWord ((out.toList.drop 32).take 32)).toNat), 32 + 32) := by
    simpa [uint256, abiUInt256] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 32) htake32
  rw [huintDec]
  simp only [Option.bind_some]
  rw [hword0, hword32]

theorem endCageIlkParDecode_ok {out : ByteArray} (hlo : 32 ≤ out.size) :
    config.externalABI.decode? "par" out =
      some [.int (Int.ofNat (endCageIlkReturnWord out).toNat)] := by
  change decodeReturn? uint256 out =
    some [.int (Int.ofNat (endCageIlkReturnWord out).toNat)]
  unfold decodeReturn?
  change Option.map (fun v => [v])
      (ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 abiUInt256 out) =
    some [Value.int (Int.ofNat (endCageIlkReturnWord out).toNat)]
  rw [decodeReturnValueWithMode_legacy_uint256_ok (returndata := out) hlo]
  change some [Value.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))] =
    some [Value.int (Int.ofNat (endCageIlkReturnWord out).toNat)]
  rw [show (endCageIlkReturnWord out).toNat = fromByteArrayBigEndian (out.extract 0 32) by
    unfold endCageIlkReturnWord
    exact UInt256.toNat_ofNat_of_lt (fromByteArrayBigEndian_extract0_32_lt hlo)]

theorem endCageIlkReadDecode_ok {out : ByteArray} (hlo : 32 ≤ out.size) :
    config.externalABI.decode? "read" out =
      some [.fixedBytes bytes32Width (endCageIlkReadBytes out)] := by
  change decodeReturn? bytes32 out = _
  unfold decodeReturn?
  change Option.map (fun v => [v])
      (ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 abiBytes32 out) = _
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValuesWithMode?
  rw [show abiTupleHeadSize? [abiBytes32] = some 32 by native_decide]
  simp only [bind, Option.bind]
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlenge : 32 ≤ out.toList.length := by omega
  have hdec :
      decodeABIValues? [abiBytes32] out.toList 0 0 32 32 DecodeMode.legacySolc05 =
        some ([.fixedBytes abiBytes32Width ((out.toList.drop 0).take 32)], 32) := by
    simp [decodeABIValues?, decodeABIValue?, readBytes?, abiBytes32, abiBytes32Width,
      ABI.isDynamicABIType, staticABIEncodedSize?, hlenge]
  rw [hdec]
  rfl

theorem RD.endCageIlkTagDefinedRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD endBytecode ee g s0 ⟨8923⟩ stk mem (UInt256.ofNat 3) rdata acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev endBytecode g s0 := by
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 mem) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨27⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 ⟨27⟩ mem)
      (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst endCageIlkTagDefinedRawWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact evm_run rdRaw with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 ⟨27⟩ endCageIlkTagDefinedRawWord mem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨27⟩ endCageIlkTagDefinedRawWord hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem endDecode_cageIlk_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (cageIlkTransition.params.map Param.name)
      (transitionSignature cageIlkTransition).paramTypes I.calldata =
        some (endCageIlkStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk"] [bytes32] I.calldata = _
  simpa [config, endCageIlkStore, endCageIlkIlkValue, endCageIlkIlkWord,
    cageIlkTransition, bytes32, bytes32Width, abiBytes32, abiBytes32Width] using
    endDecode_legacyBytes32_ok (cd := I.calldata) (x := "ilk") hsz36

theorem endDecode_cageIlk_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (cageIlkTransition.params.map Param.name)
      (transitionSignature cageIlkTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk"] [bytes32] I.calldata = none
  simpa [config, cageIlkTransition, bytes32, bytes32Width, abiBytes32, abiBytes32Width] using
    endDecode_legacyBytes32_none_short (cd := I.calldata) (x := "ilk") hsz4 hshort

theorem endReachCageIlkBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endCageIlkConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endCageIlkEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0xe2702fdc⟩ :=
    endSelWord_eq_of_beq I hsz 0xe2 0x70 0x2f 0xdc ⟨0xe2702fdc⟩
      (by native_decide)
      (by simpa [selIs, endCageIlkConcreteSelector, selectorBytes] using hsel)
  obtain ⟨_, _, hfirst⟩ :=
    endReachGroup114FirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup114FirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup114FirstArmPc 2))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo endCageIlkEntryPc 2 hfirst
    (fun j hj => endGroup114ArmsWellFormed j (by omega))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem endCageIlkX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endCageIlkEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endCageIlkBodyPc
      [endCageIlkIlkWord I, endCageIlkReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := endBytecode) (sel := sel) (entry := endCageIlkEntryPc)
    (ret := endCageIlkReturnPc) (decoded := endCageIlkDecodedPc) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneWordExternalJump
    (code := endBytecode) (decoded := endCageIlkDecodedPc) (ret := endCageIlkReturnPc)
    (routine := endCageIlkBodyPc) (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [endCageIlkIlkWord, calldataWord] using hroutine⟩

theorem endCageIlkX_liveNonzero {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hlive : endCageIlkLiveWord σ I ≠ ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endCageIlkBodyPc
      [endCageIlkIlkWord I, endCageIlkReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd8835 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨8⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd8836raw⟩ := rd8835.sload (by native_decide) (by evm_ov)
  have rd8836 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8836⟩
        (endCageIlkLiveWord σ I :: endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by
      simpa [endCageIlkLiveWord, endSlotWord, solcSlotWord] using rd8836raw⟩
  obtain ⟨_, _, rd8836⟩ := rd8836
  have rd8837raw := rd8836.iszero (by native_decide) (by evm_ov)
  have hzero : UInt256.isZero (endCageIlkLiveWord σ I) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hlive
  have rd8837 := rd8837raw
  rw [hzero] at rd8837
  have rd8840 := rd8837.push2 ⟨8902⟩ (by native_decide) (by evm_ov)
  have rd8841 := rd8840.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨8841⟩) (len := ⟨14⟩)
    (rawWord := ⟨0x456e642f7374696c6c2d6c697665⟩) (shift := ⟨144⟩)
    (word := UInt256.shiftLeft ⟨0x456e642f7374696c6c2d6c697665⟩ ⟨144⟩)
    (op := .PUSH14) (width := 14)
    (by simpa using rd8841)
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide) rfl
    solcFreePtrMem_size solcFreePtrMem_read64
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageIlkX_tagNonzero {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hsz36 : 36 ≤ I.calldata.size)
    (hlive : endCageIlkLiveWord σ I = ⟨0⟩)
    (htag : endCageIlkTagWord σ I ≠ ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endCageIlkBodyPc
      [endCageIlkIlkWord I, endCageIlkReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let key := endCageIlkIlkWord I
  have hslot : endCageIlkTagSlot I = solcMappingSlot ⟨12⟩ key := by
    simpa [key] using endCageIlkTagSlot_eq (I := I) hsz36
  have rd8835 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨8⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd8836raw⟩ := rd8835.sload (by native_decide) (by evm_ov)
  have hliveRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨8⟩ ⟨0⟩)) =
        ⟨0⟩ := by
    simpa [endCageIlkLiveWord, endSlotWord, solcSlotWord] using hlive
  have rd8836zero := rd8836raw
  rw [hliveRaw] at rd8836zero
  obtain ⟨_, _, rd8836⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8836⟩
        (⟨0⟩ :: endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endCageIlkBodyPc] using rd8836zero⟩
  have rd8837raw := rd8836.iszero (by native_decide) (by evm_ov)
  have rd8837 := rd8837raw
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd8837
  have rd8840 := rd8837.push2 ⟨8902⟩ (by native_decide) (by evm_ov)
  have rd8902 := rd8840.jumpiT (by native_decide)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest) (by evm_ov)
  have rd8906pre := evm_run rd8902 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd8907 := rd8906pre.mstore 0 (wordAt0Mem key solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd8912pre := evm_run rd8907 with [
    raw push1 ⟨12⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd8913 := rd8912pre.mstore 0 (twoWordHashMem key ⟨12⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd8916pre := evm_run rd8913 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key ⟨12⟩ solcFreePtrMem).readWithPadding 0 64))) =
          solcMappingSlot ⟨12⟩ key :=
    twoWordHashMem_solcMappingSlot ⟨12⟩ key solcFreePtrMem_size
  have rd8917pre := rd8916pre.keccak256 0 (solcMappingSlot ⟨12⟩ key)
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by
      simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hhash)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd8918raw⟩ := rd8917pre.sload (by native_decide) (by evm_ov)
  have rd8918 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8918⟩
        (endCageIlkTagWord σ I :: endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
        (twoWordHashMem key ⟨12⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k' C' := by
    have htagRaw :
        solcSlotWord σ I (solcMappingSlot ⟨12⟩ key) = endCageIlkTagWord σ I := by
      rw [← hslot]
      simp [endCageIlkTagWord, endSlotWord]
    exact ⟨_, _, by simpa [htagRaw] using rd8918raw⟩
  obtain ⟨_, _, rd8918⟩ := rd8918
  have rd8919raw := rd8918.iszero (by native_decide) (by evm_ov)
  have hzero : UInt256.isZero (endCageIlkTagWord σ I) = ⟨0⟩ :=
    isZero_eq_zero_of_ne htag
  have rd8919 := rd8919raw
  rw [hzero] at rd8919
  have rd8922 := rd8919.push2 ⟨8999⟩ (by native_decide) (by evm_ov)
  have rd8923 := rd8922.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  obtain ⟨_, _, rdTail⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8923⟩
        [endCageIlkIlkWord I, endCageIlkReturnPc, sel]
        (twoWordHashMem key ⟨12⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k' C' := by
    exact ⟨_, _, by simpa using rd8923⟩
  exact RD.endCageIlkTagDefinedRevert rdTail
    (twoWordHashMem_size_96 key ⟨12⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 key ⟨12⟩ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageIlkX_vatIlksExtcodesizeGuard {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (hsz36 : 36 ≤ I.calldata.size)
    (hlive : endCageIlkLiveWord σ I = ⟨0⟩)
    (htag : endCageIlkTagWord σ I = ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endCageIlkBodyPc
      [endCageIlkIlkWord I, endCageIlkReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9065⟩
      (endPackVatWord σ I :: endPackVatWord σ I :: ⟨0⟩ :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endFlowVatIlksOutSize ::
        endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σ I ::
        endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      (endCageIlkVatIlksCalldataMem I) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k' C' := by
  let key := endCageIlkIlkWord I
  have htagSlot : endCageIlkTagSlot I = solcMappingSlot ⟨12⟩ key := by
    simpa [key] using endCageIlkTagSlot_eq (I := I) hsz36
  have htagMemSize :
      (endCageIlkTagHashMem I).size = 96 := by
    rw [endCageIlkTagHashMem]
    exact twoWordHashMem_size_96 key ⟨12⟩ solcFreePtrMem_size
  have htagMemRead64 :
      (endCageIlkTagHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    rw [endCageIlkTagHashMem]
    exact twoWordHashMem_read64 key ⟨12⟩ solcFreePtrMem_size solcFreePtrMem_read64
  have hcallMem :
      (endCageIlkVatIlksCalldataMem I).size = 164 := by
    unfold endCageIlkVatIlksCalldataMem
    exact endFlowVatIlksCalldataMem_size I htagMemSize
  have hcallRead64 :
      (endCageIlkVatIlksCalldataMem I).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ := by
    unfold endCageIlkVatIlksCalldataMem
    exact endFlowVatIlksCalldataMem_read64 I htagMemSize htagMemRead64
  have hmload64Hash :
      (if (⟨64⟩ : UInt256).toNat ≥ (endCageIlkTagHashMem I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endCageIlkTagHashMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [htagMemSize]; decide) (by decide) htagMemRead64
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (endCageIlkVatIlksCalldataMem I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endCageIlkVatIlksCalldataMem I).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hcallMem]; decide) (by decide) hcallRead64
  have hselectorShift :
      UInt256.shiftLeft (⟨0x6cb1c69b⟩ : UInt256) ⟨225⟩ =
        endFlowVatIlksSelectorShifted := by
    native_decide
  have hvatMask :
      UInt256.land solcAddrMask (endSlotWord ⟨1⟩ σ I) = endPackVatWord σ I := by
    simpa [endPackVatWord, solcAddrMask] using
      u256_land_comm solcAddrMask (endSlotWord ⟨1⟩ σ I)
  have hinSize :
      (UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨36⟩) = endFlowVatIlksInSize := by
    native_decide
  have hendPtr : ((⟨128⟩ : UInt256) + ⟨36⟩) = endFlowVatIlksEndPtr := by
    native_decide
  have rd8835 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨8⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd8836raw⟩ := rd8835.sload (by native_decide) (by evm_ov)
  have hliveRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨8⟩ ⟨0⟩)) =
        ⟨0⟩ := by
    simpa [endCageIlkLiveWord, endSlotWord, solcSlotWord] using hlive
  have rd8836zero := rd8836raw
  rw [hliveRaw] at rd8836zero
  obtain ⟨_, _, rd8836⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8836⟩
        (⟨0⟩ :: endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endCageIlkBodyPc] using rd8836zero⟩
  have rd8837raw := rd8836.iszero (by native_decide) (by evm_ov)
  have rd8837 := rd8837raw
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd8837
  have rd8840 := rd8837.push2 ⟨8902⟩ (by native_decide) (by evm_ov)
  have rd8902 := rd8840.jumpiT (by native_decide)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest) (by evm_ov)
  have rd8906pre := evm_run rd8902 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd8907 := rd8906pre.mstore 0 (wordAt0Mem key solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd8912pre := evm_run rd8907 with [
    raw push1 ⟨12⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd8913 := rd8912pre.mstore 0 (twoWordHashMem key ⟨12⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd8916pre := evm_run rd8913 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key ⟨12⟩ solcFreePtrMem).readWithPadding 0 64))) =
          solcMappingSlot ⟨12⟩ key :=
    twoWordHashMem_solcMappingSlot ⟨12⟩ key solcFreePtrMem_size
  have rd8917pre := rd8916pre.keccak256 0 (solcMappingSlot ⟨12⟩ key)
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by
      simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hhash)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd8918raw⟩ := rd8917pre.sload (by native_decide) (by evm_ov)
  have htagRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun ac => ac.storage.findD (solcMappingSlot ⟨12⟩ key) ⟨0⟩)) = ⟨0⟩ := by
    have hslotWord :
        solcSlotWord σ I (solcMappingSlot ⟨12⟩ key) = ⟨0⟩ := by
      rw [← htagSlot]
      simpa [endCageIlkTagWord, endSlotWord, key] using htag
    simpa [solcSlotWord] using hslotWord
  have rd8918zero := rd8918raw
  rw [htagRaw] at rd8918zero
  obtain ⟨_, _, rd8918⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8918⟩
        (⟨0⟩ :: endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
        (endCageIlkTagHashMem I) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endCageIlkTagHashMem, key] using rd8918zero⟩
  have rd8919raw := rd8918.iszero (by native_decide) (by evm_ov)
  have rd8919 := rd8919raw
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd8919
  have rd8922 := rd8919.push2 ⟨8999⟩ (by native_decide) (by evm_ov)
  have rd8999 := rd8922.jumpiT (by native_decide)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest) (by evm_ov)
  have rd9002 := evm_run rd8999 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd9003raw⟩ := rd9002.sload (by native_decide) (by evm_ov)
  have rd9003 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9003⟩
        (endSlotWord ⟨1⟩ σ I :: endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
        (endCageIlkTagHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd9003raw⟩
  obtain ⟨_, _, rd9003⟩ := rd9003
  have rd9065 := evm_run rd9003 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64Hash (by decide) (by evm_ov),
    raw push4 ⟨0x6cb1c69b⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨225⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (endFlowVatIlksSelectorMem (endCageIlkTagHashMem I)) (UInt256.ofNat 5)
      (by native_decide) mem_cost
      (by
        simp [endFlowVatIlksSelectorMem, endFlowVatIlksOutPtr, endCageIlkTagHashMem,
          hselectorShift])
      (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 3 (endCageIlkVatIlksCalldataMem I) (UInt256.ofNat 6)
      (by native_decide) mem_cost
      (by
        simp [endCageIlkVatIlksCalldataMem, endFlowVatIlksCalldataMem,
          endFlowVatIlksArg0Mem, endFlowVatIlksOutPtr, endCageIlkTagHashMem])
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push4 endFlowVatIlksSelectorWord (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [endFlowVatIlksSelectorMem, endFlowVatIlksArg0Mem,
      endFlowVatIlksCalldataMem, endCageIlkVatIlksCalldataMem, endCageIlkTagHashMem,
      endFlowVatIlksOutPtr, endFlowVatIlksInSize, endFlowVatIlksOutSize,
      endFlowVatIlksEndPtr, endFlowVatIlksSelectorShifted, endFlowVatIlksSelectorWord,
      endPackVatWord, endSlotWord, solcSlotWord, solcAddrMask, hselectorShift, hvatMask,
      hinSize, hendPtr, u256_land_comm, key]
      using rd9065⟩

theorem endCageIlkX_vatIlksNoCode {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (hsz36 : 36 ≤ I.calldata.size)
    (hlive : endCageIlkLiveWord σ I = ⟨0⟩)
    (htag : endCageIlkTagWord σ I = ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endCageIlkBodyPc
      [endCageIlkIlkWord I, endCageIlkReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (endPackVatWord σ I) = ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd9065⟩ :=
    endCageIlkX_vatIlksExtcodesizeGuard hsz36 hlive htag h
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨9065⟩) (okPc := ⟨9077⟩)
    rd9065 hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageIlkX_vatIlksCallReady {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (hsz36 : 36 ≤ I.calldata.size)
    (hlive : endCageIlkLiveWord σ I = ⟨0⟩)
    (htag : endCageIlkTagWord σ I = ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endCageIlkBodyPc
      [endCageIlkIlkWord I, endCageIlkReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9080⟩
      (gasWord :: endPackVatWord σ I :: ⟨0⟩ :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endFlowVatIlksOutSize ::
        endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σ I ::
        endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      (endCageIlkVatIlksCalldataMem I) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd9065⟩ :=
    endCageIlkX_vatIlksExtcodesizeGuard hsz36 hlive htag h
  obtain ⟨gasWord, k', C', rd9080⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨9065⟩) (okPc := ⟨9077⟩)
      rd9065 hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd9080⟩

theorem endCageIlkX_vatIlksPostCall {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel gasWord : UInt256} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9080⟩
      (gasWord :: endPackVatWord σ I :: ⟨0⟩ :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endFlowVatIlksOutSize ::
        endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σ I ::
        endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      (endCageIlkVatIlksCalldataMem I) (UInt256.ofNat 6)
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
          ((endCageIlkVatIlksCalldataMem I).readWithPadding
            endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat)
          (I.depth + 1) I.header I.perm)
      ∧ RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9081⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endFlowVatIlksEndPtr ::
            endFlowVatIlksSelectorWord :: endPackVatWord σ I ::
            endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
          (endCageIlkVatIlksPostCallMem I out) (UInt256.ofNat 9) out (cA', σ') k' C'
      ∧ out.size < UInt256.size := by
  obtain ⟨cA', σ', z, out, Ain, callGas, k', C', hΘ, rd9081raw, hout⟩ :=
    RD.call h (by native_decide) hdepth (by evm_ov)
  refine ⟨cA', σ', z, out, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · have hmin := endFlowVatIlksWriteLen_eq (out := out) hout
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat)
          endFlowVatIlksOutPtr.toNat endFlowVatIlksOutSize.toNat) = UInt256.ofNat 9 := by
      unfold endFlowVatIlksOutPtr endFlowVatIlksInSize endFlowVatIlksOutSize
      native_decide
    simpa [endCageIlkVatIlksPostCallMem, endFlowVatIlksOutPtr, endFlowVatIlksInSize,
      endFlowVatIlksOutSize, endFlowVatIlksEndPtr, hmin, haw] using rd9081raw

theorem endCageIlkX_vatIlksCallDepthLimit {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel gasWord : UInt256} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9080⟩
      (gasWord :: endPackVatWord σ I :: ⟨0⟩ :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endFlowVatIlksOutSize ::
        endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σ I ::
        endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      (endCageIlkVatIlksCalldataMem I) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9081⟩
      (⟨0⟩ :: endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endPackVatWord σ I :: endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      (endCageIlkVatIlksCalldataMem I) (UInt256.ofNat 9)
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', C', rd9081raw⟩ :=
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
    endFlowVatIlksEndPtr, hmin, byteArray_write_len_zero, haw] using rd9081raw

theorem endCageIlkX_vatIlksCallFailed {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9081⟩
      (⟨0⟩ :: endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endPackVatWord σ I :: endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata (cA', σ') k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨9081⟩) (okPc := ⟨9097⟩) h
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageIlkX_vatIlksCallSucceeded {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9081⟩
      (⟨1⟩ :: endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endPackVatWord σ I :: endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9099⟩
      (endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σ I ::
        endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata (cA', σ') k' C' := by
  exact RD.uniswapCallSuccessGuardOk (pc := ⟨9081⟩) (okPc := ⟨9097⟩) h
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simp)

theorem endCageIlkX_vatIlksReturnDecodeOk {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {out : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9099⟩
      (endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σ I ::
        endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      (endCageIlkVatIlksPostCallMem I out) (UInt256.ofNat 9) out (cA', σ') k C)
    (hlo : 160 ≤ out.size) (hout : out.size < UInt256.size) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9122⟩
      (endFlowVatIlkArtWord out :: endCageIlkIlkWord I :: endCageIlkReturnPc ::
        sel :: [])
      (endCageIlkVatIlksPostCallMem I out) (UInt256.ofNat 9) out (cA', σ') k' C' := by
  have hmload64 := endCageIlkVatIlksPostCallMem_mload64_long I out hlo
  have hmload128 := endCageIlkVatIlksPostCallMem_mload128_long I out hlo
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨160⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide, ulit_toNat' out.size hout]
    exact hlo
  have rd9114 := evm_run h with [
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
    raw push2 ⟨9119⟩ (by native_decide) (by evm_ov)]
  have rdJump := rd9114
  rw [hlt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rdJump
  have rd9122 := evm_run rdJump with [
    raw jumpiT (by native_decide) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by jump_dest) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw mload 0 (endFlowVatIlkArtWord out) (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload128 (by decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [endFlowVatIlksEndPtr, endFlowVatIlksSelectorWord, endFlowVatIlksOutPtr,
      endFlowVatIlksInSize, endFlowVatIlksOutSize] using rd9122⟩

theorem endCageIlkX_vatIlksReturnDecodeShort {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {out : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9099⟩
      (endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σ I ::
        endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      (endCageIlkVatIlksPostCallMem I out) (UInt256.ofNat 9) out (cA', σ') k C)
    (hshort : out.size < 160) (hout : out.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hmload64 := endCageIlkVatIlksPostCallMem_mload64 I out
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨160⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide, ulit_toNat' out.size hout]
    exact hshort
  have rd9114 := evm_run h with [
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
    raw push2 ⟨9119⟩ (by native_decide) (by evm_ov)]
  have rdShort := rd9114
  rw [hlt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rdShort
  have rdFall := rdShort.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.uniswapPush1Dup1Revert0 rdFall
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageIlkX_spotIlksExtcodesizeGuard {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {vatOut : ByteArray} {k C : ℕ}
    (hsz36 : 36 ≤ I.calldata.size) (hperm : I.perm = true)
    (hlo : 160 ≤ vatOut.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9122⟩
      (endFlowVatIlkArtWord vatOut :: endCageIlkIlkWord I ::
        endCageIlkReturnPc :: sel :: [])
      (endCageIlkVatIlksPostCallMem I vatOut) (UInt256.ofNat 9)
      vatOut (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9201⟩
      (endCageIlkSpotWord (endCageIlkPostArtAccountMap σ' I vatOut) I ::
        endCageIlkSpotWord (endCageIlkPostArtAccountMap σ' I vatOut) I ::
        endFlowVatIlksOutPtr :: endFlowVatIlksInSize :: endFlowVatIlksOutPtr ::
        ⟨64⟩ :: endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endCageIlkSpotWord (endCageIlkPostArtAccountMap σ' I vatOut) I ::
        ⟨0⟩ :: endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      (endCageIlkSpotIlksCalldataMem I vatOut) (UInt256.ofNat 9)
      vatOut (cA', endCageIlkPostArtAccountMap σ' I vatOut) k' C' := by
  let key := endCageIlkIlkWord I
  let σArt := endCageIlkPostArtAccountMap σ' I vatOut
  have hslot : endCageIlkArtSlot I = solcMappingSlot ⟨14⟩ key := by
    simpa [key] using endCageIlkArtSlot_eq (I := I) hsz36
  have hmload64Hash :
      (if (⟨64⟩ : UInt256).toNat ≥ (endCageIlkArtHashMem I vatOut).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endCageIlkArtHashMem I vatOut).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue
      (by rw [endCageIlkArtHashMem_size_long I vatOut hlo]; decide)
      (by decide)
      (endCageIlkArtHashMem_read64_long I vatOut hlo)
  have hmload64Spot := endCageIlkSpotIlksCalldataMem_mload64_long I vatOut hlo
  have hselectorShift :
      UInt256.shiftLeft (⟨0x6cb1c69b⟩ : UInt256) ⟨225⟩ =
        endFlowVatIlksSelectorShifted := by
    native_decide
  have hspotMask :
      UInt256.land solcAddrMask (endSlotWord ⟨6⟩ σArt I) =
        endCageIlkSpotWord σArt I := by
    simpa [σArt, endCageIlkSpotWord, endAddressReturnWord, solcAddrMask] using
      u256_land_comm solcAddrMask (endSlotWord ⟨6⟩ σArt I)
  have hinSize :
      (UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨36⟩) = endFlowVatIlksInSize := by
    native_decide
  have hendPtr : ((⟨128⟩ : UInt256) + ⟨36⟩) = endFlowVatIlksEndPtr := by
    native_decide
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((endCageIlkArtHashMem I vatOut).readWithPadding 0 64))) =
          solcMappingSlot ⟨14⟩ key := by
    unfold endCageIlkArtHashMem
    exact endFlow_twoWordHashMem_solcMappingSlot_of_ge64 ⟨14⟩ key
      (by rw [endCageIlkVatIlksPostCallMem_size_long I vatOut hlo]; omega)
  have rd9125pre := evm_run h with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd9126 := rd9125pre.mstore 0
    (wordAt0Mem key (endCageIlkVatIlksPostCallMem I vatOut))
    (UInt256.ofNat 9) (by native_decide) mem_cost
    (by simp [wordAt0Mem, key]) (by native_decide) (by evm_ov)
  have rd9131pre := evm_run rd9126 with [
    raw push1 ⟨14⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd9132 := rd9131pre.mstore 0 (endCageIlkArtHashMem I vatOut)
    (UInt256.ofNat 9) (by native_decide) mem_cost
    (by
      change (⟨14⟩ : UInt256).toByteArray.write 0
          (wordAt0Mem key (endCageIlkVatIlksPostCallMem I vatOut)) 32 32 =
        (⟨14⟩ : UInt256).toByteArray.write 0
          (wordAt0Mem (endCageIlkIlkWord I) (endCageIlkVatIlksPostCallMem I vatOut))
          32 32
      simp [key])
    (by native_decide) (by evm_ov)
  have rd9136pre := evm_run rd9132 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have rd9137pre := rd9136pre.keccak256 0 (solcMappingSlot ⟨14⟩ key)
    (UInt256.ofNat 9) (by native_decide) mem_cost
    (by
      simpa [endCageIlkArtHashMem, key, show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hhash)
    (by native_decide) (by evm_ov)
  have rd9140 := evm_run rd9137pre with [
    raw swap3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd9141raw⟩ := rd9140.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd9141⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9141⟩
        (⟨0⟩ :: ⟨64⟩ :: endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
        (endCageIlkArtHashMem I vatOut) (UInt256.ofNat 9) vatOut
        (cA', endCageIlkPostArtAccountMap σ' I vatOut) k' C' := by
    exact ⟨_, _, by
      simpa [σArt, endCageIlkPostArtAccountMap, hslot, key] using rd9141raw⟩
  have rd9143 := evm_run rd9141 with [
    raw push1 ⟨6⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd9144raw⟩ := rd9143.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd9144⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9144⟩
        (endSlotWord ⟨6⟩ (endCageIlkPostArtAccountMap σ' I vatOut) I ::
          ⟨0⟩ :: ⟨64⟩ :: endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
        (endCageIlkArtHashMem I vatOut) (UInt256.ofNat 9) vatOut
        (cA', endCageIlkPostArtAccountMap σ' I vatOut) k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd9144raw⟩
  have rd9201 := evm_run rd9144 with [
    raw dup3 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload64Hash (by decide) (by evm_ov),
    raw push4 ⟨0x6cb1c69b⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨225⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (endFlowVatIlksSelectorMem (endCageIlkArtHashMem I vatOut))
      (UInt256.ofNat 9) (by native_decide) mem_cost
      (by
        simp [endFlowVatIlksSelectorMem, endFlowVatIlksOutPtr, hselectorShift])
      (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 0 (endCageIlkSpotIlksCalldataMem I vatOut) (UInt256.ofNat 9)
      (by native_decide) mem_cost
      (by
        simp [endCageIlkSpotIlksCalldataMem, endFlowVatIlksCalldataMem,
          endFlowVatIlksArg0Mem, endFlowVatIlksOutPtr])
      (by decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload64Spot (by decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push4 endFlowVatIlksSelectorWord (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [σArt, endCageIlkSpotWord, endAddressReturnWord,
      endFlowVatIlksSelectorMem, endFlowVatIlksArg0Mem, endFlowVatIlksCalldataMem,
      endCageIlkSpotIlksCalldataMem, endFlowVatIlksOutPtr, endFlowVatIlksInSize,
      endFlowVatIlksEndPtr, endFlowVatIlksSelectorShifted, endFlowVatIlksSelectorWord,
      endSlotWord, solcSlotWord, solcAddrMask, hselectorShift, hspotMask, hinSize,
      hendPtr, u256_land_comm, key] using rd9201⟩

theorem endCageIlkX_spotIlksNoCode {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {vatOut : ByteArray} {k C : ℕ}
    (hsz36 : 36 ≤ I.calldata.size) (hperm : I.perm = true)
    (hlo : 160 ≤ vatOut.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9122⟩
      (endFlowVatIlkArtWord vatOut :: endCageIlkIlkWord I ::
        endCageIlkReturnPc :: sel :: [])
      (endCageIlkVatIlksPostCallMem I vatOut) (UInt256.ofNat 9)
      vatOut (cA', σ') k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord
        (endCageIlkPostArtAccountMap σ' I vatOut)
        (endCageIlkSpotWord (endCageIlkPostArtAccountMap σ' I vatOut) I) = ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd9201⟩ :=
    endCageIlkX_spotIlksExtcodesizeGuard hsz36 hperm hlo h
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨9201⟩) (okPc := ⟨9213⟩)
    rd9201 hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageIlkX_spotIlksCallReady {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {vatOut : ByteArray} {k C : ℕ}
    (hsz36 : 36 ≤ I.calldata.size) (hperm : I.perm = true)
    (hlo : 160 ≤ vatOut.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9122⟩
      (endFlowVatIlkArtWord vatOut :: endCageIlkIlkWord I ::
        endCageIlkReturnPc :: sel :: [])
      (endCageIlkVatIlksPostCallMem I vatOut) (UInt256.ofNat 9)
      vatOut (cA', σ') k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord
        (endCageIlkPostArtAccountMap σ' I vatOut)
        (endCageIlkSpotWord (endCageIlkPostArtAccountMap σ' I vatOut) I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9216⟩
      (gasWord :: endCageIlkSpotWord (endCageIlkPostArtAccountMap σ' I vatOut) I ::
        endFlowVatIlksOutPtr :: endFlowVatIlksInSize :: endFlowVatIlksOutPtr ::
        ⟨64⟩ :: endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endCageIlkSpotWord (endCageIlkPostArtAccountMap σ' I vatOut) I ::
        ⟨0⟩ :: endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      (endCageIlkSpotIlksCalldataMem I vatOut) (UInt256.ofNat 9)
      vatOut (cA', endCageIlkPostArtAccountMap σ' I vatOut) k' C' := by
  obtain ⟨_, _, rd9201⟩ :=
    endCageIlkX_spotIlksExtcodesizeGuard hsz36 hperm hlo h
  obtain ⟨gasWord, k', C', rd9216⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨9201⟩) (okPc := ⟨9213⟩)
      rd9201 hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd9216⟩

theorem endCageIlkX_spotIlksPostStaticcall {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {vatOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9216⟩
      (gasWord :: endCageIlkSpotWord (endCageIlkPostArtAccountMap σ' I vatOut) I ::
        endFlowVatIlksOutPtr :: endFlowVatIlksInSize :: endFlowVatIlksOutPtr ::
        ⟨64⟩ :: endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endCageIlkSpotWord (endCageIlkPostArtAccountMap σ' I vatOut) I ::
        ⟨0⟩ :: endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      (endCageIlkSpotIlksCalldataMem I vatOut) (UInt256.ofNat 9)
      vatOut (cA', endCageIlkPostArtAccountMap σ' I vatOut) k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap)
      (z : Bool) (spotOut : ByteArray) (Ain : Substate) (callGas : UInt256)
      (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA'', σ'', g'', A', z, spotOut) =
          Ethereum.EVM.Θ I.blobVersionedHashes cA' gh bl
            (endCageIlkPostArtAccountMap σ' I vatOut) σ₀ Ain
            (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
            (AccountAddress.ofUInt256
              (endCageIlkSpotWord (endCageIlkPostArtAccountMap σ' I vatOut) I))
            (toExecute (endCageIlkPostArtAccountMap σ' I vatOut)
              (AccountAddress.ofUInt256
                (endCageIlkSpotWord (endCageIlkPostArtAccountMap σ' I vatOut) I)))
            callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
            ((endCageIlkSpotIlksCalldataMem I vatOut).readWithPadding
              endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat)
            (I.depth + 1) I.header false)
      ∧ RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9217⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endFlowVatIlksEndPtr ::
            endFlowVatIlksSelectorWord ::
            endCageIlkSpotWord (endCageIlkPostArtAccountMap σ' I vatOut) I ::
            ⟨0⟩ :: endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
          (endCageIlkSpotIlksPostCallMem I vatOut spotOut) (UInt256.ofNat 9)
          spotOut (cA'', σ'') k' C'
      ∧ spotOut.size < UInt256.size := by
  obtain ⟨cA'', σ'', z, spotOut, Ain, callGas, k', C', hΘ, rd9217raw, hout⟩ :=
    RD.uniswapStaticcall h (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨cA'', σ'', z, spotOut, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · have hmin := endCageIlkSpotIlksWriteLen_eq (out := spotOut) hout
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
          endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat)
          endFlowVatIlksOutPtr.toNat (⟨64⟩ : UInt256).toNat) = UInt256.ofNat 9 := by
      unfold endFlowVatIlksOutPtr endFlowVatIlksInSize
      native_decide
    simpa [endCageIlkSpotIlksPostCallMem, endFlowVatIlksOutPtr,
      endFlowVatIlksInSize, endFlowVatIlksEndPtr, hmin, haw] using rd9217raw

theorem endCageIlkX_spotIlksStaticcallDepthLimit {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {vatOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9216⟩
      (gasWord :: endCageIlkSpotWord (endCageIlkPostArtAccountMap σ' I vatOut) I ::
        endFlowVatIlksOutPtr :: endFlowVatIlksInSize :: endFlowVatIlksOutPtr ::
        ⟨64⟩ :: endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endCageIlkSpotWord (endCageIlkPostArtAccountMap σ' I vatOut) I ::
        ⟨0⟩ :: endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      (endCageIlkSpotIlksCalldataMem I vatOut) (UInt256.ofNat 9)
      vatOut (cA', endCageIlkPostArtAccountMap σ' I vatOut) k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9217⟩
      (⟨0⟩ :: endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endCageIlkSpotWord (endCageIlkPostArtAccountMap σ' I vatOut) I ::
        ⟨0⟩ :: endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      (endCageIlkSpotIlksCalldataMem I vatOut) (UInt256.ofNat 9)
      ByteArray.empty (cA', endCageIlkPostArtAccountMap σ' I vatOut) k' C' := by
  obtain ⟨k', C', rd9217raw⟩ :=
    RD.uniswapStaticcallDepthLimit h (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin :
      (min (⟨64⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
        endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat)
        endFlowVatIlksOutPtr.toNat (⟨64⟩ : UInt256).toNat) = UInt256.ofNat 9 := by
    unfold endFlowVatIlksOutPtr endFlowVatIlksInSize
    native_decide
  simpa [endFlowVatIlksOutPtr, endFlowVatIlksInSize, endFlowVatIlksEndPtr,
    hmin, byteArray_write_len_zero, haw] using rd9217raw

theorem endCageIlkX_spotIlksCallFailed {cA cA' gh bl σ σTarget σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {vatOut : ByteArray} {mem rdata : ByteArray}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9217⟩
      (⟨0⟩ :: endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endCageIlkSpotWord (endCageIlkPostArtAccountMap σTarget I vatOut) I ::
        ⟨0⟩ :: endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata (cA', σ') k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨9217⟩) (okPc := ⟨9233⟩) h
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageIlkX_spotIlksCallSucceeded {cA cA' gh bl σ σTarget σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {vatOut : ByteArray} {mem rdata : ByteArray}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9217⟩
      (⟨1⟩ :: endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endCageIlkSpotWord (endCageIlkPostArtAccountMap σTarget I vatOut) I ::
        ⟨0⟩ :: endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])  
      mem (UInt256.ofNat 9) rdata (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9235⟩
      (endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endCageIlkSpotWord (endCageIlkPostArtAccountMap σTarget I vatOut) I ::
        ⟨0⟩ :: endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata (cA', σ') k' C' := by
  exact RD.uniswapCallSuccessGuardOk (pc := ⟨9217⟩) (okPc := ⟨9233⟩) h
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simp)

theorem endCageIlkX_spotIlksReturnDecodeOk {cA cA' gh bl σ σTarget σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {vatOut spotOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9235⟩
      (endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endCageIlkSpotWord (endCageIlkPostArtAccountMap σTarget I vatOut) I ::
        ⟨0⟩ :: endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      (endCageIlkSpotIlksPostCallMem I vatOut spotOut) (UInt256.ofNat 9)
      spotOut (cA', σ') k C)
    (hvat : 160 ≤ vatOut.size) (hlo : 64 ≤ spotOut.size)
    (hout : spotOut.size < UInt256.size) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9258⟩
      (endCageIlkSpotIlkPipWord spotOut :: ⟨0⟩ :: endCageIlkIlkWord I ::
        endCageIlkReturnPc :: sel :: [])
      (endCageIlkSpotIlksPostCallMem I vatOut spotOut) (UInt256.ofNat 9)
      spotOut (cA', σ') k' C' := by
  have hmload64 := endCageIlkSpotIlksPostCallMem_mload64 I vatOut spotOut hvat hout
  have hmload128 := endCageIlkSpotIlksPostCallMem_mload128 I vatOut spotOut hvat hout hlo
  have hlt : UInt256.lt (UInt256.ofNat spotOut.size) (⟨64⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, ulit_toNat' spotOut.size hout]
    exact hlo
  have rd9250 := evm_run h with [
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
    raw push2 ⟨9255⟩ (by native_decide) (by evm_ov)]
  have rdJump := rd9250
  rw [hlt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rdJump
  have rd9258 := evm_run rdJump with [
    raw jumpiT (by native_decide) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by jump_dest) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw mload 0 (endCageIlkSpotIlkPipWord spotOut) (UInt256.ofNat 9)
      (by native_decide) mem_cost hmload128 (by decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [endFlowVatIlksEndPtr, endFlowVatIlksSelectorWord] using rd9258⟩

theorem endCageIlkX_spotIlksReturnDecodeShort {cA cA' gh bl σ σTarget σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {vatOut spotOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9235⟩
      (endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endCageIlkSpotWord (endCageIlkPostArtAccountMap σTarget I vatOut) I ::
        ⟨0⟩ :: endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      (endCageIlkSpotIlksPostCallMem I vatOut spotOut) (UInt256.ofNat 9)
      spotOut (cA', σ') k C)
    (hvat : 160 ≤ vatOut.size) (hshort : spotOut.size < 64)
    (hout : spotOut.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hmload64 := endCageIlkSpotIlksPostCallMem_mload64 I vatOut spotOut hvat hout
  have hlt : UInt256.lt (UInt256.ofNat spotOut.size) (⟨64⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, ulit_toNat' spotOut.size hout]
    exact hshort
  have rd9250 := evm_run h with [
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
    raw push2 ⟨9255⟩ (by native_decide) (by evm_ov)]
  have rdShort := rd9250
  rw [hlt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rdShort
  have rdFall := rdShort.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.uniswapPush1Dup1Revert0 rdFall
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageIlkX_parExtcodesizeGuard {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {vatOut spotOut : ByteArray} {k C : ℕ}
    (hvat : 160 ≤ vatOut.size) (hspot : spotOut.size < UInt256.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9258⟩
      (endCageIlkSpotIlkPipWord spotOut :: ⟨0⟩ :: endCageIlkIlkWord I ::
        endCageIlkReturnPc :: sel :: [])
      (endCageIlkSpotIlksPostCallMem I vatOut spotOut) (UInt256.ofNat 9)
      spotOut (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9321⟩
      (endCageIlkSpotWord σ' I :: endCageIlkSpotWord σ' I ::
        endFlowVatIlksOutPtr :: endCageIlkNoArgInSize :: endFlowVatIlksOutPtr ::
        endCageIlkNoArgOutSize :: endCageIlkNoArgEndPtr :: endCageIlkParSelectorWord ::
        endCageIlkSpotWord σ' I :: ⟨9490⟩ :: endCageIlkSpotIlkPipWord spotOut ::
        endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      (endCageIlkParCalldataMem I vatOut spotOut) (UInt256.ofNat 9)
      spotOut (cA', σ') k' C' := by
  have hbaseSize :
      (endCageIlkSpotIlksPostCallMem I vatOut spotOut).size = 288 :=
    endCageIlkSpotIlksPostCallMem_size I vatOut spotOut hvat hspot
  have hbaseRead64 :
      (endCageIlkSpotIlksPostCallMem I vatOut spotOut).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    endCageIlkSpotIlksPostCallMem_read64 I vatOut spotOut hvat hspot
  have hselectorSize :
      (UInt256.shiftLeft endCageIlkParSelectorWord ⟨224⟩).toByteArray.size = 32 := by
    rw [toByteArray_size]
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endCageIlkSpotIlksPostCallMem I vatOut spotOut).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((endCageIlkSpotIlksPostCallMem I vatOut spotOut).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    endCageIlkSpotIlksPostCallMem_mload64 I vatOut spotOut hvat hspot
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endCageIlkParCalldataMem I vatOut spotOut).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((endCageIlkParCalldataMem I vatOut spotOut).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    unfold endCageIlkParCalldataMem
    exact endCageIlkNoArgCalldataMem_mload64 hselectorSize hbaseSize hbaseRead64
  have hspotMask :
      UInt256.land (endSlotWord ⟨6⟩ σ' I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        endCageIlkSpotWord σ' I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by native_decide]
  have hinSize :
      UInt256.sub endFlowVatIlksOutPtr endFlowVatIlksOutPtr + endCageIlkNoArgInSize =
        endCageIlkNoArgInSize := by
    native_decide
  have hendPtr : endFlowVatIlksOutPtr + endCageIlkNoArgInSize = endCageIlkNoArgEndPtr := by
    native_decide
  have rd9259 := evm_run h with [
    raw push1 ⟨6⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd9261raw⟩ := rd9259.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd9261⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9261⟩
        (endSlotWord ⟨6⟩ σ' I :: endCageIlkSpotIlkPipWord spotOut ::
          ⟨0⟩ :: endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
        (endCageIlkSpotIlksPostCallMem I vatOut spotOut) (UInt256.ofNat 9)
        spotOut (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd9261raw⟩
  have rd9321pre := evm_run rd9261 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw push4 endCageIlkParSelectorWord (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (endCageIlkParCalldataMem I vatOut spotOut) (UInt256.ofNat 9)
      (by native_decide) mem_cost
      (by simp [endCageIlkParCalldataMem, endCageIlkNoArgCalldataMem,
        endFlowVatIlksOutPtr])
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push2 ⟨9490⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push4 endCageIlkParSelectorWord (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    have rd9321norm := rd9321pre
    rw [hspotMask] at rd9321norm
    simpa [endCageIlkParCalldataMem, endCageIlkNoArgCalldataMem,
      endFlowVatIlksOutPtr, endCageIlkNoArgInSize, endCageIlkNoArgOutSize,
      endCageIlkNoArgEndPtr, hinSize, hendPtr] using rd9321norm⟩

theorem endCageIlkX_parNoCode {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {vatOut spotOut : ByteArray} {k C : ℕ}
    (hvat : 160 ≤ vatOut.size) (hspot : spotOut.size < UInt256.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9258⟩
      (endCageIlkSpotIlkPipWord spotOut :: ⟨0⟩ :: endCageIlkIlkWord I ::
        endCageIlkReturnPc :: sel :: [])
      (endCageIlkSpotIlksPostCallMem I vatOut spotOut) (UInt256.ofNat 9)
      spotOut (cA', σ') k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ' (endCageIlkSpotWord σ' I) = ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd9321⟩ := endCageIlkX_parExtcodesizeGuard hvat hspot h
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨9321⟩) (okPc := ⟨9333⟩)
    rd9321 hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageIlkX_parCallReady {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {vatOut spotOut : ByteArray} {k C : ℕ}
    (hvat : 160 ≤ vatOut.size) (hspot : spotOut.size < UInt256.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9258⟩
      (endCageIlkSpotIlkPipWord spotOut :: ⟨0⟩ :: endCageIlkIlkWord I ::
        endCageIlkReturnPc :: sel :: [])
      (endCageIlkSpotIlksPostCallMem I vatOut spotOut) (UInt256.ofNat 9)
      spotOut (cA', σ') k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ' (endCageIlkSpotWord σ' I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9336⟩
      (gasWord :: endCageIlkSpotWord σ' I :: endFlowVatIlksOutPtr ::
        endCageIlkNoArgInSize :: endFlowVatIlksOutPtr :: endCageIlkNoArgOutSize ::
        endCageIlkNoArgEndPtr :: endCageIlkParSelectorWord :: endCageIlkSpotWord σ' I ::
        ⟨9490⟩ :: endCageIlkSpotIlkPipWord spotOut :: endCageIlkIlkWord I ::
        endCageIlkReturnPc :: sel :: [])
      (endCageIlkParCalldataMem I vatOut spotOut) (UInt256.ofNat 9)
      spotOut (cA', σ') k' C' := by
  obtain ⟨_, _, rd9321⟩ := endCageIlkX_parExtcodesizeGuard hvat hspot h
  obtain ⟨gasWord, k', C', rd9336⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨9321⟩) (okPc := ⟨9333⟩)
      rd9321 hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd9336⟩

theorem endCageIlkX_parPostStaticcall {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {vatOut spotOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9336⟩
      (gasWord :: endCageIlkSpotWord σ' I :: endFlowVatIlksOutPtr ::
        endCageIlkNoArgInSize :: endFlowVatIlksOutPtr :: endCageIlkNoArgOutSize ::
        endCageIlkNoArgEndPtr :: endCageIlkParSelectorWord :: endCageIlkSpotWord σ' I ::
        ⟨9490⟩ :: endCageIlkSpotIlkPipWord spotOut :: endCageIlkIlkWord I ::
        endCageIlkReturnPc :: sel :: [])
      (endCageIlkParCalldataMem I vatOut spotOut) (UInt256.ofNat 9)
      spotOut (cA', σ') k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap)
      (z : Bool) (parOut : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA'', σ'', g'', A', z, parOut) =
          Ethereum.EVM.Θ I.blobVersionedHashes cA' gh bl σ' σ₀ Ain
            (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
            (AccountAddress.ofUInt256 (endCageIlkSpotWord σ' I))
            (toExecute σ' (AccountAddress.ofUInt256 (endCageIlkSpotWord σ' I)))
            callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
            ((endCageIlkParCalldataMem I vatOut spotOut).readWithPadding
              endFlowVatIlksOutPtr.toNat endCageIlkNoArgInSize.toNat)
            (I.depth + 1) I.header false)
      ∧ RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9337⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endCageIlkNoArgEndPtr ::
            endCageIlkParSelectorWord :: endCageIlkSpotWord σ' I :: ⟨9490⟩ ::
            endCageIlkSpotIlkPipWord spotOut :: endCageIlkIlkWord I ::
            endCageIlkReturnPc :: sel :: [])
          (endCageIlkParPostCallMem I vatOut spotOut parOut) (UInt256.ofNat 9)
          parOut (cA'', σ'') k' C'
      ∧ parOut.size < UInt256.size := by
  obtain ⟨cA'', σ'', z, parOut, Ain, callGas, k', C', hΘ, rd9337raw, hout⟩ :=
    RD.uniswapStaticcall h (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨cA'', σ'', z, parOut, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · have hmin := endCageIlkNoArgWriteLen_eq (out := parOut) hout
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
          endFlowVatIlksOutPtr.toNat endCageIlkNoArgInSize.toNat)
          endFlowVatIlksOutPtr.toNat endCageIlkNoArgOutSize.toNat) = UInt256.ofNat 9 := by
      unfold endFlowVatIlksOutPtr endCageIlkNoArgInSize endCageIlkNoArgOutSize
      native_decide
    simpa [endCageIlkParPostCallMem, endCageIlkNoArgPostCallMem,
      endFlowVatIlksOutPtr, endCageIlkNoArgInSize, endCageIlkNoArgOutSize,
      endCageIlkNoArgEndPtr, hmin, haw] using rd9337raw

theorem endCageIlkX_parStaticcallDepthLimit {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {vatOut spotOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9336⟩
      (gasWord :: endCageIlkSpotWord σ' I :: endFlowVatIlksOutPtr ::
        endCageIlkNoArgInSize :: endFlowVatIlksOutPtr :: endCageIlkNoArgOutSize ::
        endCageIlkNoArgEndPtr :: endCageIlkParSelectorWord :: endCageIlkSpotWord σ' I ::
        ⟨9490⟩ :: endCageIlkSpotIlkPipWord spotOut :: endCageIlkIlkWord I ::
        endCageIlkReturnPc :: sel :: [])
      (endCageIlkParCalldataMem I vatOut spotOut) (UInt256.ofNat 9)
      spotOut (cA', σ') k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9337⟩
      (⟨0⟩ :: endCageIlkNoArgEndPtr :: endCageIlkParSelectorWord ::
        endCageIlkSpotWord σ' I :: ⟨9490⟩ :: endCageIlkSpotIlkPipWord spotOut ::
        endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      (endCageIlkParCalldataMem I vatOut spotOut) (UInt256.ofNat 9)
      ByteArray.empty (cA', σ') k' C' := by
  obtain ⟨k', C', rd9337raw⟩ :=
    RD.uniswapStaticcallDepthLimit h (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
        endFlowVatIlksOutPtr.toNat endCageIlkNoArgInSize.toNat)
        endFlowVatIlksOutPtr.toNat endCageIlkNoArgOutSize.toNat) = UInt256.ofNat 9 := by
    unfold endFlowVatIlksOutPtr endCageIlkNoArgInSize endCageIlkNoArgOutSize
    native_decide
  simpa [endFlowVatIlksOutPtr, endCageIlkNoArgInSize, endCageIlkNoArgOutSize,
    endCageIlkNoArgEndPtr, hmin, byteArray_write_len_zero, haw] using rd9337raw

theorem endCageIlkX_parCallFailed {cA cA' gh bl σ σTarget σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {spotOut : ByteArray} {mem rdata : ByteArray}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9337⟩
      (⟨0⟩ :: endCageIlkNoArgEndPtr :: endCageIlkParSelectorWord ::
        endCageIlkSpotWord σTarget I :: ⟨9490⟩ :: endCageIlkSpotIlkPipWord spotOut ::
        endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata (cA', σ') k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨9337⟩) (okPc := ⟨9353⟩) h
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageIlkX_parCallSucceeded {cA cA' gh bl σ σTarget σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {spotOut : ByteArray} {mem rdata : ByteArray}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9337⟩
      (⟨1⟩ :: endCageIlkNoArgEndPtr :: endCageIlkParSelectorWord ::
        endCageIlkSpotWord σTarget I :: ⟨9490⟩ :: endCageIlkSpotIlkPipWord spotOut ::
        endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9355⟩
      (endCageIlkNoArgEndPtr :: endCageIlkParSelectorWord ::
        endCageIlkSpotWord σTarget I :: ⟨9490⟩ :: endCageIlkSpotIlkPipWord spotOut ::
        endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata (cA', σ') k' C' := by
  exact RD.uniswapCallSuccessGuardOk (pc := ⟨9337⟩) (okPc := ⟨9353⟩) h
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simp)

theorem endCageIlkX_parReturnDecodeOk {cA cA' gh bl σ σTarget σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {vatOut spotOut parOut : ByteArray} {k C : ℕ}
    (hvat : 160 ≤ vatOut.size) (hspot : spotOut.size < UInt256.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9355⟩
      (endCageIlkNoArgEndPtr :: endCageIlkParSelectorWord ::
        endCageIlkSpotWord σTarget I :: ⟨9490⟩ :: endCageIlkSpotIlkPipWord spotOut ::
        endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      (endCageIlkParPostCallMem I vatOut spotOut parOut) (UInt256.ofNat 9)
      parOut (cA', σ') k C)
    (hlo : 32 ≤ parOut.size) (hout : parOut.size < UInt256.size) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9378⟩
      (endCageIlkReturnWord parOut :: ⟨9490⟩ :: endCageIlkSpotIlkPipWord spotOut ::
        endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      (endCageIlkParPostCallMem I vatOut spotOut parOut) (UInt256.ofNat 9)
      parOut (cA', σ') k' C' := by
  have hbaseSize :
      (endCageIlkSpotIlksPostCallMem I vatOut spotOut).size = 288 :=
    endCageIlkSpotIlksPostCallMem_size I vatOut spotOut hvat hspot
  have hbaseRead64 :
      (endCageIlkSpotIlksPostCallMem I vatOut spotOut).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    endCageIlkSpotIlksPostCallMem_read64 I vatOut spotOut hvat hspot
  have hselectorSize :
      (UInt256.shiftLeft endCageIlkParSelectorWord ⟨224⟩).toByteArray.size = 32 := by
    rw [toByteArray_size]
  exact RD.solcUint256ReturnWordDecodeOk (pc := ⟨9355⟩) (okPc := ⟨9375⟩)
    (retWord := endCageIlkReturnWord parOut) h hlo hout
    mem_cost
    (by native_decide)
    (by
      unfold endCageIlkParPostCallMem
      exact endCageIlkNoArgPostCallMem_mload64 hselectorSize hbaseSize hbaseRead64 hout)
    (by
      unfold endCageIlkParPostCallMem
      exact endCageIlkNoArgPostCallMem_mload128 hselectorSize hbaseSize hout hlo)
    mem_cost
    (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by native_decide) (by native_decide) (by native_decide)
    (by simp)

theorem endCageIlkX_parReturnDecodeShort {cA cA' gh bl σ σTarget σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {vatOut spotOut parOut : ByteArray} {k C : ℕ}
    (hvat : 160 ≤ vatOut.size) (hspot : spotOut.size < UInt256.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9355⟩
      (endCageIlkNoArgEndPtr :: endCageIlkParSelectorWord ::
        endCageIlkSpotWord σTarget I :: ⟨9490⟩ :: endCageIlkSpotIlkPipWord spotOut ::
        endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      (endCageIlkParPostCallMem I vatOut spotOut parOut) (UInt256.ofNat 9)
      parOut (cA', σ') k C)
    (hshort : parOut.size < 32) (hout : parOut.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hbaseSize :
      (endCageIlkSpotIlksPostCallMem I vatOut spotOut).size = 288 :=
    endCageIlkSpotIlksPostCallMem_size I vatOut spotOut hvat hspot
  have hbaseRead64 :
      (endCageIlkSpotIlksPostCallMem I vatOut spotOut).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    endCageIlkSpotIlksPostCallMem_read64 I vatOut spotOut hvat hspot
  have hselectorSize :
      (UInt256.shiftLeft endCageIlkParSelectorWord ⟨224⟩).toByteArray.size = 32 := by
    rw [toByteArray_size]
  exact RD.solcUint256ReturnWordDecodeShortReverts (pc := ⟨9355⟩) (okPc := ⟨9375⟩)
    h hshort hout
    mem_cost
    (by native_decide)
    (by
      unfold endCageIlkParPostCallMem
      exact endCageIlkNoArgPostCallMem_mload64 hselectorSize hbaseSize hbaseRead64 hout)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    (by simp)

theorem endCageIlkX_readExtcodesizeGuard {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {vatOut spotOut parOut : ByteArray} {k C : ℕ}
    (hvat : 160 ≤ vatOut.size) (hspot : spotOut.size < UInt256.size)
    (hpar : parOut.size < UInt256.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9378⟩
      (endCageIlkReturnWord parOut :: ⟨9490⟩ :: endCageIlkSpotIlkPipWord spotOut ::
        endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      (endCageIlkParPostCallMem I vatOut spotOut parOut) (UInt256.ofNat 9)
      parOut (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9429⟩
      (endCageIlkPipCallWord spotOut :: endCageIlkPipCallWord spotOut ::
        endFlowVatIlksOutPtr :: endCageIlkNoArgInSize :: endFlowVatIlksOutPtr ::
        endCageIlkNoArgOutSize :: endCageIlkNoArgEndPtr :: endCageIlkReadSelectorWord ::
        endCageIlkPipCallWord spotOut :: endCageIlkReturnWord parOut :: ⟨9490⟩ ::
        endCageIlkSpotIlkPipWord spotOut :: endCageIlkIlkWord I ::
        endCageIlkReturnPc :: sel :: [])
      (endCageIlkReadCalldataMem I vatOut spotOut parOut) (UInt256.ofNat 9)
      parOut (cA', σ') k' C' := by
  have hspotMemSize :
      (endCageIlkSpotIlksPostCallMem I vatOut spotOut).size = 288 :=
    endCageIlkSpotIlksPostCallMem_size I vatOut spotOut hvat hspot
  have hspotMemRead64 :
      (endCageIlkSpotIlksPostCallMem I vatOut spotOut).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    endCageIlkSpotIlksPostCallMem_read64 I vatOut spotOut hvat hspot
  have hparSelectorSize :
      (UInt256.shiftLeft endCageIlkParSelectorWord ⟨224⟩).toByteArray.size = 32 := by
    rw [toByteArray_size]
  have hreadSelectorSize :
      (UInt256.shiftLeft endCageIlkReadSelectorRaw ⟨226⟩).toByteArray.size = 32 := by
    rw [toByteArray_size]
  have hbaseSize :
      (endCageIlkParPostCallMem I vatOut spotOut parOut).size = 288 := by
    unfold endCageIlkParPostCallMem
    exact endCageIlkNoArgPostCallMem_size hparSelectorSize hspotMemSize hpar
  have hbaseRead64 :
      (endCageIlkParPostCallMem I vatOut spotOut parOut).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ := by
    unfold endCageIlkParPostCallMem
    exact endCageIlkNoArgPostCallMem_read64 hparSelectorSize hspotMemSize
      hspotMemRead64 hpar
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endCageIlkParPostCallMem I vatOut spotOut parOut).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((endCageIlkParPostCallMem I vatOut spotOut parOut).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    unfold endCageIlkParPostCallMem
    exact endCageIlkNoArgPostCallMem_mload64 hparSelectorSize hspotMemSize
      hspotMemRead64 hpar
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endCageIlkReadCalldataMem I vatOut spotOut parOut).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((endCageIlkReadCalldataMem I vatOut spotOut parOut).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    unfold endCageIlkReadCalldataMem
    exact endCageIlkNoArgCalldataMem_mload64 hreadSelectorSize hbaseSize hbaseRead64
  have hpipMask :
      UInt256.land (endCageIlkSpotIlkPipWord spotOut)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        endCageIlkPipCallWord spotOut := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by native_decide]
  have hinSize :
      UInt256.sub endFlowVatIlksOutPtr endFlowVatIlksOutPtr + endCageIlkNoArgInSize =
        endCageIlkNoArgInSize := by
    native_decide
  have hendPtr : endFlowVatIlksOutPtr + endCageIlkNoArgInSize = endCageIlkNoArgEndPtr := by
    native_decide
  have rd9429pre := evm_run h with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw push4 endCageIlkReadSelectorRaw (by native_decide) (by evm_ov),
    raw push1 ⟨226⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (endCageIlkReadCalldataMem I vatOut spotOut parOut)
      (UInt256.ofNat 9) (by native_decide) mem_cost
      (by simp [endCageIlkReadCalldataMem, endCageIlkNoArgCalldataMem,
        endFlowVatIlksOutPtr])
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push4 endCageIlkReadSelectorWord (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    have rd9429norm := rd9429pre
    rw [hpipMask] at rd9429norm
    simpa [endCageIlkReadCalldataMem, endCageIlkNoArgCalldataMem,
      endFlowVatIlksOutPtr, endCageIlkNoArgInSize, endCageIlkNoArgOutSize,
      endCageIlkNoArgEndPtr, hinSize, hendPtr] using rd9429norm⟩

theorem endCageIlkX_readNoCode {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {vatOut spotOut parOut : ByteArray} {k C : ℕ}
    (hvat : 160 ≤ vatOut.size) (hspot : spotOut.size < UInt256.size)
    (hpar : parOut.size < UInt256.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9378⟩
      (endCageIlkReturnWord parOut :: ⟨9490⟩ :: endCageIlkSpotIlkPipWord spotOut ::
        endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      (endCageIlkParPostCallMem I vatOut spotOut parOut) (UInt256.ofNat 9)
      parOut (cA', σ') k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ' (endCageIlkPipCallWord spotOut) = ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd9429⟩ := endCageIlkX_readExtcodesizeGuard hvat hspot hpar h
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨9429⟩) (okPc := ⟨9441⟩)
    rd9429 hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageIlkX_readCallReady {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {vatOut spotOut parOut : ByteArray} {k C : ℕ}
    (hvat : 160 ≤ vatOut.size) (hspot : spotOut.size < UInt256.size)
    (hpar : parOut.size < UInt256.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9378⟩
      (endCageIlkReturnWord parOut :: ⟨9490⟩ :: endCageIlkSpotIlkPipWord spotOut ::
        endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      (endCageIlkParPostCallMem I vatOut spotOut parOut) (UInt256.ofNat 9)
      parOut (cA', σ') k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ' (endCageIlkPipCallWord spotOut) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9444⟩
      (gasWord :: endCageIlkPipCallWord spotOut :: endFlowVatIlksOutPtr ::
        endCageIlkNoArgInSize :: endFlowVatIlksOutPtr :: endCageIlkNoArgOutSize ::
        endCageIlkNoArgEndPtr :: endCageIlkReadSelectorWord ::
        endCageIlkPipCallWord spotOut :: endCageIlkReturnWord parOut :: ⟨9490⟩ ::
        endCageIlkSpotIlkPipWord spotOut :: endCageIlkIlkWord I ::
        endCageIlkReturnPc :: sel :: [])
      (endCageIlkReadCalldataMem I vatOut spotOut parOut) (UInt256.ofNat 9)
      parOut (cA', σ') k' C' := by
  obtain ⟨_, _, rd9429⟩ := endCageIlkX_readExtcodesizeGuard hvat hspot hpar h
  obtain ⟨gasWord, k', C', rd9444⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨9429⟩) (okPc := ⟨9441⟩)
      rd9429 hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd9444⟩

theorem endCageIlkX_readPostStaticcall {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {vatOut spotOut parOut : ByteArray}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9444⟩
      (gasWord :: endCageIlkPipCallWord spotOut :: endFlowVatIlksOutPtr ::
        endCageIlkNoArgInSize :: endFlowVatIlksOutPtr :: endCageIlkNoArgOutSize ::
        endCageIlkNoArgEndPtr :: endCageIlkReadSelectorWord ::
        endCageIlkPipCallWord spotOut :: endCageIlkReturnWord parOut :: ⟨9490⟩ ::
        endCageIlkSpotIlkPipWord spotOut :: endCageIlkIlkWord I ::
        endCageIlkReturnPc :: sel :: [])
      (endCageIlkReadCalldataMem I vatOut spotOut parOut) (UInt256.ofNat 9)
      parOut (cA', σ') k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap)
      (z : Bool) (readOut : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA'', σ'', g'', A', z, readOut) =
          Ethereum.EVM.Θ I.blobVersionedHashes cA' gh bl σ' σ₀ Ain
            (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
            (AccountAddress.ofUInt256 (endCageIlkPipCallWord spotOut))
            (toExecute σ' (AccountAddress.ofUInt256 (endCageIlkPipCallWord spotOut)))
            callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
            ((endCageIlkReadCalldataMem I vatOut spotOut parOut).readWithPadding
              endFlowVatIlksOutPtr.toNat endCageIlkNoArgInSize.toNat)
            (I.depth + 1) I.header false)
      ∧ RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9445⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endCageIlkNoArgEndPtr ::
            endCageIlkReadSelectorWord :: endCageIlkPipCallWord spotOut ::
            endCageIlkReturnWord parOut :: ⟨9490⟩ :: endCageIlkSpotIlkPipWord spotOut ::
            endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
          (endCageIlkReadPostCallMem I vatOut spotOut parOut readOut) (UInt256.ofNat 9)
          readOut (cA'', σ'') k' C'
      ∧ readOut.size < UInt256.size := by
  obtain ⟨cA'', σ'', z, readOut, Ain, callGas, k', C', hΘ, rd9445raw, hout⟩ :=
    RD.uniswapStaticcall h (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨cA'', σ'', z, readOut, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · have hmin := endCageIlkNoArgWriteLen_eq (out := readOut) hout
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
          endFlowVatIlksOutPtr.toNat endCageIlkNoArgInSize.toNat)
          endFlowVatIlksOutPtr.toNat endCageIlkNoArgOutSize.toNat) = UInt256.ofNat 9 := by
      unfold endFlowVatIlksOutPtr endCageIlkNoArgInSize endCageIlkNoArgOutSize
      native_decide
    simpa [endCageIlkReadPostCallMem, endCageIlkNoArgPostCallMem,
      endFlowVatIlksOutPtr, endCageIlkNoArgInSize, endCageIlkNoArgOutSize,
      endCageIlkNoArgEndPtr, hmin, haw] using rd9445raw

theorem endCageIlkX_readStaticcallDepthLimit {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {vatOut spotOut parOut : ByteArray}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9444⟩
      (gasWord :: endCageIlkPipCallWord spotOut :: endFlowVatIlksOutPtr ::
        endCageIlkNoArgInSize :: endFlowVatIlksOutPtr :: endCageIlkNoArgOutSize ::
        endCageIlkNoArgEndPtr :: endCageIlkReadSelectorWord ::
        endCageIlkPipCallWord spotOut :: endCageIlkReturnWord parOut :: ⟨9490⟩ ::
        endCageIlkSpotIlkPipWord spotOut :: endCageIlkIlkWord I ::
        endCageIlkReturnPc :: sel :: [])
      (endCageIlkReadCalldataMem I vatOut spotOut parOut) (UInt256.ofNat 9)
      parOut (cA', σ') k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9445⟩
      (⟨0⟩ :: endCageIlkNoArgEndPtr :: endCageIlkReadSelectorWord ::
        endCageIlkPipCallWord spotOut :: endCageIlkReturnWord parOut :: ⟨9490⟩ ::
        endCageIlkSpotIlkPipWord spotOut :: endCageIlkIlkWord I ::
        endCageIlkReturnPc :: sel :: [])
      (endCageIlkReadCalldataMem I vatOut spotOut parOut) (UInt256.ofNat 9)
      ByteArray.empty (cA', σ') k' C' := by
  obtain ⟨k', C', rd9445raw⟩ :=
    RD.uniswapStaticcallDepthLimit h (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
        endFlowVatIlksOutPtr.toNat endCageIlkNoArgInSize.toNat)
        endFlowVatIlksOutPtr.toNat endCageIlkNoArgOutSize.toNat) = UInt256.ofNat 9 := by
    unfold endFlowVatIlksOutPtr endCageIlkNoArgInSize endCageIlkNoArgOutSize
    native_decide
  simpa [endFlowVatIlksOutPtr, endCageIlkNoArgInSize, endCageIlkNoArgOutSize,
    endCageIlkNoArgEndPtr, hmin, byteArray_write_len_zero, haw] using rd9445raw

theorem endCageIlkX_readCallFailed {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel parWord : UInt256} {spotOut : ByteArray} {mem rdata : ByteArray}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9445⟩
      (⟨0⟩ :: endCageIlkNoArgEndPtr :: endCageIlkReadSelectorWord ::
        endCageIlkPipCallWord spotOut :: parWord :: ⟨9490⟩ ::
        endCageIlkSpotIlkPipWord spotOut :: endCageIlkIlkWord I ::
        endCageIlkReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata (cA', σ') k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨9445⟩) (okPc := ⟨9461⟩) h
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageIlkX_readCallSucceeded {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel parWord : UInt256} {spotOut : ByteArray} {mem rdata : ByteArray}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9445⟩
      (⟨1⟩ :: endCageIlkNoArgEndPtr :: endCageIlkReadSelectorWord ::
        endCageIlkPipCallWord spotOut :: parWord :: ⟨9490⟩ ::
        endCageIlkSpotIlkPipWord spotOut :: endCageIlkIlkWord I ::
        endCageIlkReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9463⟩
      (endCageIlkNoArgEndPtr :: endCageIlkReadSelectorWord ::
        endCageIlkPipCallWord spotOut :: parWord :: ⟨9490⟩ ::
        endCageIlkSpotIlkPipWord spotOut :: endCageIlkIlkWord I ::
        endCageIlkReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata (cA', σ') k' C' := by
  exact RD.uniswapCallSuccessGuardOk (pc := ⟨9445⟩) (okPc := ⟨9461⟩) h
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simp)

theorem endCageIlkX_readReturnDecodeOk {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {vatOut spotOut parOut readOut : ByteArray} {k C : ℕ}
    (hvat : 160 ≤ vatOut.size) (hspot : spotOut.size < UInt256.size)
    (hpar : parOut.size < UInt256.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9463⟩
      (endCageIlkNoArgEndPtr :: endCageIlkReadSelectorWord ::
        endCageIlkPipCallWord spotOut :: endCageIlkReturnWord parOut :: ⟨9490⟩ ::
        endCageIlkSpotIlkPipWord spotOut :: endCageIlkIlkWord I ::
        endCageIlkReturnPc :: sel :: [])
      (endCageIlkReadPostCallMem I vatOut spotOut parOut readOut) (UInt256.ofNat 9)
      readOut (cA', σ') k C)
    (hlo : 32 ≤ readOut.size) (hout : readOut.size < UInt256.size) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9486⟩
      (endCageIlkReturnWord readOut :: endCageIlkReturnWord parOut :: ⟨9490⟩ ::
        endCageIlkSpotIlkPipWord spotOut :: endCageIlkIlkWord I ::
        endCageIlkReturnPc :: sel :: [])
      (endCageIlkReadPostCallMem I vatOut spotOut parOut readOut) (UInt256.ofNat 9)
      readOut (cA', σ') k' C' := by
  have hspotMemSize :
      (endCageIlkSpotIlksPostCallMem I vatOut spotOut).size = 288 :=
    endCageIlkSpotIlksPostCallMem_size I vatOut spotOut hvat hspot
  have hspotMemRead64 :
      (endCageIlkSpotIlksPostCallMem I vatOut spotOut).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    endCageIlkSpotIlksPostCallMem_read64 I vatOut spotOut hvat hspot
  have hparSelectorSize :
      (UInt256.shiftLeft endCageIlkParSelectorWord ⟨224⟩).toByteArray.size = 32 := by
    rw [toByteArray_size]
  have hreadSelectorSize :
      (UInt256.shiftLeft endCageIlkReadSelectorRaw ⟨226⟩).toByteArray.size = 32 := by
    rw [toByteArray_size]
  have hbaseSize :
      (endCageIlkParPostCallMem I vatOut spotOut parOut).size = 288 := by
    unfold endCageIlkParPostCallMem
    exact endCageIlkNoArgPostCallMem_size hparSelectorSize hspotMemSize hpar
  have hbaseRead64 :
      (endCageIlkParPostCallMem I vatOut spotOut parOut).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ := by
    unfold endCageIlkParPostCallMem
    exact endCageIlkNoArgPostCallMem_read64 hparSelectorSize hspotMemSize
      hspotMemRead64 hpar
  exact RD.solcUint256ReturnWordDecodeOk (pc := ⟨9463⟩) (okPc := ⟨9483⟩)
    (retWord := endCageIlkReturnWord readOut) h hlo hout
    mem_cost
    (by native_decide)
    (by
      unfold endCageIlkReadPostCallMem
      exact endCageIlkNoArgPostCallMem_mload64 hreadSelectorSize hbaseSize
        hbaseRead64 hout)
    (by
      unfold endCageIlkReadPostCallMem
      exact endCageIlkNoArgPostCallMem_mload128 hreadSelectorSize hbaseSize hout hlo)
    mem_cost
    (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by native_decide) (by native_decide) (by native_decide)
    (by simp)

theorem endCageIlkX_readReturnDecodeShort {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {vatOut spotOut parOut readOut : ByteArray} {k C : ℕ}
    (hvat : 160 ≤ vatOut.size) (hspot : spotOut.size < UInt256.size)
    (hpar : parOut.size < UInt256.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9463⟩
      (endCageIlkNoArgEndPtr :: endCageIlkReadSelectorWord ::
        endCageIlkPipCallWord spotOut :: endCageIlkReturnWord parOut :: ⟨9490⟩ ::
        endCageIlkSpotIlkPipWord spotOut :: endCageIlkIlkWord I ::
        endCageIlkReturnPc :: sel :: [])
      (endCageIlkReadPostCallMem I vatOut spotOut parOut readOut) (UInt256.ofNat 9)
      readOut (cA', σ') k C)
    (hshort : readOut.size < 32) (hout : readOut.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hspotMemSize :
      (endCageIlkSpotIlksPostCallMem I vatOut spotOut).size = 288 :=
    endCageIlkSpotIlksPostCallMem_size I vatOut spotOut hvat hspot
  have hspotMemRead64 :
      (endCageIlkSpotIlksPostCallMem I vatOut spotOut).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    endCageIlkSpotIlksPostCallMem_read64 I vatOut spotOut hvat hspot
  have hparSelectorSize :
      (UInt256.shiftLeft endCageIlkParSelectorWord ⟨224⟩).toByteArray.size = 32 := by
    rw [toByteArray_size]
  have hreadSelectorSize :
      (UInt256.shiftLeft endCageIlkReadSelectorRaw ⟨226⟩).toByteArray.size = 32 := by
    rw [toByteArray_size]
  have hbaseSize :
      (endCageIlkParPostCallMem I vatOut spotOut parOut).size = 288 := by
    unfold endCageIlkParPostCallMem
    exact endCageIlkNoArgPostCallMem_size hparSelectorSize hspotMemSize hpar
  have hbaseRead64 :
      (endCageIlkParPostCallMem I vatOut spotOut parOut).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ := by
    unfold endCageIlkParPostCallMem
    exact endCageIlkNoArgPostCallMem_read64 hparSelectorSize hspotMemSize
      hspotMemRead64 hpar
  exact RD.solcUint256ReturnWordDecodeShortReverts (pc := ⟨9463⟩) (okPc := ⟨9483⟩)
    h hshort hout
    mem_cost
    (by native_decide)
    (by
      unfold endCageIlkReadPostCallMem
      exact endCageIlkNoArgPostCallMem_mload64 hreadSelectorSize hbaseSize
        hbaseRead64 hout)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    (by simp)

theorem endCageIlkX_wdivEntry {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {vatOut spotOut parOut readOut : ByteArray}
    {mem : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9486⟩
      (endCageIlkReturnWord readOut :: endCageIlkReturnWord parOut :: ⟨9490⟩ ::
        endCageIlkSpotIlkPipWord spotOut :: endCageIlkIlkWord I ::
        endCageIlkReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) readOut (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10170⟩
      (endWadWord :: endCageIlkReturnWord parOut :: ⟨10139⟩ ::
        endCageIlkReturnWord readOut :: ⟨0⟩ :: endCageIlkReturnWord readOut ::
        endCageIlkReturnWord parOut :: ⟨9490⟩ :: endCageIlkSpotIlkPipWord spotOut ::
        endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) readOut (cA', σ') k' C' := by
  have rd10231 := evm_run h with [
    raw push2 ⟨10231⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd10239pre := evm_run rd10231 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨10139⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov)]
  have rd10248 := rd10239pre.pushConst endWadWord
    (width := 8) (op := .PUSH8) (by decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd10170 := evm_run rd10248 with [
    raw push2 ⟨10170⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by simpa [endWadWord] using rd10170⟩

theorem endCageIlkInvalidError {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {stk : List UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.INVALID, .none)) :
    X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass ∨
      X (g.toNat + 1) (D_J code 0) s0 = .error .InvalidInstruction := by
  rcases RD.conclude h with hoog | ⟨k', C', s', hX, hcode, hpc, _hstk, _hgas, hk, hC,
    _hmem, _haw, _hrdata, _hacc⟩
  · exact Or.inl hoog
  · have hdec' : decode s'.executionEnv.code s'.machineState.pc = some (.INVALID, .none) := by
      rw [hcode, hpc]
      exact hdec
    have hstep : Xstep (D_J code 0) s' = .error .InvalidInstruction := by
      have hstep' := Ethereum.EVM.step_invalid s' hdec'
      simpa [hcode] using hstep'
    have hfuel : g.toNat + 1 - k' = (g.toNat + 1 - (k' + 1)) + 1 := by
      omega
    exact Or.inr (by
      rw [hX, hfuel]
      exact Ethereum.EVM.Xstep_X_X_except _ s' _ _ hstep)

theorem endCageIlkX_wdivMulOverflow {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {vatOut spotOut parOut readOut : ByteArray}
    {mem : ByteArray} {k C : ℕ}
    (hover : UInt256.size ≤ (endCageIlkReturnWord parOut).toNat * endWadWord.toNat)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9486⟩
      (endCageIlkReturnWord readOut :: endCageIlkReturnWord parOut :: ⟨9490⟩ ::
        endCageIlkSpotIlkPipWord spotOut :: endCageIlkIlkWord I ::
        endCageIlkReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) readOut (cA', σ') k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd10170⟩ := endCageIlkX_wdivEntry (vatOut := vatOut) h
  exact endFlowX_mulHelperOverflow
    (x := endCageIlkReturnWord parOut) (y := endWadWord) (ret := ⟨10139⟩)
    (R := [endCageIlkReturnWord readOut, ⟨0⟩, endCageIlkReturnWord readOut,
      endCageIlkReturnWord parOut, ⟨9490⟩, endCageIlkSpotIlkPipWord spotOut,
      endCageIlkIlkWord I, endCageIlkReturnPc, sel])
    (mem := mem) (rdata := readOut) (acc := (cA', σ')) hover rd10170
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageIlkX_wdivDivZeroInvalid {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {vatOut spotOut parOut readOut : ByteArray}
    {mem : ByteArray} {k C : ℕ}
    (hfit : (endCageIlkReturnWord parOut).toNat * endWadWord.toNat < UInt256.size)
    (hden : endCageIlkReturnWord readOut = ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9486⟩
      (endCageIlkReturnWord readOut :: endCageIlkReturnWord parOut :: ⟨9490⟩ ::
        endCageIlkSpotIlkPipWord spotOut :: endCageIlkIlkWord I ::
        endCageIlkReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) readOut (cA', σ') k C) :
    X (g.toNat + 1) (D_J endBytecode 0)
        (initState cA gh bl σ σ₀ g A I) = .error .OutOfGass ∨
      X (g.toNat + 1) (D_J endBytecode 0)
        (initState cA gh bl σ σ₀ g A I) = .error .InvalidInstruction := by
  obtain ⟨_, _, rd10170⟩ := endCageIlkX_wdivEntry (vatOut := vatOut) h
  have hWadNonzero : endWadWord ≠ ⟨0⟩ := by native_decide
  obtain ⟨_, _, rd10139⟩ :=
    endFlowX_mulHelperReturns
      (x := endCageIlkReturnWord parOut) (y := endWadWord) (ret := ⟨10139⟩)
      (R := [endCageIlkReturnWord readOut, ⟨0⟩, endCageIlkReturnWord readOut,
        endCageIlkReturnWord parOut, ⟨9490⟩, endCageIlkSpotIlkPipWord spotOut,
        endCageIlkIlkWord I, endCageIlkReturnPc, sel])
      (mem := mem) (rdata := readOut) (acc := (cA', σ')) hfit hWadNonzero rd10170
      (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  have rd10144 := evm_run rd10139 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨10146⟩ (by native_decide) (by evm_ov)]
  have rd10145 := rd10144.jumpiNT (by native_decide) (by simpa using hden) (by evm_ov)
  exact endCageIlkInvalidError rd10145 (by native_decide)

theorem endCageIlkX_wdivReturns {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {vatOut spotOut parOut readOut : ByteArray}
    {mem : ByteArray} {k C : ℕ}
    (hfit : (endCageIlkReturnWord parOut).toNat * endWadWord.toNat < UInt256.size)
    (hden : endCageIlkReturnWord readOut ≠ ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9486⟩
      (endCageIlkReturnWord readOut :: endCageIlkReturnWord parOut :: ⟨9490⟩ ::
        endCageIlkSpotIlkPipWord spotOut :: endCageIlkIlkWord I ::
        endCageIlkReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) readOut (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9490⟩
      (endCageIlkTagVWord parOut readOut :: endCageIlkSpotIlkPipWord spotOut ::
        endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) readOut (cA', σ') k' C' := by
  obtain ⟨_, _, rd10170⟩ := endCageIlkX_wdivEntry (vatOut := vatOut) h
  have hWadNonzero : endWadWord ≠ ⟨0⟩ := by native_decide
  obtain ⟨_, _, rd10139⟩ :=
    endFlowX_mulHelperReturns
      (x := endCageIlkReturnWord parOut) (y := endWadWord) (ret := ⟨10139⟩)
      (R := [endCageIlkReturnWord readOut, ⟨0⟩, endCageIlkReturnWord readOut,
        endCageIlkReturnWord parOut, ⟨9490⟩, endCageIlkSpotIlkPipWord spotOut,
        endCageIlkIlkWord I, endCageIlkReturnPc, sel])
      (mem := mem) (rdata := readOut) (acc := (cA', σ')) hfit hWadNonzero rd10170
      (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  have rd10144 := evm_run rd10139 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨10146⟩ (by native_decide) (by evm_ov)]
  have rd10146 := rd10144.jumpiT (by native_decide) hden (by jump_dest) (by evm_ov)
  have rd10153 := evm_run rd10146 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd9490raw := RD.jump (a := ⟨9490⟩)
    (t := [UInt256.div (endCageIlkReturnWord parOut * endWadWord)
        (endCageIlkReturnWord readOut),
      endCageIlkSpotIlkPipWord spotOut, endCageIlkIlkWord I, endCageIlkReturnPc, sel])
    rd10153 (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa [endCageIlkTagVWord, endCageIlkWdivProductWord] using rd9490raw⟩

theorem endCageIlkX_finish {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {vatOut spotOut parOut readOut : ByteArray} {k C : ℕ}
    (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size)
    (hvat : 160 ≤ vatOut.size) (hspotSize : spotOut.size < UInt256.size)
    (hparSize : parOut.size < UInt256.size) (hreadSize : readOut.size < UInt256.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9490⟩
      (endCageIlkTagVWord parOut readOut :: endCageIlkSpotIlkPipWord spotOut ::
        endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
      (endCageIlkReadPostCallMem I vatOut spotOut parOut readOut) (UInt256.ofNat 9)
      readOut (cA', σ') k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA', endCageIlkPostTagAccountMap σ' I (endCageIlkTagVWord parOut readOut))
      ByteArray.empty := by
  let key := endCageIlkIlkWord I
  let tagV := endCageIlkTagVWord parOut readOut
  let pip := endCageIlkSpotIlkPipWord spotOut
  let memBase := endCageIlkReadPostCallMem I vatOut spotOut parOut readOut
  let memHash := twoWordHashMem key ⟨12⟩ memBase
  have hspotMemSize :
      (endCageIlkSpotIlksPostCallMem I vatOut spotOut).size = 288 :=
    endCageIlkSpotIlksPostCallMem_size I vatOut spotOut hvat hspotSize
  have hspotMemRead64 :
      (endCageIlkSpotIlksPostCallMem I vatOut spotOut).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    endCageIlkSpotIlksPostCallMem_read64 I vatOut spotOut hvat hspotSize
  have hparSelectorSize :
      (UInt256.shiftLeft endCageIlkParSelectorWord ⟨224⟩).toByteArray.size = 32 := by
    rw [toByteArray_size]
  have hreadSelectorSize :
      (UInt256.shiftLeft endCageIlkReadSelectorRaw ⟨226⟩).toByteArray.size = 32 := by
    rw [toByteArray_size]
  have hparMemSize :
      (endCageIlkParPostCallMem I vatOut spotOut parOut).size = 288 := by
    unfold endCageIlkParPostCallMem
    exact endCageIlkNoArgPostCallMem_size hparSelectorSize hspotMemSize hparSize
  have hparMemRead64 :
      (endCageIlkParPostCallMem I vatOut spotOut parOut).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ := by
    unfold endCageIlkParPostCallMem
    exact endCageIlkNoArgPostCallMem_read64 hparSelectorSize hspotMemSize hspotMemRead64
      hparSize
  have hmemBaseSize : memBase.size = 288 := by
    unfold memBase endCageIlkReadPostCallMem
    exact endCageIlkNoArgPostCallMem_size hreadSelectorSize hparMemSize hreadSize
  have hmemBaseRead64 :
      memBase.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    unfold memBase endCageIlkReadPostCallMem
    exact endCageIlkNoArgPostCallMem_read64 hreadSelectorSize hparMemSize hparMemRead64
      hreadSize
  have hmemHashSize : memHash.size = 288 := by
    unfold memHash
    rw [endFlow_twoWordHashMem_size_of_ge64 key ⟨12⟩]
    · exact hmemBaseSize
    · rw [hmemBaseSize]
      omega
  have hmemHashRead64 :
      memHash.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    unfold memHash
    exact endCageIlk_twoWordHashMem_read64_of_ge96 key ⟨12⟩ (by rw [hmemBaseSize]; omega)
      hmemBaseRead64
  have hmload64Hash :
      (if (⟨64⟩ : UInt256).toNat ≥ memHash.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (memHash.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemHashSize]; decide) (by decide) hmemHashRead64
  have hslot : endCageIlkTagSlot I = solcMappingSlot ⟨12⟩ key := by
    simpa [key] using endCageIlkTagSlot_eq (I := I) hsz36
  have rd9495pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd9496 := rd9495pre.mstore 0 (wordAt0Mem key memBase)
    (UInt256.ofNat 9) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd9500pre := evm_run rd9496 with [
    raw push1 ⟨12⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd9501 := rd9500pre.mstore 0 memHash
    (UInt256.ofNat 9) (by native_decide) mem_cost
    (by
      change (UInt256.toByteArray (⟨12⟩ : UInt256)).write 0 (wordAt0Mem key memBase) 32 32 =
        wordAt32Mem ⟨12⟩ (wordAt0Mem key memBase)
      rfl)
    (by native_decide) (by evm_ov)
  have rd9505pre := evm_run rd9501 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memHash.readWithPadding 0 64))) =
          solcMappingSlot ⟨12⟩ key := by
    unfold memHash
    exact endFlow_twoWordHashMem_solcMappingSlot_of_ge64 ⟨12⟩ key
      (by rw [hmemBaseSize]; omega)
  have rd9506 := rd9505pre.keccak256 0 (solcMappingSlot ⟨12⟩ key)
    (UInt256.ofNat 9) (by native_decide) mem_cost
    (by
      simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hhash)
    (by native_decide) (by evm_ov)
  have rd9509pre := evm_run rd9506 with [
    raw swap3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov)]
  obtain ⟨k9510, C9510, rd9510raw⟩ := rd9509pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd9510 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9510⟩
      (⟨0⟩ :: ⟨64⟩ :: pip :: key :: endCageIlkReturnPc :: sel :: [])
      memHash (UInt256.ofNat 9) readOut
      (cA', endCageIlkPostTagAccountMap σ' I tagV) k9510 C9510 := by
    simpa [endCageIlkPostTagAccountMap, hslot, tagV, key, pip] using rd9510raw
  have rd9547pre := evm_run rd9510 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload64Hash (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rd9547 := rd9547pre.pushConst endCageIlkCageIlkLogTopic
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd9548 := evm_run rd9547 with [
    raw swap2 (by native_decide) (by evm_ov)]
  have rdLog := RD.log2
    (a := ⟨128⟩) (b := ⟨0⟩) (c := endCageIlkCageIlkLogTopic) (d := key)
    (t := [pip, key, endCageIlkReturnPc, sel])
    0
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat 9).toNat (⟨128⟩ : UInt256).toNat
        (⟨0⟩ : UInt256).toNat))
    rd9548 (by native_decide) hperm mem_cost (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd9550 := RD.pop (a := pip) (t := [key, endCageIlkReturnPc, sel]) rdLog
    (by native_decide) (by evm_ov)
  have rd9551 := RD.pop (a := key) (t := [endCageIlkReturnPc, sel]) rd9550
    (by native_decide) (by evm_ov)
  have rd562 := RD.jump (a := endCageIlkReturnPc) (t := [sel]) rd9551
    (by native_decide) (by jump_dest) (by evm_ov)
  have rd563 := RD.jumpdest (pc := endCageIlkReturnPc) (stk := [sel]) rd562
    (by native_decide) (by evm_ov)
  exact RD.stop rd563 (by native_decide) (by evm_ov)

theorem evalStorageRef_endCageIlk_live (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := endCageIlkStore I } evm
      liveRef = .ok endCageIlkLiveEvaledRef := by
  simp [endCageIlkLiveEvaledRef, liveRef, evalStorageRef, evalStorageRefSteps,
    EvalResult.bind, pure, bind]

theorem evalExpr_endCageIlk_live_zero_false (evm : EVM.State) (I : ExecutionEnv)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endCageIlkStore I } evm
      (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm
        (.storage liveRef) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := endCageIlkStore I })
      (slot := liveRef)
      (er := endCageIlkLiveEvaledRef)
      (t := .int uint256Int)
      (loc := wordLoc ⟨8⟩)
      (hbase := by simp [endCageIlkStore, liveRef])
      (her := evalStorageRef_endCageIlk_live evm I)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by exact endStorageLocLoad_uint256 evm ⟨8⟩)
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat) ≠
        Value.int 0 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    exact uint256_toNat_eq_zero (Int.ofNat.inj hbad)
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat) ==
        Value.int 0) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat))
      (Value.int 0) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem evalExpr_endCageIlk_ilk (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endCageIlkStore I } evm (.var "ilk") =
      .ok (endCageIlkIlkValue I) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((endCageIlkStore I).get? "ilk") =
    .ok (endCageIlkIlkValue I)
  rw [endCageIlkStore, store_get_self]
  rfl

theorem evalStorageRef_endCageIlk_tag (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := endCageIlkStore I } evm
      (tagRef (.var "ilk")) = .ok (endCageIlkTagEvaledRef I) := by
  have hargLen : min 32 (I.calldata.toList.length - 4) = bytes32Width.val + 1 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [htlen]
    simp [bytes32Width]
    omega
  have hilk := evalExpr_endCageIlk_ilk evm I
  simp [endCageIlkTagEvaledRef, endCageIlkIlkKey, hilk, endCageIlkIlkValue,
    endBytes32ArgValue, endBytes32ArgKey, endBytes32ArgBytes, evalStorageRef,
    evalStorageRefSteps, evalStorageRefStep, tagRef, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, pure, bind]
  rw [if_pos hargLen]

theorem evalExpr_endCageIlk_tag (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := endCageIlkStore I } evm
      (.storage (tagRef (.var "ilk"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (endCageIlkTagSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := endCageIlkStore I })
    (slot := tagRef (.var "ilk"))
    (er := endCageIlkTagEvaledRef I)
    (t := .int uint256Int)
    (loc := wordLoc (endCageIlkTagSlot I))
    (hbase := by simp [endCageIlkStore, tagRef])
    (her := evalStorageRef_endCageIlk_tag evm I hsz36)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := endStorageLocLoad_uint256 evm (endCageIlkTagSlot I))

theorem evalExpr_endCageIlk_tag_eq_false (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size)
    (htag :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endCageIlkTagSlot I) ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endCageIlkStore I } evm
      (.binary .eq (.storage (tagRef (.var "ilk"))) (.intLit 0)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm
        (.storage (tagRef (.var "ilk"))) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (endCageIlkTagSlot I)).toNat)) :=
    evalExpr_endCageIlk_tag evm I hsz36
  have hzero :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  apply endEvalExpr_eq_int_false hstorage hzero
  intro hbad
  apply htag
  exact uint256_toNat_eq_zero (Int.ofNat.inj hbad)

theorem evalExpr_endCageIlk_live_zero_true (evm : EVM.State) (I : ExecutionEnv)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endCageIlkStore I } evm
      (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm
        (.storage liveRef) = .ok (.int 0) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := endCageIlkStore I })
      (slot := liveRef)
      (er := endCageIlkLiveEvaledRef)
      (t := .int uint256Int)
      (loc := wordLoc ⟨8⟩)
      (value := .int 0)
      (hbase := by simp [endCageIlkStore, liveRef])
      (her := evalStorageRef_endCageIlk_live evm I)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by simpa [hlive] using endStorageLocLoad_uint256 evm ⟨8⟩)]
  have hzero :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  exact endEvalExpr_eq_int_true hstorage hzero rfl

theorem evalExpr_endCageIlk_tag_eq_true (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size)
    (htag :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endCageIlkTagSlot I) = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endCageIlkStore I } evm
      (.binary .eq (.storage (tagRef (.var "ilk"))) (.intLit 0)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm
        (.storage (tagRef (.var "ilk"))) = .ok (.int 0) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := endCageIlkStore I })
      (slot := tagRef (.var "ilk"))
      (er := endCageIlkTagEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (endCageIlkTagSlot I))
      (value := .int 0)
      (hbase := by simp [endCageIlkStore, tagRef])
      (her := evalStorageRef_endCageIlk_tag evm I hsz36)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by
        simpa [htag] using endStorageLocLoad_uint256 evm (endCageIlkTagSlot I))]
  have hzero :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  exact endEvalExpr_eq_int_true hstorage hzero rfl

theorem endCageIlkVatIlksDecode_ok_aux {out : ByteArray} (hlo : 160 ≤ out.size) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
        [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256] out =
      some [.int (Int.ofNat (endFlowVatIlkArtWord out).toNat),
        .int (Int.ofNat (endFlowVatIlkRateWord out).toNat),
        .int (Int.ofNat (endFlowVatIlkSpotWord out).toNat),
        .int (Int.ofNat (endFlowVatIlkLineWord out).toNat),
        .int (Int.ofNat (endFlowVatIlkDustWord out).toNat)] := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
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
  have hword0 := endCageIlk_bytesToWord_drop_take32_eq_extract out 0
  have hword32 := endCageIlk_bytesToWord_drop_take32_eq_extract out 32
  have hword64 := endCageIlk_bytesToWord_drop_take32_eq_extract out 64
  have hword96 := endCageIlk_bytesToWord_drop_take32_eq_extract out 96
  have hword128 := endCageIlk_bytesToWord_drop_take32_eq_extract out 128
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq
    (types := [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256])
    (bytes := out.toList) (cursor := 0)
    (total := 32 * [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256].length)
    (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := out.toList) (start := 0) htake0]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := out.toList) (start := 32) htake32]
  simp only [Option.bind_some]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := out.toList) (start := 64) htake64]
  simp only [Option.bind_some]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := out.toList) (start := 96) htake96]
  simp only [Option.bind_some]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := out.toList) (start := 128) htake128]
  simp only [Option.bind_some]
  rw [hword0, hword32, hword64, hword96, hword128]

theorem endCageIlkVatIlksDecode_ok {out : ByteArray} (hlo : 160 ≤ out.size) :
    config.externalABI.decode? "vatIlks" out =
      some [.int (Int.ofNat (endFlowVatIlkArtWord out).toNat),
        .int (Int.ofNat (endFlowVatIlkRateWord out).toNat),
        .int (Int.ofNat (endFlowVatIlkSpotWord out).toNat),
        .int (Int.ofNat (endFlowVatIlkLineWord out).toNat),
        .int (Int.ofNat (endFlowVatIlkDustWord out).toNat)] := by
  have h := endCageIlkVatIlksDecode_ok_aux (out := out) hlo
  simpa [config, externalABI, uint256, uint256Int, abiUInt256] using h

theorem endCageIlkVatIlksDecode_none_short_aux {out : ByteArray} (hshort : out.size < 160) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
        [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256] out = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq
    (types := [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256])
    (bytes := out.toList) (cursor := 0)
    (total := 32 * [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256].length)
    (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  by_cases htake0 : ((out.toList.drop 0).take 32).length = 32
  · rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
      (bytes := out.toList) (start := 0) htake0]
    simp only [Option.bind_eq_bind, Option.bind_some]
    by_cases htake32 : ((out.toList.drop 32).take 32).length = 32
    · rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 32) htake32]
      simp only [Option.bind_some]
      by_cases htake64 : ((out.toList.drop 64).take 32).length = 32
      · rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
          (bytes := out.toList) (start := 64) htake64]
        simp only [Option.bind_some]
        by_cases htake96 : ((out.toList.drop 96).take 32).length = 32
        · rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
            (bytes := out.toList) (start := 96) htake96]
          simp only [Option.bind_some]
          have htake128 :
              ¬ ((out.toList.drop 128).take 32).length = 32 := by
            rw [List.length_take, List.length_drop, hlen]
            omega
          rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
            (bytes := out.toList) (start := 128) htake128]
          simp
        · rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
            (bytes := out.toList) (start := 96) htake96]
          simp
      · rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
          (bytes := out.toList) (start := 64) htake64]
        simp
    · rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 32) htake32]
      simp
  · rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
      (bytes := out.toList) (start := 0) htake0]
    simp

theorem endCageIlkVatIlksDecode_none_short {out : ByteArray} (hshort : out.size < 160) :
    config.externalABI.decode? "vatIlks" out = none := by
  have h := endCageIlkVatIlksDecode_none_short_aux (out := out) hshort
  simpa [config, externalABI, uint256, uint256Int, abiUInt256] using h

theorem endCageIlkSpotIlksDecode_none_short {out : ByteArray} (hshort : out.size < 64) :
    config.externalABI.decode? "spotIlks" out = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  change ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [addr, uint256] out = none
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq (types := [addr, uint256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [addr, uint256]) (bytes := out.toList) (cursor := 0)
    (total := 32 * [addr, uint256].length) (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  by_cases htake0 : ((out.toList.drop 0).take 32).length = 32
  · have haddrDec :
        decodeScalarWordWithMode? DecodeMode.legacySolc05 addr out.toList 0 =
          some (.address (AccountAddress.ofNat
            (ABI.bytesToWord ((out.toList.drop 0).take 32)).toNat), 0 + 32) := by
      simpa [addr, abiAddress] using
        decodeScalarWord_legacyAddress_ok (bytes := out.toList) (start := 0)
          (by simpa using htake0)
    rw [haddrDec]
    simp only [Option.bind_eq_bind, Option.bind_some]
    have htake32 : ¬ ((out.toList.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop, hlen]
      omega
    have huintShort :
        decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList (0 + 32) =
          none := by
      simpa [uint256, abiUInt256] using
        decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
          (bytes := out.toList) (start := 32) htake32
    rw [huintShort]
    simp
  · have haddrShort :
        decodeScalarWordWithMode? DecodeMode.legacySolc05 addr out.toList 0 = none := by
      simpa [addr, abiAddress] using
        decodeScalarWord_legacyAddress_none_short (bytes := out.toList) (start := 0)
          (by simpa using htake0)
    rw [haddrShort]
    simp

theorem endCageIlkParDecode_none_short {out : ByteArray} (hshort : out.size < 32) :
    config.externalABI.decode? "par" out = none := by
  change decodeReturn? uint256 out = none
  unfold decodeReturn?
  have hdec :
      decodeReturnValueWithMode? DecodeMode.legacySolc05 uint256 out = none := by
    simpa [uint256, abiUInt256] using
      decodeReturnValueWithMode_legacy_uint256_none_short (returndata := out) hshort
  rw [hdec]
  rfl

theorem endCageIlkReadDecode_none_short {out : ByteArray} (hshort : out.size < 32) :
    config.externalABI.decode? "read" out = none := by
  change decodeReturn? bytes32 out = none
  unfold decodeReturn?
  change Option.map (fun v => [v])
      (ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 abiBytes32 out) = none
  have hdec :
      ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 abiBytes32 out = none := by
    unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValuesWithMode?
    rw [show abiTupleHeadSize? [abiBytes32] = some 32 by native_decide]
    simp only [bind, Option.bind]
    have hlen : out.toList.length = out.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    have hread : readBytes? out.toList 0 32 = none := by
      unfold readBytes?
      have htake0 : ¬ ((out.toList.drop 0).take 32).length = 32 := by
        rw [List.drop_zero, List.length_take, hlen]
        omega
      rw [if_neg htake0]
    have hdecValues :
        decodeABIValues? [abiBytes32] out.toList 0 0 32 32 DecodeMode.legacySolc05 =
          none := by
      simp [decodeABIValues?, decodeABIValue?, abiBytes32, abiBytes32Width,
        ABI.isDynamicABIType, staticABIEncodedSize?, hread]
    rw [hdecValues]
  rw [hdec]
  rfl

theorem endCageIlk_evalExpr_spot {locals : Store} (evm : EVM.State)
    (hbase : locals.get? "spot" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage spotRef) =
      .ok (.address
        (AccountAddress.ofNat (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := spotRef)
    (er := ({ base := "spot", steps := [] } : EvaledStorageRef))
    (t := .address)
    (loc := addrLoc ⟨6⟩)
    (value :=
      .address (AccountAddress.ofNat
        (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat))
    (hbase := hbase)
    (her := by
      simp [evalStorageRef, evalStorageRefSteps, spotRef, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (hloc := by rfl)
    (hload := by
      simpa [endCageIlkSpotWord, endAddressReturnWord, endSlotWord, solcSlotWord,
        Solm.EVM.storageLoad, State.lookupAccount] using
        endStorageLocLoad_address_offset0 evm ⟨6⟩)

theorem endCageIlkAddressWordCode_zero_of_state {evm : EVM.State} (target : UInt256)
    (hzero : Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap target = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount (AccountAddress.ofNat target.toNat)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
  simpa [State.lookupAccount] using
    endUniswapExtCodeSizeWord_zero_lookup_code_zero
      (σ := evm.accountMap) (target := target)
      (addr := AccountAddress.ofNat target.toNat)
      (accountAddress_ofUInt256_eq_ofNat_toNat target).symm hzero

theorem endCageIlkAddressWordCode_pos_of_state {evm : EVM.State} (target : UInt256)
    (hne : Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap target ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((evm.lookupAccount (AccountAddress.ofNat target.toNat)).option 0
        (fun acc => acc.code.size))).toNat := by
  simpa [State.lookupAccount] using
    endUniswapExtCodeSizeWord_ne_zero_lookup_code_pos
      (σ := evm.accountMap) (target := target)
      (addr := AccountAddress.ofNat target.toNat)
      (accountAddress_ofUInt256_eq_ofNat_toNat target).symm hne

theorem endCageIlkPipAddr_eq_ofUInt256 (out : ByteArray) :
    endCageIlkSpotIlkPipAddr out =
      AccountAddress.ofUInt256 (endCageIlkPipCallWord out) := by
  have haddr :
      endCageIlkSpotIlkPipAddr out =
        AccountAddress.ofNat
          (UInt256.land solcAddrMask (endCageIlkSpotIlkPipWord out)).toNat := by
    have h := solcAddressValue_masked (endCageIlkSpotIlkPipWord out)
    simpa [endCageIlkSpotIlkPipAddr] using
      congrArg
        (fun v =>
          match v with
          | .address a => a
          | _ => (0 : AccountAddress))
        h
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  simpa [endCageIlkPipCallWord, u256_land_comm] using haddr

theorem endCageIlkAddress_ofUInt256 (w : UInt256) :
    EVM.address (AccountAddress.ofUInt256 w) = AccountAddress.ofUInt256 w := by
  apply Fin.ext
  show ↑(AccountAddress.ofUInt256 w) % EVM.twoPow 160 = ↑(AccountAddress.ofUInt256 w)
  rw [Nat.mod_eq_of_lt]
  exact (AccountAddress.ofUInt256 w).isLt

theorem endCageIlkSpotWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    endCageIlkSpotWord σ I = endCageIlkSpotWord τ I := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨6⟩ ⟨0⟩
  simpa [endCageIlkSpotWord, endAddressReturnWord, endSlotWord, solcSlotWord] using
    congrArg (fun w => UInt256.land w solcAddrMask) hslot

theorem endCageIlkSpotCodeSize_zero_EVMStateEquiv {evm₁ evm₂ : EVM.State}
    (hState : EVMStateEquiv evm₁ evm₂)
    (hcode :
      Reasoning.Theory.uniswapExtCodeSizeWord evm₁.accountMap
        (endCageIlkSpotWord evm₁.accountMap evm₁.executionEnv) = ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord evm₂.accountMap
        (endCageIlkSpotWord evm₂.accountMap evm₂.executionEnv) = ⟨0⟩ := by
  have htarget :
      endCageIlkSpotWord evm₁.accountMap evm₁.executionEnv =
        endCageIlkSpotWord evm₂.accountMap evm₂.executionEnv := by
    rw [← hState.executionEnv]
    exact endCageIlkSpotWord_accountMapEquiv hState.accountMap
  have hcodeEq :=
    Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hState.accountMap
      (endCageIlkSpotWord evm₁.accountMap evm₁.executionEnv)
  rw [← htarget, ← hcodeEq]
  exact hcode

theorem endCageIlkSpotCodeSize_ne_EVMStateEquiv {evm₁ evm₂ : EVM.State}
    (hState : EVMStateEquiv evm₁ evm₂)
    (hcode :
      Reasoning.Theory.uniswapExtCodeSizeWord evm₁.accountMap
        (endCageIlkSpotWord evm₁.accountMap evm₁.executionEnv) ≠ ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord evm₂.accountMap
        (endCageIlkSpotWord evm₂.accountMap evm₂.executionEnv) ≠ ⟨0⟩ := by
  intro hbad
  have htarget :
      endCageIlkSpotWord evm₁.accountMap evm₁.executionEnv =
        endCageIlkSpotWord evm₂.accountMap evm₂.executionEnv := by
    rw [← hState.executionEnv]
    exact endCageIlkSpotWord_accountMapEquiv hState.accountMap
  have hcodeEq :=
    Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hState.accountMap
      (endCageIlkSpotWord evm₁.accountMap evm₁.executionEnv)
  rw [← htarget, ← hcodeEq] at hbad
  exact hcode hbad

theorem endCageIlkPipCodeSize_zero_accountMapEquiv {σ τ : AccountMap}
    (hAccounts : accountMapEquiv σ τ) (spotOut : ByteArray)
    (hcode :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (endCageIlkPipCallWord spotOut) = ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ (endCageIlkPipCallWord spotOut) = ⟨0⟩ := by
  rw [← Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccounts
    (endCageIlkPipCallWord spotOut)]
  exact hcode

theorem endCageIlkPipCodeSize_ne_accountMapEquiv {σ τ : AccountMap}
    (hAccounts : accountMapEquiv σ τ) (spotOut : ByteArray)
    (hcode :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (endCageIlkPipCallWord spotOut) ≠ ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ (endCageIlkPipCallWord spotOut) ≠ ⟨0⟩ := by
  intro hbad
  rw [← Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccounts
    (endCageIlkPipCallWord spotOut)] at hbad
  exact hcode hbad

theorem endCageIlkCheckedVatIlksNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (endPackVatWord σ I) = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := endCageIlkStore I } evm0
      (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
        "vatIlk") .reverted := by
  intro evm0
  have hreceiver :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm0
        (.storage vatRef) = .ok (.address (endPackVatAddr σ I)) := by
    have hbase : (endCageIlkStore I).get? "vat" = none := by
      simp [endCageIlkStore]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endPack_vat (locals := endCageIlkStore I) evm0 hbase
  have hcodeZero :
      (UInt256.ofNat
        ((evm0.lookupAccount (endPackVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat =
        0 := by
    simpa [evm0] using
      endPackVatCode_zero_of_codeSize_zero
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  simpa [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm0)
      (locals := endCageIlkStore I) (receiver := .storage vatRef)
      (retVar := "vatIlk") (name := "vatIlks") (sendVal := 0)
      (args := [.var "ilk"]) (perm := true) hguard

theorem endCageIlkCheckedVatIlksFailure {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat : EVM.State} {out : ByteArray}
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "vatIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (false, evmVat, out) true) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := endCageIlkStore I } evm0
      (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
        "vatIlk") .reverted := by
  intro evm0
  have hreceiver :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm0
        (.storage vatRef) = .ok (.address (endPackVatAddr σ I)) := by
    have hbase : (endCageIlkStore I).get? "vat" = none := by
      simp [endCageIlkStore]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endPack_vat (locals := endCageIlkStore I) evm0 hbase
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm0.lookupAccount (endPackVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
    simpa [evm0] using
      endPackVatCode_pos_of_codeSize_ne
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hilk :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm0 (.var "ilk") =
        .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((endCageIlkStore I).get? "ilk") =
      .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I))
    rw [endCageIlkStore, store_get_self]
    rfl
  have hargs :
      evalExprs? config { contract := contract, locals := endCageIlkStore I } evm0 [.var "ilk"] =
        .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I)] := by
    simp [evalExprs?, hilk, EvalResult.bind, bind, pure]
  simpa [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config) (C := contract) (evm := evm0) (evm' := evmVat)
      (locals := endCageIlkStore I) (receiver := .storage vatRef)
      (retVar := "vatIlk") (name := "vatIlks") (target := endPackVatAddr σ I)
      (sendVal := 0) (args := [.var "ilk"])
      (argVals := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
      (out := out) (perm := true) hguard hreceiver hargs (by simpa [evm0] using hcall)

theorem endCageIlkCheckedVatIlksDecodeRevert {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat : EVM.State} {out : ByteArray}
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "vatIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmVat, out) true)
    (hshort : out.size < 160) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := endCageIlkStore I } evm0
      (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
        "vatIlk") .reverted := by
  intro evm0
  have hreceiver :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm0
        (.storage vatRef) = .ok (.address (endPackVatAddr σ I)) := by
    have hbase : (endCageIlkStore I).get? "vat" = none := by
      simp [endCageIlkStore]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endPack_vat (locals := endCageIlkStore I) evm0 hbase
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm0.lookupAccount (endPackVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
    simpa [evm0] using
      endPackVatCode_pos_of_codeSize_ne
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hilk :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm0 (.var "ilk") =
        .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((endCageIlkStore I).get? "ilk") =
      .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I))
    rw [endCageIlkStore, store_get_self]
    rfl
  have hargs :
      evalExprs? config { contract := contract, locals := endCageIlkStore I } evm0 [.var "ilk"] =
        .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I)] := by
    simp [evalExprs?, hilk, EvalResult.bind, bind, pure]
  simpa [checkedExternalCallStmts] using
    checkedExternalCallDecodeRevert
      (cfg := config) (C := contract) (evm := evm0) (evm' := evmVat)
      (locals := endCageIlkStore I) (receiver := .storage vatRef)
      (retVar := "vatIlk") (name := "vatIlks") (target := endPackVatAddr σ I)
      (sendVal := 0) (args := [.var "ilk"])
      (argVals := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
      (out := out) (perm := true) hguard hreceiver hargs
      (by simpa [evm0] using hcall) (endCageIlkVatIlksDecode_none_short hshort)

theorem endCageIlkCheckedVatIlksSuccess {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat : EVM.State} {out : ByteArray}
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "vatIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmVat, out) true)
    (hlo : 160 ≤ out.size) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := endCageIlkStore I } evm0
      (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
        "vatIlk")
      (.ok { contract := contract, locals := endCageIlkStoreVatIlk I out } evmVat) := by
  intro evm0
  have hreceiver :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm0
        (.storage vatRef) = .ok (.address (endPackVatAddr σ I)) := by
    have hbase : (endCageIlkStore I).get? "vat" = none := by
      simp [endCageIlkStore]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endPack_vat (locals := endCageIlkStore I) evm0 hbase
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm0.lookupAccount (endPackVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
    simpa [evm0] using
      endPackVatCode_pos_of_codeSize_ne
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hilk :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm0 (.var "ilk") =
        .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((endCageIlkStore I).get? "ilk") =
      .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I))
    rw [endCageIlkStore, store_get_self]
    rfl
  have hargs :
      evalExprs? config { contract := contract, locals := endCageIlkStore I } evm0 [.var "ilk"] =
        .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I)] := by
    simp [evalExprs?, hilk, EvalResult.bind, bind, pure]
  have hvalue := endCageIlkVatIlksDecode_ok (out := out) hlo
  have hblock := checkedExternalCallSuccess
    (cfg := config) (C := contract) (evm := evm0) (evm' := evmVat)
    (locals := endCageIlkStore I) (receiver := .storage vatRef)
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
  simpa [checkedExternalCallStmts, endCageIlkStoreVatIlk, collapseReturns] using hblock

theorem endCageIlkCheckedSpotIlksNoCode (evm : EVM.State) (I : ExecutionEnv)
    (vatOut : ByteArray)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (endCageIlkSpotWord evm.accountMap evm.executionEnv) = ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut } evm
      (checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"]
        "spotIlk" (perm := false)) .reverted := by
  have hreceiver :
      evalExpr? config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut } evm
        (.storage spotRef) =
          .ok (.address
            (AccountAddress.ofNat (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat)) := by
    exact endCageIlk_evalExpr_spot evm (by simp [endCageIlkStoreVatIlk, endCageIlkStore, spotRef])
  have hcodeZero :
      (UInt256.ofNat
        ((evm.lookupAccount
          (AccountAddress.ofNat
            (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat)).option 0
          (fun acc => acc.code.size))).toNat = 0 :=
    endCageIlkAddressWordCode_zero_of_state
      (endCageIlkSpotWord evm.accountMap evm.executionEnv) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut } evm
        (.binary .gt (.extCodeSize (.storage spotRef)) (.intLit 0)) = .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  simpa [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm)
      (locals := endCageIlkStoreVatIlk I vatOut) (receiver := .storage spotRef)
      (retVar := "spotIlk") (name := "spotIlks") (sendVal := 0)
      (args := [.var "ilk"]) (perm := false) hguard

theorem endCageIlkCheckedSpotIlksFailure {evm evm' : EVM.State}
    {I : ExecutionEnv} {vatOut spotOut : ByteArray}
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (endCageIlkSpotWord evm.accountMap evm.executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address
          (AccountAddress.ofNat (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat))
        "spotIlks" 0 [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (false, evm', spotOut) false) :
    ExecBlock config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut } evm
      (checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"]
        "spotIlk" (perm := false)) .reverted := by
  have hreceiver :
      evalExpr? config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut } evm
        (.storage spotRef) =
          .ok (.address
            (AccountAddress.ofNat (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat)) := by
    exact endCageIlk_evalExpr_spot evm (by simp [endCageIlkStoreVatIlk, endCageIlkStore, spotRef])
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm.lookupAccount
          (AccountAddress.ofNat
            (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat)).option 0
          (fun acc => acc.code.size))).toNat :=
    endCageIlkAddressWordCode_pos_of_state
      (endCageIlkSpotWord evm.accountMap evm.executionEnv) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut } evm
        (.binary .gt (.extCodeSize (.storage spotRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hilk :
      evalExpr? config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut } evm
        (.var "ilk") = .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((endCageIlkStoreVatIlk I vatOut).get? "ilk") =
      .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I))
    rw [endCageIlkStoreVatIlk, store_get_ne _ _ (by decide), endCageIlkStore,
      store_get_self]
    rfl
  have hargs :
      evalExprs? config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut } evm
        [.var "ilk"] = .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I)] := by
    simp [evalExprs?, hilk, EvalResult.bind, bind, pure]
  simpa [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config) (C := contract) (evm := evm) (evm' := evm')
      (locals := endCageIlkStoreVatIlk I vatOut) (receiver := .storage spotRef)
      (retVar := "spotIlk") (name := "spotIlks")
      (target := AccountAddress.ofNat (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat)
      (sendVal := 0) (args := [.var "ilk"])
      (argVals := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
      (out := spotOut) (perm := false) hguard hreceiver hargs hcall

theorem endCageIlkCheckedSpotIlksDecodeRevert {evm evm' : EVM.State}
    {I : ExecutionEnv} {vatOut spotOut : ByteArray}
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (endCageIlkSpotWord evm.accountMap evm.executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address
          (AccountAddress.ofNat (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat))
        "spotIlks" 0 [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evm', spotOut) false)
    (hshort : spotOut.size < 64) :
    ExecBlock config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut } evm
      (checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"]
        "spotIlk" (perm := false)) .reverted := by
  have hreceiver :
      evalExpr? config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut } evm
        (.storage spotRef) =
          .ok (.address
            (AccountAddress.ofNat (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat)) := by
    exact endCageIlk_evalExpr_spot evm (by simp [endCageIlkStoreVatIlk, endCageIlkStore, spotRef])
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm.lookupAccount
          (AccountAddress.ofNat
            (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat)).option 0
          (fun acc => acc.code.size))).toNat :=
    endCageIlkAddressWordCode_pos_of_state
      (endCageIlkSpotWord evm.accountMap evm.executionEnv) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut } evm
        (.binary .gt (.extCodeSize (.storage spotRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hilk :
      evalExpr? config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut } evm
        (.var "ilk") = .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((endCageIlkStoreVatIlk I vatOut).get? "ilk") =
      .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I))
    rw [endCageIlkStoreVatIlk, store_get_ne _ _ (by decide), endCageIlkStore,
      store_get_self]
    rfl
  have hargs :
      evalExprs? config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut } evm
        [.var "ilk"] = .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I)] := by
    simp [evalExprs?, hilk, EvalResult.bind, bind, pure]
  simpa [checkedExternalCallStmts] using
    checkedExternalCallDecodeRevert
      (cfg := config) (C := contract) (evm := evm) (evm' := evm')
      (locals := endCageIlkStoreVatIlk I vatOut) (receiver := .storage spotRef)
      (retVar := "spotIlk") (name := "spotIlks")
      (target := AccountAddress.ofNat (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat)
      (sendVal := 0) (args := [.var "ilk"])
      (argVals := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
      (out := spotOut) (perm := false) hguard hreceiver hargs hcall
      (endCageIlkSpotIlksDecode_none_short hshort)

theorem endCageIlkCheckedSpotIlksSuccess {evm evm' : EVM.State}
    {I : ExecutionEnv} {vatOut spotOut : ByteArray}
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (endCageIlkSpotWord evm.accountMap evm.executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address
          (AccountAddress.ofNat (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat))
        "spotIlks" 0 [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evm', spotOut) false)
    (hlo : 64 ≤ spotOut.size) :
    ExecBlock config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut } evm
      (checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"]
        "spotIlk" (perm := false))
      (.ok { contract := contract, locals := endCageIlkStoreSpotIlk I vatOut spotOut }
        evm') := by
  have hreceiver :
      evalExpr? config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut } evm
        (.storage spotRef) =
          .ok (.address
            (AccountAddress.ofNat (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat)) := by
    exact endCageIlk_evalExpr_spot evm (by simp [endCageIlkStoreVatIlk, endCageIlkStore, spotRef])
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm.lookupAccount
          (AccountAddress.ofNat
            (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat)).option 0
          (fun acc => acc.code.size))).toNat :=
    endCageIlkAddressWordCode_pos_of_state
      (endCageIlkSpotWord evm.accountMap evm.executionEnv) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut } evm
        (.binary .gt (.extCodeSize (.storage spotRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hilk :
      evalExpr? config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut } evm
        (.var "ilk") = .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((endCageIlkStoreVatIlk I vatOut).get? "ilk") =
      .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I))
    rw [endCageIlkStoreVatIlk, store_get_ne _ _ (by decide), endCageIlkStore,
      store_get_self]
    rfl
  have hargs :
      evalExprs? config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut } evm
        [.var "ilk"] = .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I)] := by
    simp [evalExprs?, hilk, EvalResult.bind, bind, pure]
  have hvalue := endCageIlkSpotIlksDecode_ok (out := spotOut) hlo
  have hblock := checkedExternalCallSuccess
    (cfg := config) (C := contract) (evm := evm) (evm' := evm')
    (locals := endCageIlkStoreVatIlk I vatOut) (receiver := .storage spotRef)
    (retVar := "spotIlk") (name := "spotIlks")
    (target := AccountAddress.ofNat (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat)
    (sendVal := 0) (args := [.var "ilk"])
    (argVals := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
    (out := spotOut) (perm := false)
    (value := [.address (endCageIlkSpotIlkPipAddr spotOut),
      .int (Int.ofNat (endCageIlkSpotIlkMatWord spotOut).toNat)])
    hguard hreceiver hargs hcall hvalue
  simpa [checkedExternalCallStmts, endCageIlkStoreSpotIlk, collapseReturns] using hblock

theorem endCageIlk_evalExpr_pip {I : ExecutionEnv} {vatOut spotOut parOut : ByteArray}
    (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := endCageIlkStorePar I vatOut spotOut parOut }
      evm (.var "pip") = .ok (.address (endCageIlkSpotIlkPipAddr spotOut)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable
      ((endCageIlkStorePar I vatOut spotOut parOut).get? "pip") =
    .ok (.address (endCageIlkSpotIlkPipAddr spotOut))
  rw [endCageIlkStorePar, store_get_ne _ _ (by decide), endCageIlkStorePip,
    store_get_self]
  rfl

theorem endCageIlkCheckedParNoCode (evm : EVM.State) (I : ExecutionEnv)
    (vatOut spotOut : ByteArray)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (endCageIlkSpotWord evm.accountMap evm.executionEnv) = ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endCageIlkStorePip I vatOut spotOut } evm
      (checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
        (perm := false)) .reverted := by
  have hreceiver :
      evalExpr? config { contract := contract, locals := endCageIlkStorePip I vatOut spotOut } evm
        (.storage spotRef) =
          .ok (.address
            (AccountAddress.ofNat (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat)) := by
    exact endCageIlk_evalExpr_spot evm
      (by simp [endCageIlkStorePip, endCageIlkStoreSpotIlk, endCageIlkStoreVatIlk,
        endCageIlkStore])
  have hcodeZero :
      (UInt256.ofNat
        ((evm.lookupAccount
          (AccountAddress.ofNat
            (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat)).option 0
          (fun acc => acc.code.size))).toNat = 0 :=
    endCageIlkAddressWordCode_zero_of_state
      (endCageIlkSpotWord evm.accountMap evm.executionEnv) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endCageIlkStorePip I vatOut spotOut } evm
        (.binary .gt (.extCodeSize (.storage spotRef)) (.intLit 0)) = .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  simpa [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm)
      (locals := endCageIlkStorePip I vatOut spotOut) (receiver := .storage spotRef)
      (retVar := "parV") (name := "par") (sendVal := 0)
      (args := []) (perm := false) hguard

theorem endCageIlkCheckedParFailure {evm evm' : EVM.State}
    {I : ExecutionEnv} {vatOut spotOut parOut : ByteArray}
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (endCageIlkSpotWord evm.accountMap evm.executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address
          (AccountAddress.ofNat (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat))
        "par" 0 [] (false, evm', parOut) false) :
    ExecBlock config { contract := contract, locals := endCageIlkStorePip I vatOut spotOut } evm
      (checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
        (perm := false)) .reverted := by
  have hreceiver :
      evalExpr? config { contract := contract, locals := endCageIlkStorePip I vatOut spotOut } evm
        (.storage spotRef) =
          .ok (.address
            (AccountAddress.ofNat (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat)) := by
    exact endCageIlk_evalExpr_spot evm
      (by simp [endCageIlkStorePip, endCageIlkStoreSpotIlk, endCageIlkStoreVatIlk,
        endCageIlkStore])
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm.lookupAccount
          (AccountAddress.ofNat
            (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat)).option 0
          (fun acc => acc.code.size))).toNat :=
    endCageIlkAddressWordCode_pos_of_state
      (endCageIlkSpotWord evm.accountMap evm.executionEnv) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endCageIlkStorePip I vatOut spotOut } evm
        (.binary .gt (.extCodeSize (.storage spotRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs :
      evalExprs? config { contract := contract, locals := endCageIlkStorePip I vatOut spotOut } evm
        [] = .ok [] := by
    simp [evalExprs?, pure]
  simpa [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config) (C := contract) (evm := evm) (evm' := evm')
      (locals := endCageIlkStorePip I vatOut spotOut) (receiver := .storage spotRef)
      (retVar := "parV") (name := "par")
      (target := AccountAddress.ofNat (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat)
      (sendVal := 0) (args := []) (argVals := [])
      (out := parOut) (perm := false) hguard hreceiver hargs hcall

theorem endCageIlkCheckedParDecodeRevert {evm evm' : EVM.State}
    {I : ExecutionEnv} {vatOut spotOut parOut : ByteArray}
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (endCageIlkSpotWord evm.accountMap evm.executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address
          (AccountAddress.ofNat (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat))
        "par" 0 [] (true, evm', parOut) false)
    (hshort : parOut.size < 32) :
    ExecBlock config { contract := contract, locals := endCageIlkStorePip I vatOut spotOut } evm
      (checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
        (perm := false)) .reverted := by
  have hreceiver :
      evalExpr? config { contract := contract, locals := endCageIlkStorePip I vatOut spotOut } evm
        (.storage spotRef) =
          .ok (.address
            (AccountAddress.ofNat (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat)) := by
    exact endCageIlk_evalExpr_spot evm
      (by simp [endCageIlkStorePip, endCageIlkStoreSpotIlk, endCageIlkStoreVatIlk,
        endCageIlkStore])
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm.lookupAccount
          (AccountAddress.ofNat
            (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat)).option 0
          (fun acc => acc.code.size))).toNat :=
    endCageIlkAddressWordCode_pos_of_state
      (endCageIlkSpotWord evm.accountMap evm.executionEnv) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endCageIlkStorePip I vatOut spotOut } evm
        (.binary .gt (.extCodeSize (.storage spotRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs :
      evalExprs? config { contract := contract, locals := endCageIlkStorePip I vatOut spotOut } evm
        [] = .ok [] := by
    simp [evalExprs?, pure]
  simpa [checkedExternalCallStmts] using
    checkedExternalCallDecodeRevert
      (cfg := config) (C := contract) (evm := evm) (evm' := evm')
      (locals := endCageIlkStorePip I vatOut spotOut) (receiver := .storage spotRef)
      (retVar := "parV") (name := "par")
      (target := AccountAddress.ofNat (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat)
      (sendVal := 0) (args := []) (argVals := [])
      (out := parOut) (perm := false) hguard hreceiver hargs hcall
      (endCageIlkParDecode_none_short hshort)

theorem endCageIlkCheckedParSuccess {evm evm' : EVM.State}
    {I : ExecutionEnv} {vatOut spotOut parOut : ByteArray}
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (endCageIlkSpotWord evm.accountMap evm.executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address
          (AccountAddress.ofNat (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat))
        "par" 0 [] (true, evm', parOut) false)
    (hlo : 32 ≤ parOut.size) :
    ExecBlock config { contract := contract, locals := endCageIlkStorePip I vatOut spotOut } evm
      (checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
        (perm := false))
      (.ok { contract := contract, locals := endCageIlkStorePar I vatOut spotOut parOut }
        evm') := by
  have hreceiver :
      evalExpr? config { contract := contract, locals := endCageIlkStorePip I vatOut spotOut } evm
        (.storage spotRef) =
          .ok (.address
            (AccountAddress.ofNat (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat)) := by
    exact endCageIlk_evalExpr_spot evm
      (by simp [endCageIlkStorePip, endCageIlkStoreSpotIlk, endCageIlkStoreVatIlk,
        endCageIlkStore])
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm.lookupAccount
          (AccountAddress.ofNat
            (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat)).option 0
          (fun acc => acc.code.size))).toNat :=
    endCageIlkAddressWordCode_pos_of_state
      (endCageIlkSpotWord evm.accountMap evm.executionEnv) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endCageIlkStorePip I vatOut spotOut } evm
        (.binary .gt (.extCodeSize (.storage spotRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs :
      evalExprs? config { contract := contract, locals := endCageIlkStorePip I vatOut spotOut } evm
        [] = .ok [] := by
    simp [evalExprs?, pure]
  have hvalue := endCageIlkParDecode_ok (out := parOut) hlo
  have hblock := checkedExternalCallSuccess
    (cfg := config) (C := contract) (evm := evm) (evm' := evm')
    (locals := endCageIlkStorePip I vatOut spotOut) (receiver := .storage spotRef)
    (retVar := "parV") (name := "par")
    (target := AccountAddress.ofNat (endCageIlkSpotWord evm.accountMap evm.executionEnv).toNat)
    (sendVal := 0) (args := []) (argVals := [])
    (out := parOut) (perm := false)
    (value := [.int (Int.ofNat (endCageIlkReturnWord parOut).toNat)])
    hguard hreceiver hargs hcall hvalue
  simpa [checkedExternalCallStmts, endCageIlkStorePar, collapseReturns] using hblock

theorem endCageIlkCheckedReadNoCode (evm : EVM.State) (I : ExecutionEnv)
    (vatOut spotOut parOut : ByteArray)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (endCageIlkPipCallWord spotOut) = ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endCageIlkStorePar I vatOut spotOut parOut } evm
      (checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
        (perm := false)) .reverted := by
  have hreceiver :
      evalExpr? config { contract := contract, locals := endCageIlkStorePar I vatOut spotOut parOut }
        evm (.var "pip") = .ok (.address (endCageIlkSpotIlkPipAddr spotOut)) :=
    endCageIlk_evalExpr_pip evm
  have hcodeZero :
      (UInt256.ofNat
        ((evm.lookupAccount (endCageIlkSpotIlkPipAddr spotOut)).option 0
          (fun acc => acc.code.size))).toNat = 0 := by
    rw [endCageIlkPipAddr_eq_ofUInt256 spotOut, accountAddress_ofUInt256_eq_ofNat_toNat]
    exact endCageIlkAddressWordCode_zero_of_state
      (evm := evm) (endCageIlkPipCallWord spotOut) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endCageIlkStorePar I vatOut spotOut parOut }
        evm (.binary .gt (.extCodeSize (.var "pip")) (.intLit 0)) = .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  simpa [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm)
      (locals := endCageIlkStorePar I vatOut spotOut parOut) (receiver := .var "pip")
      (retVar := "pipRead") (name := "read") (sendVal := 0)
      (args := []) (perm := false) hguard

theorem endCageIlkCheckedReadFailure {evm evm' : EVM.State}
    {I : ExecutionEnv} {vatOut spotOut parOut readOut : ByteArray}
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (endCageIlkPipCallWord spotOut) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (endCageIlkSpotIlkPipAddr spotOut))
        "read" 0 [] (false, evm', readOut) false) :
    ExecBlock config { contract := contract, locals := endCageIlkStorePar I vatOut spotOut parOut } evm
      (checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
        (perm := false)) .reverted := by
  have hreceiver :
      evalExpr? config { contract := contract, locals := endCageIlkStorePar I vatOut spotOut parOut }
        evm (.var "pip") = .ok (.address (endCageIlkSpotIlkPipAddr spotOut)) :=
    endCageIlk_evalExpr_pip evm
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (endCageIlkSpotIlkPipAddr spotOut)).option 0
          (fun acc => acc.code.size))).toNat := by
    rw [endCageIlkPipAddr_eq_ofUInt256 spotOut, accountAddress_ofUInt256_eq_ofNat_toNat]
    exact endCageIlkAddressWordCode_pos_of_state
      (evm := evm) (endCageIlkPipCallWord spotOut) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endCageIlkStorePar I vatOut spotOut parOut }
        evm (.binary .gt (.extCodeSize (.var "pip")) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs :
      evalExprs? config { contract := contract, locals := endCageIlkStorePar I vatOut spotOut parOut }
        evm [] = .ok [] := by
    simp [evalExprs?, pure]
  simpa [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config) (C := contract) (evm := evm) (evm' := evm')
      (locals := endCageIlkStorePar I vatOut spotOut parOut) (receiver := .var "pip")
      (retVar := "pipRead") (name := "read")
      (target := endCageIlkSpotIlkPipAddr spotOut)
      (sendVal := 0) (args := []) (argVals := [])
      (out := readOut) (perm := false) hguard hreceiver hargs hcall

theorem endCageIlkCheckedReadDecodeRevert {evm evm' : EVM.State}
    {I : ExecutionEnv} {vatOut spotOut parOut readOut : ByteArray}
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (endCageIlkPipCallWord spotOut) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (endCageIlkSpotIlkPipAddr spotOut))
        "read" 0 [] (true, evm', readOut) false)
    (hshort : readOut.size < 32) :
    ExecBlock config { contract := contract, locals := endCageIlkStorePar I vatOut spotOut parOut } evm
      (checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
        (perm := false)) .reverted := by
  have hreceiver :
      evalExpr? config { contract := contract, locals := endCageIlkStorePar I vatOut spotOut parOut }
        evm (.var "pip") = .ok (.address (endCageIlkSpotIlkPipAddr spotOut)) :=
    endCageIlk_evalExpr_pip evm
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (endCageIlkSpotIlkPipAddr spotOut)).option 0
          (fun acc => acc.code.size))).toNat := by
    rw [endCageIlkPipAddr_eq_ofUInt256 spotOut, accountAddress_ofUInt256_eq_ofNat_toNat]
    exact endCageIlkAddressWordCode_pos_of_state
      (evm := evm) (endCageIlkPipCallWord spotOut) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endCageIlkStorePar I vatOut spotOut parOut }
        evm (.binary .gt (.extCodeSize (.var "pip")) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs :
      evalExprs? config { contract := contract, locals := endCageIlkStorePar I vatOut spotOut parOut }
        evm [] = .ok [] := by
    simp [evalExprs?, pure]
  simpa [checkedExternalCallStmts] using
    checkedExternalCallDecodeRevert
      (cfg := config) (C := contract) (evm := evm) (evm' := evm')
      (locals := endCageIlkStorePar I vatOut spotOut parOut) (receiver := .var "pip")
      (retVar := "pipRead") (name := "read")
      (target := endCageIlkSpotIlkPipAddr spotOut)
      (sendVal := 0) (args := []) (argVals := [])
      (out := readOut) (perm := false) hguard hreceiver hargs hcall
      (endCageIlkReadDecode_none_short hshort)

theorem endCageIlkCheckedReadSuccess {evm evm' : EVM.State}
    {I : ExecutionEnv} {vatOut spotOut parOut readOut : ByteArray}
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (endCageIlkPipCallWord spotOut) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (endCageIlkSpotIlkPipAddr spotOut))
        "read" 0 [] (true, evm', readOut) false)
    (hlo : 32 ≤ readOut.size) :
    ExecBlock config { contract := contract, locals := endCageIlkStorePar I vatOut spotOut parOut } evm
      (checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
        (perm := false))
      (.ok { contract := contract, locals := endCageIlkStoreRead I vatOut spotOut parOut readOut }
        evm') := by
  have hreceiver :
      evalExpr? config { contract := contract, locals := endCageIlkStorePar I vatOut spotOut parOut }
        evm (.var "pip") = .ok (.address (endCageIlkSpotIlkPipAddr spotOut)) :=
    endCageIlk_evalExpr_pip evm
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (endCageIlkSpotIlkPipAddr spotOut)).option 0
          (fun acc => acc.code.size))).toNat := by
    rw [endCageIlkPipAddr_eq_ofUInt256 spotOut, accountAddress_ofUInt256_eq_ofNat_toNat]
    exact endCageIlkAddressWordCode_pos_of_state
      (evm := evm) (endCageIlkPipCallWord spotOut) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endCageIlkStorePar I vatOut spotOut parOut }
        evm (.binary .gt (.extCodeSize (.var "pip")) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs :
      evalExprs? config { contract := contract, locals := endCageIlkStorePar I vatOut spotOut parOut }
        evm [] = .ok [] := by
    simp [evalExprs?, pure]
  have hvalue := endCageIlkReadDecode_ok (out := readOut) hlo
  have hblock := checkedExternalCallSuccess
    (cfg := config) (C := contract) (evm := evm) (evm' := evm')
    (locals := endCageIlkStorePar I vatOut spotOut parOut) (receiver := .var "pip")
    (retVar := "pipRead") (name := "read")
    (target := endCageIlkSpotIlkPipAddr spotOut)
    (sendVal := 0) (args := []) (argVals := [])
    (out := readOut) (perm := false)
    (value := [.fixedBytes bytes32Width (endCageIlkReadBytes readOut)])
    hguard hreceiver hargs hcall hvalue
  simpa [checkedExternalCallStmts, endCageIlkStoreRead, collapseReturns] using hblock

theorem evalExpr_endCageIlk_vatIlk_art (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    evalExpr? config { contract := contract, locals := endCageIlkStoreVatIlk I out } evm
      (.tupleGet (.var "vatIlk") 0) =
        .ok (.int (Int.ofNat (endFlowVatIlkArtWord out).toNat)) := by
  have hvar :
      evalExpr? config { contract := contract, locals := endCageIlkStoreVatIlk I out } evm
        (.var "vatIlk") =
          .ok (.tuple [.int (Int.ofNat (endFlowVatIlkArtWord out).toNat),
            .int (Int.ofNat (endFlowVatIlkRateWord out).toNat),
            .int (Int.ofNat (endFlowVatIlkSpotWord out).toNat),
            .int (Int.ofNat (endFlowVatIlkLineWord out).toNat),
            .int (Int.ofNat (endFlowVatIlkDustWord out).toNat)]) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((endCageIlkStoreVatIlk I out).get? "vatIlk") =
      .ok (.tuple [.int (Int.ofNat (endFlowVatIlkArtWord out).toNat),
        .int (Int.ofNat (endFlowVatIlkRateWord out).toNat),
        .int (Int.ofNat (endFlowVatIlkSpotWord out).toNat),
        .int (Int.ofNat (endFlowVatIlkLineWord out).toNat),
        .int (Int.ofNat (endFlowVatIlkDustWord out).toNat)])
    rw [endCageIlkStoreVatIlk, store_get_self]
    rfl
  rw [evalExpr?]
  simp [hvar, tupleGetValue?, EvalResult.bind, bind]

theorem evalStorageRef_endCageIlk_Art_of_get {locals : Store} (evm : EVM.State)
    (I : ExecutionEnv)
    (hget : locals.get? "ilk" = some (endCageIlkIlkValue I))
    (hsz36 : 36 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (ArtRef (.var "ilk")) = .ok (endCageIlkArtEvaledRef I) := by
  have hargLen : min 32 (I.calldata.toList.length - 4) = bytes32Width.val + 1 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [htlen]
    simp [bytes32Width]
    omega
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, ArtRef,
    endCageIlkArtEvaledRef, endCageIlkIlkValue, endBytes32ArgValue, endCageIlkIlkKey,
    endBytes32ArgKey, valueToKey?, EvalResult.ofOption, EvalResult.bind, evalExpr?,
    pure, bind, ← Std.HashMap.get?_eq_getElem?, hget]
  rw [if_pos hargLen]

theorem endCageIlkAssignArt {locals : Store} (evm : EVM.State) (I : ExecutionEnv)
    (vatOut : ByteArray)
    (hbase : locals.get? "Art" = none)
    (hget : locals.get? "ilk" = some (endCageIlkIlkValue I))
    (hsz36 : 36 ≤ I.calldata.size) :
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (ArtRef (.var "ilk"))
      (.int (Int.ofNat (endFlowVatIlkArtWord vatOut).toNat)) =
        .ok ({ contract := contract, locals := locals }, endCageIlkPostArtState evm I vatOut) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := endCageIlkArtEvaledRef I)
      (loc := wordLoc (endCageIlkArtSlot I))
      (hbase := hbase)
      (her := evalStorageRef_endCageIlk_Art_of_get evm I hget hsz36)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [endCageIlkPostArtState] using
    endStorageLocStore_uint256 evm (endCageIlkArtSlot I) (endFlowVatIlkArtWord vatOut)

theorem endCageIlkStmtArt (evm : EVM.State) (I : ExecutionEnv) (vatOut : ByteArray)
    (hsz36 : 36 ≤ I.calldata.size) :
    ExecStmt config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut } evm
      (.assign .storage (ArtRef (.var "ilk")) (.tupleGet (.var "vatIlk") 0))
      (.ok { contract := contract, locals := endCageIlkStoreVatIlk I vatOut }
        (endCageIlkPostArtState evm I vatOut)) := by
  have hrhs := evalExpr_endCageIlk_vatIlk_art evm I vatOut
  have hassign :
      assignStorageRef? config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut }
        evm .storage (ArtRef (.var "ilk"))
        (.int (Int.ofNat (endFlowVatIlkArtWord vatOut).toNat)) =
          .ok ({ contract := contract, locals := endCageIlkStoreVatIlk I vatOut },
            endCageIlkPostArtState evm I vatOut) := by
    apply endCageIlkAssignArt
    · simp [endCageIlkStoreVatIlk, endCageIlkStore]
    · rw [endCageIlkStoreVatIlk, store_get_ne _ _ (by decide), endCageIlkStore,
        store_get_self]
    · exact hsz36
  exact ExecStmt.assign hrhs hassign

theorem evalExpr_endCageIlk_spotIlk_pip (evm : EVM.State) (I : ExecutionEnv)
    (vatOut spotOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endCageIlkStoreSpotIlk I vatOut spotOut }
      evm (.tupleGet (.var "spotIlk") 0) =
        .ok (.address (endCageIlkSpotIlkPipAddr spotOut)) := by
  have hvar :
      evalExpr? config { contract := contract, locals := endCageIlkStoreSpotIlk I vatOut spotOut }
        evm (.var "spotIlk") =
          .ok (.tuple [.address (endCageIlkSpotIlkPipAddr spotOut),
            .int (Int.ofNat (endCageIlkSpotIlkMatWord spotOut).toNat)]) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((endCageIlkStoreSpotIlk I vatOut spotOut).get? "spotIlk") =
      .ok (.tuple [.address (endCageIlkSpotIlkPipAddr spotOut),
        .int (Int.ofNat (endCageIlkSpotIlkMatWord spotOut).toNat)])
    rw [endCageIlkStoreSpotIlk, store_get_self]
    rfl
  rw [evalExpr?]
  simp [hvar, tupleGetValue?, EvalResult.bind, bind]

theorem endCageIlkStmtPip (evm : EVM.State) (I : ExecutionEnv)
    (vatOut spotOut : ByteArray) :
    ExecStmt config { contract := contract, locals := endCageIlkStoreSpotIlk I vatOut spotOut }
      evm (.letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0))
      (.ok { contract := contract, locals := endCageIlkStorePip I vatOut spotOut } evm) := by
  simpa [endCageIlkStorePip] using
    ExecStmt.letDecl (evalExpr_endCageIlk_spotIlk_pip evm I vatOut spotOut)

theorem evalExpr_endCageIlk_parV (evm : EVM.State) (I : ExecutionEnv)
    (vatOut spotOut parOut readOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endCageIlkStoreRead I vatOut spotOut parOut readOut }
      evm (.var "parV") =
        .ok (.int (Int.ofNat (endCageIlkReturnWord parOut).toNat)) := by
  simpa [endCageIlkStoreRead, endCageIlkStorePar] using
    endEvalExpr_varUInt256
      (evm := evm)
      (locals := endCageIlkStoreRead I vatOut spotOut parOut readOut)
      (name := "parV") (value := endCageIlkReturnWord parOut)
      (by
        rw [endCageIlkStoreRead, store_get_ne _ _ (by decide), endCageIlkStorePar,
          store_get_self])

theorem evalExpr_endCageIlk_pipRead_cast (evm : EVM.State) (I : ExecutionEnv)
    (vatOut spotOut parOut readOut : ByteArray) (hlo : 32 ≤ readOut.size) :
    evalExpr? config { contract := contract, locals := endCageIlkStoreRead I vatOut spotOut parOut readOut }
      evm (.cast (.var "pipRead") uint256St) =
        .ok (.int (Int.ofNat (endCageIlkReturnWord readOut).toNat)) := by
  have hpipRead :
      evalExpr? config { contract := contract, locals := endCageIlkStoreRead I vatOut spotOut parOut readOut }
        evm (.var "pipRead") =
          .ok (.fixedBytes bytes32Width (endCageIlkReadBytes readOut)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((endCageIlkStoreRead I vatOut spotOut parOut readOut).get? "pipRead") =
      .ok (.fixedBytes bytes32Width (endCageIlkReadBytes readOut))
    rw [endCageIlkStoreRead, store_get_self]
    rfl
  have hlen : (endCageIlkReadBytes readOut).length = bytes32Width.val + 1 := by
    unfold endCageIlkReadBytes
    rw [List.drop_zero, List.length_take]
    have htlen : readOut.toList.length = readOut.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [htlen]
    simp [bytes32Width]
    omega
  have hfrom :
      fromBytesBigEndian (endCageIlkReadBytes readOut) =
        (endCageIlkReturnWord readOut).toNat := by
    have hslice :
        (readOut.extract 0 32).toList = (readOut.toList.drop 0).take 32 := by
      rw [byteArray_toList_eq (readOut.extract 0 32), ByteArray.data_extract,
        Array.toList_extract, List.extract_eq_take_drop, byteArray_toList_eq]
    rw [endCageIlkReturnWord, UInt256.toNat_ofNat_of_lt
      (fromByteArrayBigEndian_extract0_32_lt (returndata := readOut) hlo)]
    unfold fromByteArrayBigEndian endCageIlkReadBytes
    rw [hslice, List.drop_zero]
  rw [evalExpr?]
  simp [hpipRead, castValue?, fixedBytesToNat?, fixedBytesValid, uint256St, uint256Int,
    fixedBytesSize, bytes32Width, hlen, hfrom, EvalResult.ofOption, EvalResult.bind, bind]

theorem endCageIlkStmtWdivReturns (evm : EVM.State) (I : ExecutionEnv)
    (vatOut spotOut parOut readOut : ByteArray)
    (hreadSize : 32 ≤ readOut.size)
    (hfit : (endCageIlkReturnWord parOut).toNat * endWadWord.toNat < UInt256.size)
    (hy : endCageIlkReturnWord readOut ≠ ⟨0⟩) :
    ExecStmt config { contract := contract, locals := endCageIlkStoreRead I vatOut spotOut parOut readOut }
      evm (.internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV")
      (.ok { contract := contract, locals := endCageIlkStoreTagV I vatOut spotOut parOut readOut }
        evm) := by
  have hpar := evalExpr_endCageIlk_parV evm I vatOut spotOut parOut readOut
  have hread := evalExpr_endCageIlk_pipRead_cast evm I vatOut spotOut parOut readOut hreadSize
  have hargs :
      evalExprs? config { contract := contract, locals := endCageIlkStoreRead I vatOut spotOut parOut readOut }
        evm [.var "parV", .cast (.var "pipRead") uint256St] =
          .ok [.int (Int.ofNat (endCageIlkReturnWord parOut).toNat),
            .int (Int.ofNat (endCageIlkReturnWord readOut).toNat)] := by
    simp [evalExprs?, hpar, hread, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? wdivFunction.params
          [.int (Int.ofNat (endCageIlkReturnWord parOut).toNat),
            .int (Int.ofNat (endCageIlkReturnWord readOut).toNat)] =
        some (endUintBinaryLocals (endCageIlkReturnWord parOut)
          (endCageIlkReturnWord readOut)) := by
    simp [wdivFunction, uint256, bindParams?, endUintBinaryLocals]
  have hbody :=
    endExecWdivFunctionReturn (evm := evm)
      (x := endCageIlkReturnWord parOut) (y := endCageIlkReturnWord readOut)
      (prod := endCageIlkWdivProductWord parOut)
      (q := endCageIlkTagVWord parOut readOut) rfl hfit hy rfl
  have hstmt := internalCallFunctionReturn
    (cfg := config)
    (caller := { contract := contract, locals := endCageIlkStoreRead I vatOut spotOut parOut readOut })
    (evm := evm) (name := "wdiv") (retVar := "tagV")
    (args := [.var "parV", .cast (.var "pipRead") uint256St])
    (argVals := [.int (Int.ofNat (endCageIlkReturnWord parOut).toNat),
      .int (Int.ofNat (endCageIlkReturnWord readOut).toNat)])
    (callee := wdivFunction)
    (locals := endUintBinaryLocals (endCageIlkReturnWord parOut)
      (endCageIlkReturnWord readOut))
    hargs (by rfl) hbind hbody
  simpa [endCageIlkStoreTagV, resumeAfterInternalCall, collapseReturns] using hstmt

theorem endCageIlkStmtWdivRevertMul (evm : EVM.State) (I : ExecutionEnv)
    (vatOut spotOut parOut readOut : ByteArray)
    (hreadSize : 32 ≤ readOut.size)
    (hover : UInt256.size ≤ (endCageIlkReturnWord parOut).toNat * endWadWord.toNat) :
    ExecStmt config { contract := contract, locals := endCageIlkStoreRead I vatOut spotOut parOut readOut }
      evm (.internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV")
      .reverted := by
  have hpar := evalExpr_endCageIlk_parV evm I vatOut spotOut parOut readOut
  have hread := evalExpr_endCageIlk_pipRead_cast evm I vatOut spotOut parOut readOut hreadSize
  have hargs :
      evalExprs? config { contract := contract, locals := endCageIlkStoreRead I vatOut spotOut parOut readOut }
        evm [.var "parV", .cast (.var "pipRead") uint256St] =
          .ok [.int (Int.ofNat (endCageIlkReturnWord parOut).toNat),
            .int (Int.ofNat (endCageIlkReturnWord readOut).toNat)] := by
    simp [evalExprs?, hpar, hread, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? wdivFunction.params
          [.int (Int.ofNat (endCageIlkReturnWord parOut).toNat),
            .int (Int.ofNat (endCageIlkReturnWord readOut).toNat)] =
        some (endUintBinaryLocals (endCageIlkReturnWord parOut)
          (endCageIlkReturnWord readOut)) := by
    simp [wdivFunction, uint256, bindParams?, endUintBinaryLocals]
  have hbody :=
    endExecWdivFunctionRevertMul (evm := evm)
      (x := endCageIlkReturnWord parOut) (y := endCageIlkReturnWord readOut) hover
  exact internalCallFunctionRevert
    (cfg := config)
    (caller := { contract := contract, locals := endCageIlkStoreRead I vatOut spotOut parOut readOut })
    (evm := evm) (name := "wdiv") (retVar := "tagV")
    (args := [.var "parV", .cast (.var "pipRead") uint256St])
    (argVals := [.int (Int.ofNat (endCageIlkReturnWord parOut).toNat),
      .int (Int.ofNat (endCageIlkReturnWord readOut).toNat)])
    (callee := wdivFunction)
    (locals := endUintBinaryLocals (endCageIlkReturnWord parOut)
      (endCageIlkReturnWord readOut))
    hargs (by rfl) hbind hbody

theorem endCageIlkStmtWdivRevertDivZero (evm : EVM.State) (I : ExecutionEnv)
    (vatOut spotOut parOut readOut : ByteArray)
    (hreadSize : 32 ≤ readOut.size)
    (hfit : (endCageIlkReturnWord parOut).toNat * endWadWord.toNat < UInt256.size)
    (hy : endCageIlkReturnWord readOut = ⟨0⟩) :
    ExecStmt config { contract := contract, locals := endCageIlkStoreRead I vatOut spotOut parOut readOut }
      evm (.internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV")
      .reverted := by
  have hpar := evalExpr_endCageIlk_parV evm I vatOut spotOut parOut readOut
  have hread := evalExpr_endCageIlk_pipRead_cast evm I vatOut spotOut parOut readOut hreadSize
  have hargs :
      evalExprs? config { contract := contract, locals := endCageIlkStoreRead I vatOut spotOut parOut readOut }
        evm [.var "parV", .cast (.var "pipRead") uint256St] =
          .ok [.int (Int.ofNat (endCageIlkReturnWord parOut).toNat),
            .int (Int.ofNat (endCageIlkReturnWord readOut).toNat)] := by
    simp [evalExprs?, hpar, hread, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? wdivFunction.params
          [.int (Int.ofNat (endCageIlkReturnWord parOut).toNat),
            .int (Int.ofNat (endCageIlkReturnWord readOut).toNat)] =
        some (endUintBinaryLocals (endCageIlkReturnWord parOut)
          (endCageIlkReturnWord readOut)) := by
    simp [wdivFunction, uint256, bindParams?, endUintBinaryLocals]
  have hbody :=
    endExecWdivFunctionRevertDivZero (evm := evm)
      (x := endCageIlkReturnWord parOut) (y := endCageIlkReturnWord readOut)
      (prod := endCageIlkWdivProductWord parOut) rfl hfit hy
  exact internalCallFunctionRevert
    (cfg := config)
    (caller := { contract := contract, locals := endCageIlkStoreRead I vatOut spotOut parOut readOut })
    (evm := evm) (name := "wdiv") (retVar := "tagV")
    (args := [.var "parV", .cast (.var "pipRead") uint256St])
    (argVals := [.int (Int.ofNat (endCageIlkReturnWord parOut).toNat),
      .int (Int.ofNat (endCageIlkReturnWord readOut).toNat)])
    (callee := wdivFunction)
    (locals := endUintBinaryLocals (endCageIlkReturnWord parOut)
      (endCageIlkReturnWord readOut))
    hargs (by rfl) hbind hbody

theorem evalStorageRef_endCageIlk_tag_of_get {locals : Store} (evm : EVM.State)
    (I : ExecutionEnv)
    (hget : locals.get? "ilk" = some (endCageIlkIlkValue I))
    (hsz36 : 36 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (tagRef (.var "ilk")) = .ok (endCageIlkTagEvaledRef I) := by
  have hargLen : min 32 (I.calldata.toList.length - 4) = bytes32Width.val + 1 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [htlen]
    simp [bytes32Width]
    omega
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, tagRef,
    endCageIlkTagEvaledRef, endCageIlkIlkValue, endBytes32ArgValue, endCageIlkIlkKey,
    endBytes32ArgKey, valueToKey?, EvalResult.ofOption, EvalResult.bind, evalExpr?,
    pure, bind, ← Std.HashMap.get?_eq_getElem?, hget]
  rw [if_pos hargLen]

theorem endCageIlkAssignTag {locals : Store} (evm : EVM.State) (I : ExecutionEnv)
    (tagV : UInt256)
    (hbase : locals.get? "tag" = none)
    (hget : locals.get? "ilk" = some (endCageIlkIlkValue I))
    (hsz36 : 36 ≤ I.calldata.size) :
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (tagRef (.var "ilk")) (.int (Int.ofNat tagV.toNat)) =
        .ok ({ contract := contract, locals := locals }, endCageIlkPostTagState evm I tagV) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := endCageIlkTagEvaledRef I)
      (loc := wordLoc (endCageIlkTagSlot I))
      (hbase := hbase)
      (her := evalStorageRef_endCageIlk_tag_of_get evm I hget hsz36)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [endCageIlkPostTagState] using
    endStorageLocStore_uint256 evm (endCageIlkTagSlot I) tagV

theorem endCageIlkStmtTag (evm : EVM.State) (I : ExecutionEnv)
    (vatOut spotOut parOut readOut : ByteArray) (hsz36 : 36 ≤ I.calldata.size) :
    ExecStmt config
      { contract := contract, locals := endCageIlkStoreTagV I vatOut spotOut parOut readOut }
      evm (.assign .storage (tagRef (.var "ilk")) (.var "tagV"))
      (.ok { contract := contract, locals := endCageIlkStoreTagV I vatOut spotOut parOut readOut }
        (endCageIlkPostTagState evm I (endCageIlkTagVWord parOut readOut))) := by
  have htagV :
      evalExpr? config
        { contract := contract, locals := endCageIlkStoreTagV I vatOut spotOut parOut readOut }
        evm (.var "tagV") =
          .ok (.int (Int.ofNat (endCageIlkTagVWord parOut readOut).toNat)) := by
    simpa [endCageIlkStoreTagV] using
      endEvalExpr_varUInt256
        (evm := evm)
        (locals := endCageIlkStoreTagV I vatOut spotOut parOut readOut)
        (name := "tagV") (value := endCageIlkTagVWord parOut readOut)
        (by simp [endCageIlkStoreTagV])
  have hassign :=
    endCageIlkAssignTag
      (locals := endCageIlkStoreTagV I vatOut spotOut parOut readOut)
      evm I (endCageIlkTagVWord parOut readOut)
      (by
        simp [endCageIlkStoreTagV, endCageIlkStoreRead, endCageIlkStorePar,
          endCageIlkStorePip, endCageIlkStoreSpotIlk, endCageIlkStoreVatIlk,
          endCageIlkStore])
      (by
        rw [endCageIlkStoreTagV, store_get_ne _ _ (by decide),
          endCageIlkStoreRead, store_get_ne _ _ (by decide),
          endCageIlkStorePar, store_get_ne _ _ (by decide),
          endCageIlkStorePip, store_get_ne _ _ (by decide),
          endCageIlkStoreSpotIlk, store_get_ne _ _ (by decide),
          endCageIlkStoreVatIlk, store_get_ne _ _ (by decide),
          endCageIlkStore, store_get_self])
      hsz36
  exact ExecStmt.assign htagV hassign

theorem endCageIlkTailReverts_wdivMulOverflow (evm : EVM.State) (I : ExecutionEnv)
    (vatOut spotOut parOut readOut : ByteArray)
    (hreadSize : 32 ≤ readOut.size)
    (hover : UInt256.size ≤ (endCageIlkReturnWord parOut).toNat * endWadWord.toNat) :
    ExecBlock config { contract := contract, locals := endCageIlkStoreRead I vatOut spotOut parOut readOut }
      evm
      [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
        .assign .storage (tagRef (.var "ilk")) (.var "tagV") ]
      .reverted := by
  exact ExecBlock.consRevert
    (endCageIlkStmtWdivRevertMul evm I vatOut spotOut parOut readOut hreadSize hover)

theorem endCageIlkTailReverts_wdivDivZero (evm : EVM.State) (I : ExecutionEnv)
    (vatOut spotOut parOut readOut : ByteArray)
    (hreadSize : 32 ≤ readOut.size)
    (hfit : (endCageIlkReturnWord parOut).toNat * endWadWord.toNat < UInt256.size)
    (hy : endCageIlkReturnWord readOut = ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endCageIlkStoreRead I vatOut spotOut parOut readOut }
      evm
      [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
        .assign .storage (tagRef (.var "ilk")) (.var "tagV") ]
      .reverted := by
  exact ExecBlock.consRevert
    (endCageIlkStmtWdivRevertDivZero evm I vatOut spotOut parOut readOut hreadSize hfit hy)

theorem endCageIlkTailReturns (evm : EVM.State) (I : ExecutionEnv)
    (vatOut spotOut parOut readOut : ByteArray)
    (hsz36 : 36 ≤ I.calldata.size)
    (hreadSize : 32 ≤ readOut.size)
    (hfit : (endCageIlkReturnWord parOut).toNat * endWadWord.toNat < UInt256.size)
    (hy : endCageIlkReturnWord readOut ≠ ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endCageIlkStoreRead I vatOut spotOut parOut readOut }
      evm
      [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
        .assign .storage (tagRef (.var "ilk")) (.var "tagV") ]
      (.ok { contract := contract, locals := endCageIlkStoreTagV I vatOut spotOut parOut readOut }
        (endCageIlkPostTagState evm I (endCageIlkTagVWord parOut readOut))) := by
  refine ExecBlock.consNormal
    (endCageIlkStmtWdivReturns evm I vatOut spotOut parOut readOut hreadSize hfit hy) ?_
  refine ExecBlock.consNormal ?_ ExecBlock.nil
  exact endCageIlkStmtTag evm I vatOut spotOut parOut readOut hsz36

theorem endCageIlkBodyReverts_vatIlksTerminated {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hlive : endCageIlkLiveWord σ I = ⟨0⟩)
    (htag : endCageIlkTagWord σ I = ⟨0⟩)
    (hvat :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      ExecBlock config { contract := contract, locals := endCageIlkStore I } evm0
        (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk") .reverted) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endCageIlkStore I) cageIlkTransition.body
      .reverted := by
  intro evm0
  have hvat' :
      ExecBlock config { contract := contract, locals := endCageIlkStore I } evm0
        (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk") .reverted := by
    simpa [evm0] using hvat
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endCageIlkLiveWord, endSlotWord, solcSlotWord] using hlive
  have htagLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (endCageIlkTagSlot I) = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endCageIlkTagWord, endSlotWord, solcSlotWord] using htag
  have hguardLive :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_endCageIlk_live_zero_true evm0 I hliveLoad
  have hguardTag :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm0
        (.binary .eq (.storage (tagRef (.var "ilk"))) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_endCageIlk_tag_eq_true evm0 I hsz36 htagLoad
  have hblock :
      ExecBlock config { contract := contract, locals := endCageIlkStore I } evm0
        cageIlkTransition.body .reverted := by
    simp only [cageIlkTransition, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp only [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardTag) ?_
    exact Reasoning.Refinement.execBlock_append_term
      (s1 := checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
        "vatIlk")
      (s2 :=
        [ .assign .storage (ArtRef (.var "ilk")) (.tupleGet (.var "vatIlk") 0) ] ++
        checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"]
          "spotIlk" (perm := false) ++
        [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
        checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
          (perm := false) ++
        checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
          (perm := false) ++
        [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
          .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
      hvat'
      (by intro f' e' h; cases h)
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endCageIlkBodyReverts_vatIlksNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hlive : endCageIlkLiveWord σ I = ⟨0⟩)
    (htag : endCageIlkTagWord σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (endPackVatWord σ I) = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endCageIlkStore I) cageIlkTransition.body
      .reverted := by
  exact endCageIlkBodyReverts_vatIlksTerminated
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hwv hsz36 hlive htag
    (by
      simpa using (
      endCageIlkCheckedVatIlksNoCode
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize))

theorem endCageIlkBodyReverts_vatIlksCallFailed {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hlive : endCageIlkLiveWord σ I = ⟨0⟩)
    (htag : endCageIlkTagWord σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "vatIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (false, evmVat, out) true) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endCageIlkStore I) cageIlkTransition.body
      .reverted := by
  exact endCageIlkBodyReverts_vatIlksTerminated
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hwv hsz36 hlive htag
    (by
      simpa using (
      endCageIlkCheckedVatIlksFailure
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (evmVat := evmVat) (out := out)
        hcodeSize hcall))

theorem endCageIlkBodyReverts_vatIlksDecodeShort {cA gh bl σ σ₀ A I}
    {g : UInt256} {evmVat : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hlive : endCageIlkLiveWord σ I = ⟨0⟩)
    (htag : endCageIlkTagWord σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "vatIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmVat, out) true)
    (hshort : out.size < 160) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endCageIlkStore I) cageIlkTransition.body
      .reverted := by
  exact endCageIlkBodyReverts_vatIlksTerminated
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hwv hsz36 hlive htag
    (by
      simpa using (
      endCageIlkCheckedVatIlksDecodeRevert
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (evmVat := evmVat) (out := out)
        hcodeSize hcall hshort))

theorem endCageIlkTailFromVatReverts_spotTerminated (evmVat : EVM.State)
    (I : ExecutionEnv) (vatOut : ByteArray) (hsz36 : 36 ≤ I.calldata.size)
    (hspot :
      let evmArt := endCageIlkPostArtState evmVat I vatOut
      ExecBlock config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut }
        evmArt
        (checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"]
          "spotIlk" (perm := false)) .reverted) :
    ExecBlock config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut }
      evmVat
      ([ .assign .storage (ArtRef (.var "ilk")) (.tupleGet (.var "vatIlk") 0) ] ++
      checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"]
        "spotIlk" (perm := false) ++
      [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
      checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
        (perm := false) ++
      checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
        (perm := false) ++
      [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
        .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
      .reverted := by
  let evmArt := endCageIlkPostArtState evmVat I vatOut
  have hspot' :
      ExecBlock config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut }
        evmArt
        (checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"]
          "spotIlk" (perm := false)) .reverted := by
    simpa [evmArt] using hspot
  refine ExecBlock.consNormal (endCageIlkStmtArt evmVat I vatOut hsz36) ?_
  exact Reasoning.Refinement.execBlock_append_term
    (s1 := checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"]
      "spotIlk" (perm := false))
    (s2 :=
      [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
      checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
        (perm := false) ++
      checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
        (perm := false) ++
      [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
        .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
    hspot' (by intro f' e' h; cases h)

theorem endCageIlkTailFromVatReverts_spotNoCode (evmVat : EVM.State)
    (I : ExecutionEnv) (vatOut : ByteArray) (hsz36 : 36 ≤ I.calldata.size)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord
        (endCageIlkPostArtState evmVat I vatOut).accountMap
        (endCageIlkSpotWord (endCageIlkPostArtState evmVat I vatOut).accountMap
          (endCageIlkPostArtState evmVat I vatOut).executionEnv) = ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut }
      evmVat
      ([ .assign .storage (ArtRef (.var "ilk")) (.tupleGet (.var "vatIlk") 0) ] ++
      checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"]
        "spotIlk" (perm := false) ++
      [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
      checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
        (perm := false) ++
      checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
        (perm := false) ++
      [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
        .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
      .reverted := by
  exact endCageIlkTailFromVatReverts_spotTerminated evmVat I vatOut hsz36
    (by
      simpa using
        endCageIlkCheckedSpotIlksNoCode
          (endCageIlkPostArtState evmVat I vatOut) I vatOut hcodeSize)

theorem endCageIlkTailFromVatReverts_spotFailure {evmVat evmSpot : EVM.State}
    {I : ExecutionEnv} {vatOut spotOut : ByteArray}
    (hsz36 : 36 ≤ I.calldata.size)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord
        (endCageIlkPostArtState evmVat I vatOut).accountMap
        (endCageIlkSpotWord (endCageIlkPostArtState evmVat I vatOut).accountMap
          (endCageIlkPostArtState evmVat I vatOut).executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (endCageIlkPostArtState evmVat I vatOut)
        (EVM.address
          (AccountAddress.ofNat
            (endCageIlkSpotWord (endCageIlkPostArtState evmVat I vatOut).accountMap
              (endCageIlkPostArtState evmVat I vatOut).executionEnv).toNat))
        "spotIlks" 0 [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (false, evmSpot, spotOut) false) :
    ExecBlock config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut }
      evmVat
      ([ .assign .storage (ArtRef (.var "ilk")) (.tupleGet (.var "vatIlk") 0) ] ++
      checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"]
        "spotIlk" (perm := false) ++
      [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
      checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
        (perm := false) ++
      checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
        (perm := false) ++
      [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
        .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
      .reverted := by
  exact endCageIlkTailFromVatReverts_spotTerminated evmVat I vatOut hsz36
    (by
      simpa using
        endCageIlkCheckedSpotIlksFailure
          (evm := endCageIlkPostArtState evmVat I vatOut) (evm' := evmSpot)
          (I := I) (vatOut := vatOut) (spotOut := spotOut) hcodeSize hcall)

theorem endCageIlkTailFromVatReverts_spotDecodeShort {evmVat evmSpot : EVM.State}
    {I : ExecutionEnv} {vatOut spotOut : ByteArray}
    (hsz36 : 36 ≤ I.calldata.size)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord
        (endCageIlkPostArtState evmVat I vatOut).accountMap
        (endCageIlkSpotWord (endCageIlkPostArtState evmVat I vatOut).accountMap
          (endCageIlkPostArtState evmVat I vatOut).executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (endCageIlkPostArtState evmVat I vatOut)
        (EVM.address
          (AccountAddress.ofNat
            (endCageIlkSpotWord (endCageIlkPostArtState evmVat I vatOut).accountMap
              (endCageIlkPostArtState evmVat I vatOut).executionEnv).toNat))
        "spotIlks" 0 [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmSpot, spotOut) false)
    (hshort : spotOut.size < 64) :
    ExecBlock config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut }
      evmVat
      ([ .assign .storage (ArtRef (.var "ilk")) (.tupleGet (.var "vatIlk") 0) ] ++
      checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"]
        "spotIlk" (perm := false) ++
      [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
      checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
        (perm := false) ++
      checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
        (perm := false) ++
      [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
        .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
      .reverted := by
  exact endCageIlkTailFromVatReverts_spotTerminated evmVat I vatOut hsz36
    (by
      simpa using
        endCageIlkCheckedSpotIlksDecodeRevert
          (evm := endCageIlkPostArtState evmVat I vatOut) (evm' := evmSpot)
          (I := I) (vatOut := vatOut) (spotOut := spotOut)
          hcodeSize hcall hshort)

theorem endCageIlkTailAfterSpotReverts_parTerminated {evmSpot : EVM.State}
    {I : ExecutionEnv} {vatOut spotOut : ByteArray}
    (hpar :
      ExecBlock config { contract := contract, locals := endCageIlkStorePip I vatOut spotOut }
        evmSpot
        (checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
          (perm := false)) .reverted) :
    ExecBlock config { contract := contract, locals := endCageIlkStorePip I vatOut spotOut }
      evmSpot
      (checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
        (perm := false) ++
      checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
        (perm := false) ++
      [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
        .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
      .reverted := by
  exact Reasoning.Refinement.execBlock_append_term
    (s1 := checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
      (perm := false))
    (s2 :=
      checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
        (perm := false) ++
      [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
        .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
    hpar (by intro f' e' h; cases h)

theorem endCageIlkTailAfterSpotReverts_parNoCode (evmSpot : EVM.State)
    (I : ExecutionEnv) (vatOut spotOut : ByteArray)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord evmSpot.accountMap
        (endCageIlkSpotWord evmSpot.accountMap evmSpot.executionEnv) = ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endCageIlkStorePip I vatOut spotOut }
      evmSpot
      (checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
        (perm := false) ++
      checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
        (perm := false) ++
      [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
        .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
      .reverted := by
  exact endCageIlkTailAfterSpotReverts_parTerminated
    (endCageIlkCheckedParNoCode evmSpot I vatOut spotOut hcodeSize)

theorem endCageIlkTailAfterSpotReverts_parFailure {evmSpot evmPar : EVM.State}
    {I : ExecutionEnv} {vatOut spotOut parOut : ByteArray}
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord evmSpot.accountMap
        (endCageIlkSpotWord evmSpot.accountMap evmSpot.executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evmSpot
        (EVM.address
          (AccountAddress.ofNat (endCageIlkSpotWord evmSpot.accountMap
            evmSpot.executionEnv).toNat))
        "par" 0 [] (false, evmPar, parOut) false) :
    ExecBlock config { contract := contract, locals := endCageIlkStorePip I vatOut spotOut }
      evmSpot
      (checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
        (perm := false) ++
      checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
        (perm := false) ++
      [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
        .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
      .reverted := by
  exact endCageIlkTailAfterSpotReverts_parTerminated
    (endCageIlkCheckedParFailure hcodeSize hcall)

theorem endCageIlkTailAfterSpotReverts_parDecodeShort {evmSpot evmPar : EVM.State}
    {I : ExecutionEnv} {vatOut spotOut parOut : ByteArray}
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord evmSpot.accountMap
        (endCageIlkSpotWord evmSpot.accountMap evmSpot.executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evmSpot
        (EVM.address
          (AccountAddress.ofNat (endCageIlkSpotWord evmSpot.accountMap
            evmSpot.executionEnv).toNat))
        "par" 0 [] (true, evmPar, parOut) false)
    (hshort : parOut.size < 32) :
    ExecBlock config { contract := contract, locals := endCageIlkStorePip I vatOut spotOut }
      evmSpot
      (checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
        (perm := false) ++
      checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
        (perm := false) ++
      [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
        .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
      .reverted := by
  exact endCageIlkTailAfterSpotReverts_parTerminated
    (endCageIlkCheckedParDecodeRevert hcodeSize hcall hshort)

theorem endCageIlkTailAfterParReverts_readTerminated {evmPar : EVM.State}
    {I : ExecutionEnv} {vatOut spotOut parOut : ByteArray}
    (hread :
      ExecBlock config { contract := contract, locals := endCageIlkStorePar I vatOut spotOut parOut }
        evmPar
        (checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
          (perm := false)) .reverted) :
    ExecBlock config { contract := contract, locals := endCageIlkStorePar I vatOut spotOut parOut }
      evmPar
      (checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
        (perm := false) ++
      [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
        .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
      .reverted := by
  exact Reasoning.Refinement.execBlock_append_term
    (s1 := checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
      (perm := false))
    (s2 :=
      [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
        .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
    hread (by intro f' e' h; cases h)

theorem endCageIlkTailAfterParReverts_readNoCode (evmPar : EVM.State)
    (I : ExecutionEnv) (vatOut spotOut parOut : ByteArray)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord evmPar.accountMap
        (endCageIlkPipCallWord spotOut) = ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endCageIlkStorePar I vatOut spotOut parOut }
      evmPar
      (checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
        (perm := false) ++
      [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
        .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
      .reverted := by
  exact endCageIlkTailAfterParReverts_readTerminated
    (endCageIlkCheckedReadNoCode evmPar I vatOut spotOut parOut hcodeSize)

theorem endCageIlkTailAfterParReverts_readFailure {evmPar evmRead : EVM.State}
    {I : ExecutionEnv} {vatOut spotOut parOut readOut : ByteArray}
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord evmPar.accountMap
        (endCageIlkPipCallWord spotOut) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evmPar
        (EVM.address (endCageIlkSpotIlkPipAddr spotOut))
        "read" 0 [] (false, evmRead, readOut) false) :
    ExecBlock config { contract := contract, locals := endCageIlkStorePar I vatOut spotOut parOut }
      evmPar
      (checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
        (perm := false) ++
      [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
        .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
      .reverted := by
  exact endCageIlkTailAfterParReverts_readTerminated
    (endCageIlkCheckedReadFailure hcodeSize hcall)

theorem endCageIlkTailAfterParReverts_readDecodeShort {evmPar evmRead : EVM.State}
    {I : ExecutionEnv} {vatOut spotOut parOut readOut : ByteArray}
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord evmPar.accountMap
        (endCageIlkPipCallWord spotOut) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evmPar
        (EVM.address (endCageIlkSpotIlkPipAddr spotOut))
        "read" 0 [] (true, evmRead, readOut) false)
    (hshort : readOut.size < 32) :
    ExecBlock config { contract := contract, locals := endCageIlkStorePar I vatOut spotOut parOut }
      evmPar
      (checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
        (perm := false) ++
      [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
        .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
      .reverted := by
  exact endCageIlkTailAfterParReverts_readTerminated
    (endCageIlkCheckedReadDecodeRevert hcodeSize hcall hshort)

theorem endCageIlkTailAfterParReadOk {evmPar evmRead : EVM.State}
    {I : ExecutionEnv} {vatOut spotOut parOut readOut : ByteArray}
    {res : ExecResult}
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord evmPar.accountMap
        (endCageIlkPipCallWord spotOut) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evmPar
        (EVM.address (endCageIlkSpotIlkPipAddr spotOut))
        "read" 0 [] (true, evmRead, readOut) false)
    (hlo : 32 ≤ readOut.size)
    (htail :
      ExecBlock config { contract := contract, locals := endCageIlkStoreRead I vatOut spotOut parOut readOut }
        evmRead
        [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
          .assign .storage (tagRef (.var "ilk")) (.var "tagV") ]
        res) :
    ExecBlock config { contract := contract, locals := endCageIlkStorePar I vatOut spotOut parOut }
      evmPar
      (checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
        (perm := false) ++
      [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
        .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
      res := by
  have hread :=
    endCageIlkCheckedReadSuccess
      (evm := evmPar) (evm' := evmRead) (I := I) (vatOut := vatOut)
      (spotOut := spotOut) (parOut := parOut) (readOut := readOut)
      hcodeSize hcall hlo
  exact Reasoning.Refinement.execBlock_append hread htail

theorem endCageIlkTailAfterSpotParOk {evmSpot evmPar : EVM.State}
    {I : ExecutionEnv} {vatOut spotOut parOut : ByteArray}
    {res : ExecResult}
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord evmSpot.accountMap
        (endCageIlkSpotWord evmSpot.accountMap evmSpot.executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evmSpot
        (EVM.address
          (AccountAddress.ofNat (endCageIlkSpotWord evmSpot.accountMap
            evmSpot.executionEnv).toNat))
        "par" 0 [] (true, evmPar, parOut) false)
    (hlo : 32 ≤ parOut.size)
    (htail :
      ExecBlock config { contract := contract, locals := endCageIlkStorePar I vatOut spotOut parOut }
        evmPar
        (checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
          (perm := false) ++
        [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
          .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
        res) :
    ExecBlock config { contract := contract, locals := endCageIlkStorePip I vatOut spotOut }
      evmSpot
      (checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
        (perm := false) ++
      checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
        (perm := false) ++
      [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
        .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
      res := by
  have hpar :=
    endCageIlkCheckedParSuccess
      (evm := evmSpot) (evm' := evmPar) (I := I) (vatOut := vatOut)
      (spotOut := spotOut) (parOut := parOut) hcodeSize hcall hlo
  have happ := Reasoning.Refinement.execBlock_append
    (s2 :=
      checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
        (perm := false) ++
      [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
        .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
    hpar htail
  simpa [List.append_assoc] using happ

theorem endCageIlkTailFromVatSpotOk {evmVat evmSpot : EVM.State}
    {I : ExecutionEnv} {vatOut spotOut : ByteArray}
    {res : ExecResult}
    (hsz36 : 36 ≤ I.calldata.size)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord
        (endCageIlkPostArtState evmVat I vatOut).accountMap
        (endCageIlkSpotWord (endCageIlkPostArtState evmVat I vatOut).accountMap
          (endCageIlkPostArtState evmVat I vatOut).executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (endCageIlkPostArtState evmVat I vatOut)
        (EVM.address
          (AccountAddress.ofNat
            (endCageIlkSpotWord (endCageIlkPostArtState evmVat I vatOut).accountMap
              (endCageIlkPostArtState evmVat I vatOut).executionEnv).toNat))
        "spotIlks" 0 [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmSpot, spotOut) false)
    (hlo : 64 ≤ spotOut.size)
    (htail :
      ExecBlock config { contract := contract, locals := endCageIlkStorePip I vatOut spotOut }
        evmSpot
        (checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
          (perm := false) ++
        checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
          (perm := false) ++
        [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
          .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
        res) :
    ExecBlock config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut }
      evmVat
      ([ .assign .storage (ArtRef (.var "ilk")) (.tupleGet (.var "vatIlk") 0) ] ++
      checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"]
        "spotIlk" (perm := false) ++
      [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
      checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
        (perm := false) ++
      checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
        (perm := false) ++
      [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
        .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
      res := by
  let evmArt := endCageIlkPostArtState evmVat I vatOut
  have hspot :
      ExecBlock config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut }
        evmArt
        (checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"]
          "spotIlk" (perm := false))
        (.ok { contract := contract, locals := endCageIlkStoreSpotIlk I vatOut spotOut }
          evmSpot) := by
    simpa [evmArt] using
      endCageIlkCheckedSpotIlksSuccess
        (evm := evmArt) (evm' := evmSpot) (I := I) (vatOut := vatOut)
        (spotOut := spotOut) (by simpa [evmArt] using hcodeSize)
        (by simpa [evmArt] using hcall) hlo
  have hpip :
      ExecBlock config { contract := contract, locals := endCageIlkStoreSpotIlk I vatOut spotOut }
        evmSpot
        [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ]
        (.ok { contract := contract, locals := endCageIlkStorePip I vatOut spotOut } evmSpot) := by
    exact ExecBlock.consNormal (endCageIlkStmtPip evmSpot I vatOut spotOut) ExecBlock.nil
  have hspotPip :
      ExecBlock config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut }
        evmArt
        (checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"]
          "spotIlk" (perm := false) ++
        [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ])
        (.ok { contract := contract, locals := endCageIlkStorePip I vatOut spotOut } evmSpot) := by
    exact Reasoning.Refinement.execBlock_append hspot hpip
  have hrest :
      ExecBlock config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut }
        evmArt
        (checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"]
          "spotIlk" (perm := false) ++
        [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
        checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
          (perm := false) ++
        checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
          (perm := false) ++
        [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
          .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
        res := by
    have happ := Reasoning.Refinement.execBlock_append
      (s2 :=
        checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
          (perm := false) ++
        checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
          (perm := false) ++
        [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
          .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
      hspotPip htail
    simpa [List.append_assoc] using happ
  refine ExecBlock.consNormal (endCageIlkStmtArt evmVat I vatOut hsz36) ?_
  simpa [evmArt, List.append_assoc] using hrest

theorem endCageIlkPrefixVatIlksSuccess {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat : EVM.State} {vatOut : ByteArray}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hlive : endCageIlkLiveWord σ I = ⟨0⟩)
    (htag : endCageIlkTagWord σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "vatIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmVat, vatOut) true)
    (hlo : 160 ≤ vatOut.size) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := endCageIlkStore I } evm0
      (nonpayable ++
        [ .require (.binary .eq (.storage liveRef) (.intLit 0)),
          .require (.binary .eq (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
        checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk")
      (.ok { contract := contract, locals := endCageIlkStoreVatIlk I vatOut } evmVat) := by
  intro evm0
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endCageIlkLiveWord, endSlotWord, solcSlotWord] using hlive
  have htagLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (endCageIlkTagSlot I) = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endCageIlkTagWord, endSlotWord, solcSlotWord] using htag
  have hguardLive :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_endCageIlk_live_zero_true evm0 I hliveLoad
  have hguardTag :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm0
        (.binary .eq (.storage (tagRef (.var "ilk"))) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_endCageIlk_tag_eq_true evm0 I hsz36 htagLoad
  have hvat :
      ExecBlock config { contract := contract, locals := endCageIlkStore I } evm0
        (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk")
        (.ok { contract := contract, locals := endCageIlkStoreVatIlk I vatOut } evmVat) := by
    exact endCageIlkCheckedVatIlksSuccess
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (evmVat := evmVat) (out := vatOut)
      hcodeSize hcall hlo
  simp only [nonpayable, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardTag) ?_
  exact hvat

theorem endCageIlkBodyReverts_vatIlksOkTailReverted {cA gh bl σ σ₀ A I}
    {g : UInt256} {evmVat : EVM.State} {vatOut : ByteArray}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hlive : endCageIlkLiveWord σ I = ⟨0⟩)
    (htag : endCageIlkTagWord σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "vatIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmVat, vatOut) true)
    (hlo : 160 ≤ vatOut.size)
    (htail :
      ExecBlock config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut } evmVat
        ([ .assign .storage (ArtRef (.var "ilk")) (.tupleGet (.var "vatIlk") 0) ] ++
        checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"]
          "spotIlk" (perm := false) ++
        [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
        checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
          (perm := false) ++
        checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
          (perm := false) ++
        [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
          .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
        .reverted) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endCageIlkStore I) cageIlkTransition.body
      .reverted := by
  intro evm0
  have hprefix :
      ExecBlock config { contract := contract, locals := endCageIlkStore I } evm0
        (nonpayable ++
          [ .require (.binary .eq (.storage liveRef) (.intLit 0)),
            .require (.binary .eq (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
          checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
            "vatIlk")
        (.ok { contract := contract, locals := endCageIlkStoreVatIlk I vatOut } evmVat) := by
    simpa [evm0] using
      endCageIlkPrefixVatIlksSuccess
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (evmVat := evmVat) (vatOut := vatOut)
        hwv hsz36 hlive htag hcodeSize hcall hlo
  have hblock :
      ExecBlock config { contract := contract, locals := endCageIlkStore I } evm0
        cageIlkTransition.body .reverted := by
    have happ := Reasoning.Refinement.execBlock_append
      (s2 :=
        [ .assign .storage (ArtRef (.var "ilk")) (.tupleGet (.var "vatIlk") 0) ] ++
        checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"]
          "spotIlk" (perm := false) ++
        [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
        checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
          (perm := false) ++
        checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
          (perm := false) ++
        [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
          .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
      hprefix htail
    simpa [cageIlkTransition, List.append_assoc] using happ
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endCageIlkBodyReturns_vatIlksOkTail {cA gh bl σ σ₀ A I}
    {g : UInt256} {evmVat evmPost : EVM.State} {vatOut : ByteArray} {fPost : Frame}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hlive : endCageIlkLiveWord σ I = ⟨0⟩)
    (htag : endCageIlkTagWord σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "vatIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmVat, vatOut) true)
    (hlo : 160 ≤ vatOut.size)
    (htail :
      ExecBlock config { contract := contract, locals := endCageIlkStoreVatIlk I vatOut } evmVat
        ([ .assign .storage (ArtRef (.var "ilk")) (.tupleGet (.var "vatIlk") 0) ] ++
        checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"]
          "spotIlk" (perm := false) ++
        [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
        checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
          (perm := false) ++
        checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
          (perm := false) ++
        [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
          .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
        (.ok fPost evmPost)) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endCageIlkStore I) cageIlkTransition.body
      (.returned fPost evmPost none) := by
  intro evm0
  have hprefix :
      ExecBlock config { contract := contract, locals := endCageIlkStore I } evm0
        (nonpayable ++
          [ .require (.binary .eq (.storage liveRef) (.intLit 0)),
            .require (.binary .eq (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
          checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
            "vatIlk")
        (.ok { contract := contract, locals := endCageIlkStoreVatIlk I vatOut } evmVat) := by
    simpa [evm0] using
      endCageIlkPrefixVatIlksSuccess
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (evmVat := evmVat) (vatOut := vatOut)
        hwv hsz36 hlive htag hcodeSize hcall hlo
  have hblock :
      ExecBlock config { contract := contract, locals := endCageIlkStore I } evm0
        cageIlkTransition.body (.ok fPost evmPost) := by
    have happ := Reasoning.Refinement.execBlock_append
      (s2 :=
        [ .assign .storage (ArtRef (.var "ilk")) (.tupleGet (.var "vatIlk") 0) ] ++
        checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"]
          "spotIlk" (perm := false) ++
        [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
        checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
          (perm := false) ++
        checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
          (perm := false) ++
        [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
          .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
      hprefix htail
    simpa [cageIlkTransition, List.append_assoc] using happ
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockOK hblock

theorem endCageIlkBodyReverts_liveNonzero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : endCageIlkLiveWord σ I ≠ ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endCageIlkStore I) cageIlkTransition.body
      .reverted := by
  intro evm0
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨8⟩ ≠ ⟨0⟩ := by
    intro hbad
    apply hlive
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endCageIlkLiveWord, endSlotWord, solcSlotWord] using hbad
  have hguard :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_endCageIlk_live_zero_false evm0 I hliveLoad
  refine ExecFuncBody.execBlockRevert ?_
  simpa [cageIlkTransition, nonpayable, checkedExternalCallStmts] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := endCageIlkStore I })
      (evm := evm0)
      (guard := .binary .eq (.storage liveRef) (.intLit 0))
      (rest :=
        [ .require (.binary .eq (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
        checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk" ++
        [ .assign .storage (ArtRef (.var "ilk")) (.tupleGet (.var "vatIlk") 0) ] ++
        checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"]
          "spotIlk" (perm := false) ++
        [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
        checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
          (perm := false) ++
        checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
          (perm := false) ++
        [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
          .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
      (by simp only [evm0, initState]; exact hwv)
      hguard

theorem endCageIlkBodyReverts_tagNonzero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hlive : endCageIlkLiveWord σ I = ⟨0⟩)
    (htag : endCageIlkTagWord σ I ≠ ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endCageIlkStore I) cageIlkTransition.body
      .reverted := by
  intro evm0
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endCageIlkLiveWord, endSlotWord, solcSlotWord] using hlive
  have htagLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (endCageIlkTagSlot I) ≠ ⟨0⟩ := by
    intro hbad
    apply htag
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endCageIlkTagWord, endSlotWord, solcSlotWord] using hbad
  have hguardLive :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) := by
    have hstorage :
        evalExpr? config { contract := contract, locals := endCageIlkStore I } evm0
          (.storage liveRef) = .ok (.int 0) := by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := endCageIlkStore I })
        (slot := liveRef)
        (er := endCageIlkLiveEvaledRef)
        (t := .int uint256Int)
        (loc := wordLoc ⟨8⟩)
        (value := .int 0)
        (hbase := by simp [endCageIlkStore, liveRef])
        (her := evalStorageRef_endCageIlk_live evm0 I)
        (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
        (hloc := by rfl)
        (hload := by simpa [hliveLoad] using endStorageLocLoad_uint256 evm0 ⟨8⟩)]
    have hzero :
        evalExpr? config { contract := contract, locals := endCageIlkStore I } evm0
          (.intLit 0) = .ok (.int 0) := by
      simp [evalExpr?, pure]
    exact endEvalExpr_eq_int_true hstorage hzero rfl
  have hguardTag :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm0
        (.binary .eq (.storage (tagRef (.var "ilk"))) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_endCageIlk_tag_eq_false evm0 I hsz36 htagLoad
  have hblock :
      ExecBlock config { contract := contract, locals := endCageIlkStore I } evm0
        cageIlkTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguardTag)
  simpa [ExecTransitionBody, cageIlkTransition, nonpayable, checkedExternalCallStmts, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem endCageIlkX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endCageIlkEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := endBytecode) (sel := sel) (entry := endCageIlkEntryPc)
    (ret := endCageIlkReturnPc)
    (decoded := endCageIlkDecodedPc) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem endCageIlkBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some cageIlkTransition)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endCageIlkEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (endCageIlkX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (endDecode_cageIlk_none_short hsz4 hshort)

theorem endCageIlkBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf cageIlkTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endCageIlkConcreteSelector := by
    simpa [endCageIlkSelectorBytes, endCageIlkConcreteSelector] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endCageIlkConcreteSelector (by rfl) hsel'
  have hdispatch : dispatchMsg contract I.calldata = some cageIlkTransition :=
    endDispatchCageIlk hsel
  have hreach := endReachCageIlkBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel'
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode := endDecode_cageIlk_ok (I := I) hsz36
    obtain ⟨_, _, hbodyReach⟩ :=
      endCageIlkX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach
    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hliveCouple : endCageIlkLiveWord σ_evm I = endCageIlkLiveWord σ_solm I := by
      simpa [endCageIlkLiveWord, endSlotWord] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
    by_cases hlive : endCageIlkLiveWord σ_evm I = ⟨0⟩
    · have hliveSolm : endCageIlkLiveWord σ_solm I = ⟨0⟩ := by
        rw [← hliveCouple]
        exact hlive
      have htagCouple : endCageIlkTagWord σ_evm I = endCageIlkTagWord σ_solm I := by
        simpa [endCageIlkTagWord, endSlotWord] using
          accountMapEquiv_storage_findD hAccounts I.codeOwner (endCageIlkTagSlot I) ⟨0⟩
      by_cases htag : endCageIlkTagWord σ_evm I = ⟨0⟩
      · have htagSolm : endCageIlkTagWord σ_solm I = ⟨0⟩ := by
          rw [← htagCouple]
          exact htag
        by_cases hvatCode :
            Reasoning.Theory.uniswapExtCodeSizeWord σ_evm (endPackVatWord σ_evm I) =
              ⟨0⟩
        · have hvatCodeSolm :
              Reasoning.Theory.uniswapExtCodeSizeWord σ_solm
                (endPackVatWord σ_solm I) = ⟨0⟩ :=
            endPackVatCodeSize_zero_accountMapEquiv hAccounts hvatCode
          have hbody :
              ExecTransitionBody config contract evmSolm (endCageIlkStore I)
                cageIlkTransition.body .reverted := by
            simpa [evmSolm] using
              endCageIlkBodyReverts_vatIlksNoCode
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                (A := A) (I := I) (g := g)
                hwv hsz36 hliveSolm htagSolm hvatCodeSolm
          exact
            (endCageIlkX_vatIlksNoCode
              (g := Sat256.ofUInt256 g) hsz36 hlive htag hbodyReach hvatCode)
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hvatCodeNE :
              Reasoning.Theory.uniswapExtCodeSizeWord σ_evm
                (endPackVatWord σ_evm I) ≠ ⟨0⟩ := hvatCode
          have hvatCodeSolmNE :
              Reasoning.Theory.uniswapExtCodeSizeWord σ_solm
                (endPackVatWord σ_solm I) ≠ ⟨0⟩ :=
            endPackVatCodeSize_ne_accountMapEquiv hAccounts hvatCodeNE
          obtain ⟨gasWord, _, _, hcallReady⟩ :=
            endCageIlkX_vatIlksCallReady
              (g := Sat256.ofUInt256 g) hsz36 hlive htag hbodyReach hvatCodeNE
          by_cases hdepthLt : I.depth.val < 1024
          · obtain ⟨cA_vat, σ_vat, zVat, vatOut, AinVat, callGasVat, _, _, hΘVat,
                rd9081, hvatOutSize⟩ :=
              endCageIlkX_vatIlksPostCall hcallReady hdepthLt
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
              calc
                EVM.address (endPackVatAddr σ_evm I)
                    = EVM.address (AccountAddress.ofUInt256 (endPackVatWord σ_evm I)) := by
                      rw [endPackVatAddr_eq_ofUInt256]
                _ = AccountAddress.ofUInt256 (endPackVatWord σ_evm I) :=
                      endCageIlkAddress_ofUInt256 (endPackVatWord σ_evm I)
            obtain ⟨σ_vat_solm, A_vat_solm, hcallSolmRaw, hAccountsVat,
                hSubstateVat⟩ :=
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
                (mem := endCageIlkVatIlksCalldataMem I)
                (inOff := endFlowVatIlksOutPtr) (inSize := endFlowVatIlksInSize)
                (callPerm := true)
                hdepthNe htgtVat
                (endFlowVatIlksEncode_eq I hsz36
                  (twoWordHashMem_size_96 (endCageIlkIlkWord I) ⟨12⟩ solcFreePtrMem_size))
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
                  ExecTransitionBody config contract evmSolm (endCageIlkStore I)
                    cageIlkTransition.body .reverted := by
                simpa [evmSolm] using
                  endCageIlkBodyReverts_vatIlksCallFailed
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                    (A := A) (I := I) (g := g)
                    (evmVat :=
                      { evmSolm with
                        accountMap := σ_vat_solm
                        substate := A_vat_solm
                        createdAccounts := cA_vat })
                    (out := vatOut)
                    hwv hsz36 hliveSolm htagSolm hvatCodeSolmNE
                    (by simpa [evmSolm] using hcallSolm)
              exact (endCageIlkX_vatIlksCallFailed rd9081 hvatOutSize)
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
              obtain ⟨_, _, rd9099⟩ :=
                endCageIlkX_vatIlksCallSucceeded (g := Sat256.ofUInt256 g) rd9081
              by_cases hshortVat : vatOut.size < 160
              · have hbody :
                    ExecTransitionBody config contract evmSolm (endCageIlkStore I)
                      cageIlkTransition.body .reverted := by
                  simpa [evmVatSolm, evmSolm] using
                    endCageIlkBodyReverts_vatIlksDecodeShort
                      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                      (A := A) (I := I) (g := g)
                      (evmVat := evmVatSolm) (out := vatOut)
                      hwv hsz36 hliveSolm htagSolm hvatCodeSolmNE
                      (by simpa [evmVatSolm, evmSolm] using hcallSolm)
                      hshortVat
                exact (endCageIlkX_vatIlksReturnDecodeShort rd9099 hshortVat hvatOutSize)
                  |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · have hloVat : 160 ≤ vatOut.size := Nat.le_of_not_gt hshortVat
                obtain ⟨_, _, rd9122⟩ :=
                  endCageIlkX_vatIlksReturnDecodeOk rd9099 hloVat hvatOutSize
                have hStateVat : EVMStateEquiv evmVatEvm evmVatSolm := by
                  refine ⟨?_, ?_, ?_⟩
                  · simp [evmVatEvm, evmVatSolm, evmSolm, initState]
                  · simp [evmVatEvm, evmVatSolm, evmSolm, initState]
                  · simpa [evmVatEvm, evmVatSolm] using hAccountsVat
                let evmArtEvm := endCageIlkPostArtState evmVatEvm I vatOut
                let evmArtSolm := endCageIlkPostArtState evmVatSolm I vatOut
                have hStateArt : EVMStateEquiv evmArtEvm evmArtSolm := by
                  simpa [evmArtEvm, evmArtSolm, endCageIlkPostArtState] using
                    hStateVat.storageStore_codeOwner (endCageIlkArtSlot I)
                      (val₁ := endFlowVatIlkArtWord vatOut)
                      (val₂ := endFlowVatIlkArtWord vatOut) rfl
                by_cases hspotCode :
                    Reasoning.Theory.uniswapExtCodeSizeWord
                      (endCageIlkPostArtAccountMap σ_vat I vatOut)
                      (endCageIlkSpotWord (endCageIlkPostArtAccountMap σ_vat I vatOut) I) =
                        ⟨0⟩
                · have hspotCodeState :
                      Reasoning.Theory.uniswapExtCodeSizeWord evmArtEvm.accountMap
                        (endCageIlkSpotWord evmArtEvm.accountMap evmArtEvm.executionEnv) =
                          ⟨0⟩ := by
                    simpa [evmArtEvm, endCageIlkPostArtState, endCageIlkPostArtAccountMap,
                      storageStore_accountMap, storageStore_executionEnv] using hspotCode
                  have hspotCodeSolm :
                      Reasoning.Theory.uniswapExtCodeSizeWord evmArtSolm.accountMap
                        (endCageIlkSpotWord evmArtSolm.accountMap evmArtSolm.executionEnv) =
                          ⟨0⟩ :=
                    endCageIlkSpotCodeSize_zero_EVMStateEquiv hStateArt hspotCodeState
                  have htail :
                      ExecBlock config
                        { contract := contract, locals := endCageIlkStoreVatIlk I vatOut }
                        evmVatSolm
                        ([ .assign .storage (ArtRef (.var "ilk")) (.tupleGet (.var "vatIlk") 0) ] ++
                        checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0)
                          [.var "ilk"] "spotIlk" (perm := false) ++
                        [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
                        checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
                          (perm := false) ++
                        checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
                          (perm := false) ++
                        [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St]
                            "tagV",
                          .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
                        .reverted := by
                    simpa [evmArtSolm] using
                      endCageIlkTailFromVatReverts_spotNoCode evmVatSolm I vatOut hsz36
                        hspotCodeSolm
                  have hbody :
                      ExecTransitionBody config contract evmSolm (endCageIlkStore I)
                        cageIlkTransition.body .reverted := by
                    simpa [evmVatSolm, evmSolm] using
                      endCageIlkBodyReverts_vatIlksOkTailReverted
                        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                        (A := A) (I := I) (g := g) (evmVat := evmVatSolm)
                        (vatOut := vatOut)
                        hwv hsz36 hliveSolm htagSolm hvatCodeSolmNE
                        (by simpa [evmVatSolm, evmSolm] using hcallSolm)
                        hloVat htail
                  exact (endCageIlkX_spotIlksNoCode
                    (g := Sat256.ofUInt256 g) hsz36 hperm hloVat rd9122 hspotCode)
                    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                · have hspotCodeNE :
                    Reasoning.Theory.uniswapExtCodeSizeWord
                      (endCageIlkPostArtAccountMap σ_vat I vatOut)
                      (endCageIlkSpotWord (endCageIlkPostArtAccountMap σ_vat I vatOut) I) ≠
                        ⟨0⟩ := hspotCode
                  have hspotCodeStateNE :
                      Reasoning.Theory.uniswapExtCodeSizeWord evmArtEvm.accountMap
                        (endCageIlkSpotWord evmArtEvm.accountMap evmArtEvm.executionEnv) ≠
                          ⟨0⟩ := by
                    simpa [evmArtEvm, endCageIlkPostArtState, endCageIlkPostArtAccountMap,
                      storageStore_accountMap, storageStore_executionEnv] using hspotCodeNE
                  have hspotCodeSolmNE :
                      Reasoning.Theory.uniswapExtCodeSizeWord evmArtSolm.accountMap
                        (endCageIlkSpotWord evmArtSolm.accountMap evmArtSolm.executionEnv) ≠
                          ⟨0⟩ :=
                    endCageIlkSpotCodeSize_ne_EVMStateEquiv hStateArt hspotCodeStateNE
                  obtain ⟨spotGasWord, _, _, hspotReady⟩ :=
                    endCageIlkX_spotIlksCallReady
                      (g := Sat256.ofUInt256 g) hsz36 hperm hloVat rd9122 hspotCodeNE
                  by_cases hdepthLtSpot : I.depth.val < 1024
                  · obtain ⟨cA_spot, σ_spot, zSpot, spotOut, AinSpot, callGasSpot,
                        _, _, hΘSpot, rd9217, hspotOutSize⟩ :=
                      endCageIlkX_spotIlksPostStaticcall hspotReady hdepthLtSpot
                    rcases hΘSpot with ⟨gSpot'', ASpot, hΘSpotEq⟩
                    have hdepthNeSpot : evmArtEvm.executionEnv.depth ≠ 1024 := by
                      intro hbad
                      have hbadI : I.depth = 1024 := by
                        simpa [evmArtEvm, evmVatEvm, endCageIlkPostArtState, initState,
                          storageStore_executionEnv] using hbad
                      have hbadVal : I.depth.val = 1024 := congrArg Fin.val hbadI
                      omega
                    let spotTargetEvm :=
                      EVM.address
                        (AccountAddress.ofNat
                          (endCageIlkSpotWord evmArtEvm.accountMap
                            evmArtEvm.executionEnv).toNat)
                    have htgtSpot :
                        spotTargetEvm =
                          AccountAddress.ofUInt256
                            (endCageIlkSpotWord evmArtEvm.accountMap
                              evmArtEvm.executionEnv) := by
                      calc
                        spotTargetEvm =
                            EVM.address
                              (AccountAddress.ofUInt256
                                (endCageIlkSpotWord evmArtEvm.accountMap
                                  evmArtEvm.executionEnv)) := by
                          simp [spotTargetEvm, accountAddress_ofUInt256_eq_ofNat_toNat]
                        _ =
                            AccountAddress.ofUInt256
                              (endCageIlkSpotWord evmArtEvm.accountMap
                                evmArtEvm.executionEnv) :=
                          endCageIlkAddress_ofUInt256
                            (endCageIlkSpotWord evmArtEvm.accountMap evmArtEvm.executionEnv)
                    obtain ⟨σ_spot_solm, A_spot_solm, hcallSpotSolmRaw,
                        hAccountsSpot, hSubstateSpot⟩ :=
                      endCallMade_accountMapEquiv_with_substate
                        (cfg := config) (evm_evm := evmArtEvm) (evm_solm := evmArtSolm)
                        (tgt := spotTargetEvm)
                        (targetWord :=
                          endCageIlkSpotWord evmArtEvm.accountMap evmArtEvm.executionEnv)
                        (name := "spotIlks")
                        (args := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
                        (cA' := cA_spot) (σ' := σ_spot) (A' := ASpot)
                        (A_in := AinSpot) (z := zSpot) (out := spotOut)
                        (g'' := gSpot'') (callGas := callGasSpot)
                        (mem := endCageIlkSpotIlksCalldataMem I vatOut)
                        (inOff := endFlowVatIlksOutPtr) (inSize := endFlowVatIlksInSize)
                        (callPerm := false)
                        hdepthNeSpot htgtSpot
                        (endCageIlkSpotIlksEncode_eq I vatOut hsz36 hloVat)
                        (by
                          simpa [evmArtEvm, evmVatEvm, endCageIlkPostArtState,
                            endCageIlkPostArtAccountMap, initState, storageStore_accountMap,
                            storageStore_createdAccounts, storageStore_executionEnv, hperm]
                            using hΘSpotEq)
                        hStateArt.accountMap
                        (by simp [evmArtEvm, evmArtSolm, evmVatEvm, evmVatSolm, evmSolm,
                          endCageIlkPostArtState, initState])
                        hStateArt.createdAccounts.symm
                        (by simp [evmArtEvm, evmArtSolm, evmVatEvm, evmVatSolm, evmSolm,
                          endCageIlkPostArtState, initState])
                        (by simp [evmArtEvm, evmArtSolm, evmVatEvm, evmVatSolm, evmSolm,
                          endCageIlkPostArtState, initState])
                        hStateArt.executionEnv.symm
                    have hSpotWordEq :
                        endCageIlkSpotWord evmArtEvm.accountMap evmArtEvm.executionEnv =
                          endCageIlkSpotWord evmArtSolm.accountMap evmArtSolm.executionEnv := by
                      rw [← hStateArt.executionEnv]
                      exact endCageIlkSpotWord_accountMapEquiv hStateArt.accountMap
                    have hSpotTargetEq :
                        spotTargetEvm =
                          EVM.address
                            (AccountAddress.ofNat
                              (endCageIlkSpotWord evmArtSolm.accountMap
                                evmArtSolm.executionEnv).toNat) := by
                      simp [spotTargetEvm, hSpotWordEq]
                    have hcallSpotSolm :
                        typedCallViaEVM config evmArtSolm
                          (EVM.address
                            (AccountAddress.ofNat
                              (endCageIlkSpotWord evmArtSolm.accountMap
                                evmArtSolm.executionEnv).toNat))
                          "spotIlks" 0 [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
                          (zSpot,
                            { evmArtSolm with
                              accountMap := σ_spot_solm
                              substate := A_spot_solm
                              createdAccounts := cA_spot },
                            spotOut) false := by
                      simpa [hSpotTargetEq] using hcallSpotSolmRaw
                    cases zSpot
                    · have htail :
                        ExecBlock config
                          { contract := contract, locals := endCageIlkStoreVatIlk I vatOut }
                          evmVatSolm
                          ([ .assign .storage (ArtRef (.var "ilk"))
                              (.tupleGet (.var "vatIlk") 0) ] ++
                          checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0)
                            [.var "ilk"] "spotIlk" (perm := false) ++
                          [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
                          checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) []
                            "parV" (perm := false) ++
                          checkedExternalCallStmts (.var "pip") "read" (.intLit 0) []
                            "pipRead" (perm := false) ++
                          [ .internalCall "wdiv"
                              [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
                            .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
                          .reverted := by
                        simpa [evmArtSolm] using
                          endCageIlkTailFromVatReverts_spotFailure
                            (evmVat := evmVatSolm)
                            (evmSpot :=
                              { evmArtSolm with
                                accountMap := σ_spot_solm
                                substate := A_spot_solm
                                createdAccounts := cA_spot })
                            (I := I) (vatOut := vatOut) (spotOut := spotOut)
                            hsz36 hspotCodeSolmNE hcallSpotSolm
                      have hbody :
                          ExecTransitionBody config contract evmSolm (endCageIlkStore I)
                            cageIlkTransition.body .reverted := by
                        simpa [evmVatSolm, evmSolm] using
                          endCageIlkBodyReverts_vatIlksOkTailReverted
                            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                            (σ₀ := σ₀) (A := A) (I := I) (g := g)
                            (evmVat := evmVatSolm) (vatOut := vatOut)
                            hwv hsz36 hliveSolm htagSolm hvatCodeSolmNE
                            (by simpa [evmVatSolm, evmSolm] using hcallSolm)
                            hloVat htail
                      have rd9217Fail := rd9217
                      simp only [Bool.false_eq_true, if_false] at rd9217Fail
                      exact (endCageIlkX_spotIlksCallFailed
                        (vatOut := vatOut) (rdata := spotOut) rd9217Fail hspotOutSize)
                        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                    · let evmSpotSolm :=
                        { evmArtSolm with
                          accountMap := σ_spot_solm
                          substate := A_spot_solm
                          createdAccounts := cA_spot }
                      have rd9217Ok := rd9217
                      simp only [if_true] at rd9217Ok
                      obtain ⟨_, _, rd9235⟩ :=
                        endCageIlkX_spotIlksCallSucceeded
                          (g := Sat256.ofUInt256 g) (vatOut := vatOut)
                          (rdata := spotOut) rd9217Ok
                      by_cases hshortSpot : spotOut.size < 64
                      · have htail :
                          ExecBlock config
                            { contract := contract, locals := endCageIlkStoreVatIlk I vatOut }
                            evmVatSolm
                            ([ .assign .storage (ArtRef (.var "ilk"))
                                (.tupleGet (.var "vatIlk") 0) ] ++
                            checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0)
                              [.var "ilk"] "spotIlk" (perm := false) ++
                            [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
                            checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) []
                              "parV" (perm := false) ++
                            checkedExternalCallStmts (.var "pip") "read" (.intLit 0) []
                              "pipRead" (perm := false) ++
                            [ .internalCall "wdiv"
                                [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
                              .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
                            .reverted := by
                          simpa [evmSpotSolm, evmArtSolm] using
                            endCageIlkTailFromVatReverts_spotDecodeShort
                              (evmVat := evmVatSolm) (evmSpot := evmSpotSolm)
                              (I := I) (vatOut := vatOut) (spotOut := spotOut)
                              hsz36 hspotCodeSolmNE
                              (by simpa [evmSpotSolm] using hcallSpotSolm)
                              hshortSpot
                        have hbody :
                            ExecTransitionBody config contract evmSolm (endCageIlkStore I)
                              cageIlkTransition.body .reverted := by
                          simpa [evmVatSolm, evmSolm] using
                            endCageIlkBodyReverts_vatIlksOkTailReverted
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                              (σ₀ := σ₀) (A := A) (I := I) (g := g)
                              (evmVat := evmVatSolm) (vatOut := vatOut)
                              hwv hsz36 hliveSolm htagSolm hvatCodeSolmNE
                              (by simpa [evmVatSolm, evmSolm] using hcallSolm)
                              hloVat htail
                        exact
                          (endCageIlkX_spotIlksReturnDecodeShort rd9235 hloVat
                            hshortSpot hspotOutSize)
                            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                      · have hloSpot : 64 ≤ spotOut.size := Nat.le_of_not_gt hshortSpot
                        obtain ⟨_, _, rd9258⟩ :=
                          endCageIlkX_spotIlksReturnDecodeOk rd9235 hloVat hloSpot
                            hspotOutSize
                        let evmSpotEvm :=
                          { evmArtEvm with
                            accountMap := σ_spot
                            substate := ASpot
                            createdAccounts := cA_spot }
                        have hStateSpot : EVMStateEquiv evmSpotEvm evmSpotSolm := by
                          refine ⟨?_, ?_, ?_⟩
                          · simpa [evmSpotEvm, evmSpotSolm] using hStateArt.executionEnv
                          · simpa [evmSpotEvm, evmSpotSolm] using hStateArt.createdAccounts
                          · simpa [evmSpotEvm, evmSpotSolm] using hAccountsSpot
                        by_cases hparCode :
                            Reasoning.Theory.uniswapExtCodeSizeWord σ_spot
                              (endCageIlkSpotWord σ_spot I) = ⟨0⟩
                        · have hparCodeState :
                              Reasoning.Theory.uniswapExtCodeSizeWord evmSpotEvm.accountMap
                                (endCageIlkSpotWord evmSpotEvm.accountMap
                                  evmSpotEvm.executionEnv) = ⟨0⟩ := by
                            simpa [evmSpotEvm, evmArtEvm, endCageIlkPostArtState,
                              storageStore_executionEnv] using hparCode
                          have hparCodeSolm :
                              Reasoning.Theory.uniswapExtCodeSizeWord evmSpotSolm.accountMap
                                (endCageIlkSpotWord evmSpotSolm.accountMap
                                  evmSpotSolm.executionEnv) = ⟨0⟩ :=
                            endCageIlkSpotCodeSize_zero_EVMStateEquiv hStateSpot hparCodeState
                          have htailPip :=
                            endCageIlkTailAfterSpotReverts_parNoCode
                              evmSpotSolm I vatOut spotOut hparCodeSolm
                          have htail :
                              ExecBlock config
                                { contract := contract, locals := endCageIlkStoreVatIlk I vatOut }
                                evmVatSolm
                                ([ .assign .storage (ArtRef (.var "ilk"))
                                    (.tupleGet (.var "vatIlk") 0) ] ++
                                checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0)
                                  [.var "ilk"] "spotIlk" (perm := false) ++
                                [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
                                checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) []
                                  "parV" (perm := false) ++
                                checkedExternalCallStmts (.var "pip") "read" (.intLit 0) []
                                  "pipRead" (perm := false) ++
                                [ .internalCall "wdiv"
                                    [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
                                  .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
                                .reverted := by
                            simpa [evmSpotSolm, evmArtSolm] using
                              endCageIlkTailFromVatSpotOk
                                (evmVat := evmVatSolm) (evmSpot := evmSpotSolm)
                                (I := I) (vatOut := vatOut) (spotOut := spotOut)
                                hsz36 hspotCodeSolmNE
                                (by simpa [evmSpotSolm, evmArtSolm] using hcallSpotSolm)
                                hloSpot htailPip
                          have hbody :
                              ExecTransitionBody config contract evmSolm (endCageIlkStore I)
                                cageIlkTransition.body .reverted := by
                            simpa [evmVatSolm, evmSolm] using
                              endCageIlkBodyReverts_vatIlksOkTailReverted
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                                (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                (evmVat := evmVatSolm) (vatOut := vatOut)
                                hwv hsz36 hliveSolm htagSolm hvatCodeSolmNE
                                (by simpa [evmVatSolm, evmSolm] using hcallSolm)
                                hloVat htail
                          exact (endCageIlkX_parNoCode hloVat hspotOutSize rd9258 hparCode)
                            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                        · have hparCodeNE :
                            Reasoning.Theory.uniswapExtCodeSizeWord σ_spot
                              (endCageIlkSpotWord σ_spot I) ≠ ⟨0⟩ := hparCode
                          have hparCodeStateNE :
                              Reasoning.Theory.uniswapExtCodeSizeWord evmSpotEvm.accountMap
                                (endCageIlkSpotWord evmSpotEvm.accountMap
                                  evmSpotEvm.executionEnv) ≠ ⟨0⟩ := by
                            simpa [evmSpotEvm, evmArtEvm, endCageIlkPostArtState,
                              storageStore_executionEnv] using hparCodeNE
                          have hparCodeSolmNE :
                              Reasoning.Theory.uniswapExtCodeSizeWord evmSpotSolm.accountMap
                                (endCageIlkSpotWord evmSpotSolm.accountMap
                                  evmSpotSolm.executionEnv) ≠ ⟨0⟩ :=
                            endCageIlkSpotCodeSize_ne_EVMStateEquiv hStateSpot hparCodeStateNE
                          obtain ⟨parGasWord, _, _, hparReady⟩ :=
                            endCageIlkX_parCallReady hloVat hspotOutSize rd9258 hparCodeNE
                          by_cases hdepthLtPar : I.depth.val < 1024
                          · obtain ⟨cA_par, σ_par, zPar, parOut, AinPar, callGasPar,
                                _, _, hΘPar, rd9337, hparOutSize⟩ :=
                              endCageIlkX_parPostStaticcall hparReady hdepthLtPar
                            rcases hΘPar with ⟨gPar'', APar, hΘParEq⟩
                            have hdepthNePar : evmSpotEvm.executionEnv.depth ≠ 1024 := by
                              intro hbad
                              have hbadI : I.depth = 1024 := by
                                simpa [evmSpotEvm, evmArtEvm, evmVatEvm,
                                  endCageIlkPostArtState, initState, storageStore_executionEnv]
                                  using hbad
                              have hbadVal : I.depth.val = 1024 := congrArg Fin.val hbadI
                              omega
                            let parTargetEvm :=
                              EVM.address
                                (AccountAddress.ofNat
                                  (endCageIlkSpotWord evmSpotEvm.accountMap
                                    evmSpotEvm.executionEnv).toNat)
                            have htgtPar :
                                parTargetEvm =
                                  AccountAddress.ofUInt256
                                    (endCageIlkSpotWord evmSpotEvm.accountMap
                                      evmSpotEvm.executionEnv) := by
                              calc
                                parTargetEvm =
                                    EVM.address
                                      (AccountAddress.ofUInt256
                                        (endCageIlkSpotWord evmSpotEvm.accountMap
                                          evmSpotEvm.executionEnv)) := by
                                  simp [parTargetEvm, accountAddress_ofUInt256_eq_ofNat_toNat]
                                _ =
                                    AccountAddress.ofUInt256
                                      (endCageIlkSpotWord evmSpotEvm.accountMap
                                        evmSpotEvm.executionEnv) :=
                                  endCageIlkAddress_ofUInt256
                                    (endCageIlkSpotWord evmSpotEvm.accountMap
                                      evmSpotEvm.executionEnv)
                            obtain ⟨σ_par_solm, A_par_solm, hcallParSolmRaw,
                                hAccountsPar, hSubstatePar⟩ :=
                              endCallMade_accountMapEquiv_with_substate
                                (cfg := config) (evm_evm := evmSpotEvm)
                                (evm_solm := evmSpotSolm) (tgt := parTargetEvm)
                                (targetWord :=
                                  endCageIlkSpotWord evmSpotEvm.accountMap
                                    evmSpotEvm.executionEnv)
                                (name := "par") (args := [])
                                (cA' := cA_par) (σ' := σ_par) (A' := APar)
                                (A_in := AinPar) (z := zPar) (out := parOut)
                                (g'' := gPar'') (callGas := callGasPar)
                                (mem := endCageIlkParCalldataMem I vatOut spotOut)
                                (inOff := endFlowVatIlksOutPtr)
                                (inSize := endCageIlkNoArgInSize)
                                (callPerm := false)
                                hdepthNePar htgtPar
                                (endCageIlkParEncode_eq I vatOut spotOut hloVat hspotOutSize)
                                (by
                                  simpa [evmSpotEvm, evmArtEvm, evmVatEvm,
                                    endCageIlkPostArtState, initState, storageStore_accountMap,
                                    storageStore_createdAccounts, storageStore_executionEnv, hperm]
                                    using hΘParEq)
                                hStateSpot.accountMap
                                (by simp [evmSpotEvm, evmSpotSolm, evmArtEvm, evmArtSolm,
                                  evmVatEvm, evmVatSolm, evmSolm, endCageIlkPostArtState,
                                  initState])
                                hStateSpot.createdAccounts.symm
                                (by simp [evmSpotEvm, evmSpotSolm, evmArtEvm, evmArtSolm,
                                  evmVatEvm, evmVatSolm, evmSolm, endCageIlkPostArtState,
                                  initState])
                                (by simp [evmSpotEvm, evmSpotSolm, evmArtEvm, evmArtSolm,
                                  evmVatEvm, evmVatSolm, evmSolm, endCageIlkPostArtState,
                                  initState])
                                hStateSpot.executionEnv.symm
                            have hParWordEq :
                                endCageIlkSpotWord evmSpotEvm.accountMap evmSpotEvm.executionEnv =
                                  endCageIlkSpotWord evmSpotSolm.accountMap
                                    evmSpotSolm.executionEnv := by
                              rw [← hStateSpot.executionEnv]
                              exact endCageIlkSpotWord_accountMapEquiv hStateSpot.accountMap
                            have hParTargetEq :
                                parTargetEvm =
                                  EVM.address
                                    (AccountAddress.ofNat
                                      (endCageIlkSpotWord evmSpotSolm.accountMap
                                        evmSpotSolm.executionEnv).toNat) := by
                              simp [parTargetEvm, hParWordEq]
                            have hcallParSolm :
                                typedCallViaEVM config evmSpotSolm
                                  (EVM.address
                                    (AccountAddress.ofNat
                                      (endCageIlkSpotWord evmSpotSolm.accountMap
                                        evmSpotSolm.executionEnv).toNat))
                                  "par" 0 []
                                  (zPar,
                                    { evmSpotSolm with
                                      accountMap := σ_par_solm
                                      substate := A_par_solm
                                      createdAccounts := cA_par },
                                    parOut) false := by
                              simpa [hParTargetEq] using hcallParSolmRaw
                            cases zPar
                            · have rd9337Fail := rd9337
                              simp only [Bool.false_eq_true, if_false] at rd9337Fail
                              have htailPip :=
                                endCageIlkTailAfterSpotReverts_parFailure
                                  (evmSpot := evmSpotSolm)
                                  (evmPar :=
                                    { evmSpotSolm with
                                      accountMap := σ_par_solm
                                      substate := A_par_solm
                                      createdAccounts := cA_par })
                                  (I := I) (vatOut := vatOut) (spotOut := spotOut)
                                  (parOut := parOut) hparCodeSolmNE hcallParSolm
                              have htail :
                                  ExecBlock config
                                    { contract := contract,
                                      locals := endCageIlkStoreVatIlk I vatOut }
                                    evmVatSolm
                                    ([ .assign .storage (ArtRef (.var "ilk"))
                                        (.tupleGet (.var "vatIlk") 0) ] ++
                                    checkedExternalCallStmts (.storage spotRef) "spotIlks"
                                      (.intLit 0) [.var "ilk"] "spotIlk" (perm := false) ++
                                    [ .letDecl "pip" (some addr)
                                        (.tupleGet (.var "spotIlk") 0) ] ++
                                    checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0)
                                      [] "parV" (perm := false) ++
                                    checkedExternalCallStmts (.var "pip") "read" (.intLit 0) []
                                      "pipRead" (perm := false) ++
                                    [ .internalCall "wdiv"
                                        [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
                                      .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
                                    .reverted := by
                                simpa [evmSpotSolm, evmArtSolm] using
                                  endCageIlkTailFromVatSpotOk
                                    (evmVat := evmVatSolm) (evmSpot := evmSpotSolm)
                                    (I := I) (vatOut := vatOut) (spotOut := spotOut)
                                    hsz36 hspotCodeSolmNE
                                    (by simpa [evmSpotSolm, evmArtSolm] using hcallSpotSolm)
                                    hloSpot htailPip
                              have hbody :
                                  ExecTransitionBody config contract evmSolm (endCageIlkStore I)
                                    cageIlkTransition.body .reverted := by
                                simpa [evmVatSolm, evmSolm] using
                                  endCageIlkBodyReverts_vatIlksOkTailReverted
                                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                                    (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                    (evmVat := evmVatSolm) (vatOut := vatOut)
                                    hwv hsz36 hliveSolm htagSolm hvatCodeSolmNE
                                    (by simpa [evmVatSolm, evmSolm] using hcallSolm)
                                    hloVat htail
                              exact (endCageIlkX_parCallFailed
                                (rdata := parOut) rd9337Fail hparOutSize)
                                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                            · let evmParSolm :=
                                { evmSpotSolm with
                                  accountMap := σ_par_solm
                                  substate := A_par_solm
                                  createdAccounts := cA_par }
                              have rd9337Ok := rd9337
                              simp only [if_true] at rd9337Ok
                              obtain ⟨_, _, rd9355⟩ :=
                                endCageIlkX_parCallSucceeded
                                  (g := Sat256.ofUInt256 g) (rdata := parOut) rd9337Ok
                              by_cases hshortPar : parOut.size < 32
                              · have htailPip :=
                                  endCageIlkTailAfterSpotReverts_parDecodeShort
                                    (evmSpot := evmSpotSolm) (evmPar := evmParSolm)
                                    (I := I) (vatOut := vatOut) (spotOut := spotOut)
                                    (parOut := parOut) hparCodeSolmNE
                                    (by simpa [evmParSolm] using hcallParSolm)
                                    hshortPar
                                have htail :
                                    ExecBlock config
                                      { contract := contract,
                                        locals := endCageIlkStoreVatIlk I vatOut }
                                      evmVatSolm
                                      ([ .assign .storage (ArtRef (.var "ilk"))
                                          (.tupleGet (.var "vatIlk") 0) ] ++
                                      checkedExternalCallStmts (.storage spotRef) "spotIlks"
                                        (.intLit 0) [.var "ilk"] "spotIlk" (perm := false) ++
                                      [ .letDecl "pip" (some addr)
                                          (.tupleGet (.var "spotIlk") 0) ] ++
                                      checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0)
                                        [] "parV" (perm := false) ++
                                      checkedExternalCallStmts (.var "pip") "read" (.intLit 0) []
                                        "pipRead" (perm := false) ++
                                      [ .internalCall "wdiv"
                                          [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
                                        .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
                                      .reverted := by
                                  simpa [evmSpotSolm, evmArtSolm] using
                                    endCageIlkTailFromVatSpotOk
                                      (evmVat := evmVatSolm) (evmSpot := evmSpotSolm)
                                      (I := I) (vatOut := vatOut) (spotOut := spotOut)
                                      hsz36 hspotCodeSolmNE
                                      (by simpa [evmSpotSolm, evmArtSolm] using hcallSpotSolm)
                                      hloSpot htailPip
                                have hbody :
                                    ExecTransitionBody config contract evmSolm (endCageIlkStore I)
                                      cageIlkTransition.body .reverted := by
                                  simpa [evmVatSolm, evmSolm] using
                                    endCageIlkBodyReverts_vatIlksOkTailReverted
                                      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                                      (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                      (evmVat := evmVatSolm) (vatOut := vatOut)
                                      hwv hsz36 hliveSolm htagSolm hvatCodeSolmNE
                                      (by simpa [evmVatSolm, evmSolm] using hcallSolm)
                                      hloVat htail
                                exact
                                  (endCageIlkX_parReturnDecodeShort hloVat hspotOutSize
                                    rd9355 hshortPar hparOutSize)
                                    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                              · have hloPar : 32 ≤ parOut.size := Nat.le_of_not_gt hshortPar
                                obtain ⟨_, _, rd9378⟩ :=
                                  endCageIlkX_parReturnDecodeOk hloVat hspotOutSize rd9355
                                    hloPar hparOutSize
                                let evmParEvm :=
                                  { evmSpotEvm with
                                    accountMap := σ_par
                                    substate := APar
                                    createdAccounts := cA_par }
                                have hStatePar : EVMStateEquiv evmParEvm evmParSolm := by
                                  refine ⟨?_, ?_, ?_⟩
                                  · simpa [evmParEvm, evmParSolm] using hStateSpot.executionEnv
                                  · simp [evmParEvm, evmParSolm]
                                  · simpa [evmParEvm, evmParSolm] using hAccountsPar
                                have tailPipFromParTail {res : ExecResult}
                                    (htailRead :
                                      ExecBlock config
                                        { contract := contract,
                                          locals := endCageIlkStorePar I vatOut spotOut parOut }
                                        evmParSolm
                                        (checkedExternalCallStmts (.var "pip") "read"
                                          (.intLit 0) [] "pipRead" (perm := false) ++
                                        [ .internalCall "wdiv"
                                            [.var "parV", .cast (.var "pipRead") uint256St]
                                            "tagV",
                                          .assign .storage (tagRef (.var "ilk"))
                                            (.var "tagV") ])
                                        res) :
                                      ExecBlock config
                                        { contract := contract,
                                          locals := endCageIlkStorePip I vatOut spotOut }
                                        evmSpotSolm
                                        (checkedExternalCallStmts (.storage spotRef) "par"
                                          (.intLit 0) [] "parV" (perm := false) ++
                                        checkedExternalCallStmts (.var "pip") "read"
                                          (.intLit 0) [] "pipRead" (perm := false) ++
                                        [ .internalCall "wdiv"
                                            [.var "parV", .cast (.var "pipRead") uint256St]
                                            "tagV",
                                          .assign .storage (tagRef (.var "ilk"))
                                            (.var "tagV") ])
                                        res := by
                                  exact
                                    endCageIlkTailAfterSpotParOk
                                      (evmSpot := evmSpotSolm) (evmPar := evmParSolm)
                                      (I := I) (vatOut := vatOut) (spotOut := spotOut)
                                      (parOut := parOut) hparCodeSolmNE
                                      (by simpa [evmParSolm] using hcallParSolm)
                                      hloPar htailRead
                                have bodyRevertFromPip
                                    (htailPip :
                                      ExecBlock config
                                        { contract := contract,
                                          locals := endCageIlkStorePip I vatOut spotOut }
                                        evmSpotSolm
                                        (checkedExternalCallStmts (.storage spotRef) "par"
                                          (.intLit 0) [] "parV" (perm := false) ++
                                        checkedExternalCallStmts (.var "pip") "read"
                                          (.intLit 0) [] "pipRead" (perm := false) ++
                                        [ .internalCall "wdiv"
                                            [.var "parV", .cast (.var "pipRead") uint256St]
                                            "tagV",
                                          .assign .storage (tagRef (.var "ilk"))
                                            (.var "tagV") ])
                                        .reverted) :
                                      ExecTransitionBody config contract evmSolm
                                        (endCageIlkStore I) cageIlkTransition.body
                                        .reverted := by
                                  have htail :
                                      ExecBlock config
                                        { contract := contract,
                                          locals := endCageIlkStoreVatIlk I vatOut }
                                        evmVatSolm
                                        ([ .assign .storage (ArtRef (.var "ilk"))
                                            (.tupleGet (.var "vatIlk") 0) ] ++
                                        checkedExternalCallStmts (.storage spotRef)
                                          "spotIlks" (.intLit 0) [.var "ilk"] "spotIlk"
                                          (perm := false) ++
                                        [ .letDecl "pip" (some addr)
                                            (.tupleGet (.var "spotIlk") 0) ] ++
                                        checkedExternalCallStmts (.storage spotRef) "par"
                                          (.intLit 0) [] "parV" (perm := false) ++
                                        checkedExternalCallStmts (.var "pip") "read"
                                          (.intLit 0) [] "pipRead" (perm := false) ++
                                        [ .internalCall "wdiv"
                                            [.var "parV", .cast (.var "pipRead") uint256St]
                                            "tagV",
                                          .assign .storage (tagRef (.var "ilk"))
                                            (.var "tagV") ])
                                        .reverted := by
                                    simpa [evmSpotSolm, evmArtSolm] using
                                      endCageIlkTailFromVatSpotOk
                                        (evmVat := evmVatSolm) (evmSpot := evmSpotSolm)
                                        (I := I) (vatOut := vatOut) (spotOut := spotOut)
                                        hsz36 hspotCodeSolmNE
                                        (by simpa [evmSpotSolm, evmArtSolm] using
                                          hcallSpotSolm)
                                        hloSpot htailPip
                                  simpa [evmVatSolm, evmSolm] using
                                    endCageIlkBodyReverts_vatIlksOkTailReverted
                                      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                                      (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                      (evmVat := evmVatSolm) (vatOut := vatOut)
                                      hwv hsz36 hliveSolm htagSolm hvatCodeSolmNE
                                      (by simpa [evmVatSolm, evmSolm] using hcallSolm)
                                      hloVat htail
                                have bodyReturnFromPip {fPost : Frame} {evmPost : EVM.State}
                                    (htailPip :
                                      ExecBlock config
                                        { contract := contract,
                                          locals := endCageIlkStorePip I vatOut spotOut }
                                        evmSpotSolm
                                        (checkedExternalCallStmts (.storage spotRef) "par"
                                          (.intLit 0) [] "parV" (perm := false) ++
                                        checkedExternalCallStmts (.var "pip") "read"
                                          (.intLit 0) [] "pipRead" (perm := false) ++
                                        [ .internalCall "wdiv"
                                            [.var "parV", .cast (.var "pipRead") uint256St]
                                            "tagV",
                                          .assign .storage (tagRef (.var "ilk"))
                                            (.var "tagV") ])
                                        (.ok fPost evmPost)) :
                                      ExecTransitionBody config contract evmSolm
                                        (endCageIlkStore I) cageIlkTransition.body
                                        (.returned fPost evmPost none) := by
                                  have htail :
                                      ExecBlock config
                                        { contract := contract,
                                          locals := endCageIlkStoreVatIlk I vatOut }
                                        evmVatSolm
                                        ([ .assign .storage (ArtRef (.var "ilk"))
                                            (.tupleGet (.var "vatIlk") 0) ] ++
                                        checkedExternalCallStmts (.storage spotRef)
                                          "spotIlks" (.intLit 0) [.var "ilk"] "spotIlk"
                                          (perm := false) ++
                                        [ .letDecl "pip" (some addr)
                                            (.tupleGet (.var "spotIlk") 0) ] ++
                                        checkedExternalCallStmts (.storage spotRef) "par"
                                          (.intLit 0) [] "parV" (perm := false) ++
                                        checkedExternalCallStmts (.var "pip") "read"
                                          (.intLit 0) [] "pipRead" (perm := false) ++
                                        [ .internalCall "wdiv"
                                            [.var "parV", .cast (.var "pipRead") uint256St]
                                            "tagV",
                                          .assign .storage (tagRef (.var "ilk"))
                                            (.var "tagV") ])
                                        (.ok fPost evmPost) := by
                                    simpa [evmSpotSolm, evmArtSolm] using
                                      endCageIlkTailFromVatSpotOk
                                        (evmVat := evmVatSolm) (evmSpot := evmSpotSolm)
                                        (I := I) (vatOut := vatOut) (spotOut := spotOut)
                                        hsz36 hspotCodeSolmNE
                                        (by simpa [evmSpotSolm, evmArtSolm] using
                                          hcallSpotSolm)
                                        hloSpot htailPip
                                  simpa [evmVatSolm, evmSolm] using
                                    endCageIlkBodyReturns_vatIlksOkTail
                                      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                                      (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                      (evmVat := evmVatSolm) (vatOut := vatOut)
                                      hwv hsz36 hliveSolm htagSolm hvatCodeSolmNE
                                      (by simpa [evmVatSolm, evmSolm] using hcallSolm)
                                      hloVat htail
                                by_cases hreadCode :
                                    Reasoning.Theory.uniswapExtCodeSizeWord σ_par
                                      (endCageIlkPipCallWord spotOut) = ⟨0⟩
                                · have hreadCodeState :
                                      Reasoning.Theory.uniswapExtCodeSizeWord
                                        evmParEvm.accountMap
                                        (endCageIlkPipCallWord spotOut) = ⟨0⟩ := by
                                    simpa [evmParEvm] using hreadCode
                                  have hreadCodeSolm :
                                      Reasoning.Theory.uniswapExtCodeSizeWord
                                        evmParSolm.accountMap
                                        (endCageIlkPipCallWord spotOut) = ⟨0⟩ :=
                                    endCageIlkPipCodeSize_zero_accountMapEquiv
                                      hStatePar.accountMap spotOut hreadCodeState
                                  have htailRead :=
                                    endCageIlkTailAfterParReverts_readNoCode
                                      evmParSolm I vatOut spotOut parOut hreadCodeSolm
                                  have hbody := bodyRevertFromPip
                                    (tailPipFromParTail htailRead)
                                  exact
                                    (endCageIlkX_readNoCode hloVat hspotOutSize
                                      hparOutSize rd9378 hreadCode)
                                      |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                                · have hreadCodeNE :
                                      Reasoning.Theory.uniswapExtCodeSizeWord σ_par
                                        (endCageIlkPipCallWord spotOut) ≠ ⟨0⟩ := hreadCode
                                  have hreadCodeStateNE :
                                      Reasoning.Theory.uniswapExtCodeSizeWord
                                        evmParEvm.accountMap
                                        (endCageIlkPipCallWord spotOut) ≠ ⟨0⟩ := by
                                    simpa [evmParEvm] using hreadCodeNE
                                  have hreadCodeSolmNE :
                                      Reasoning.Theory.uniswapExtCodeSizeWord
                                        evmParSolm.accountMap
                                        (endCageIlkPipCallWord spotOut) ≠ ⟨0⟩ :=
                                    endCageIlkPipCodeSize_ne_accountMapEquiv
                                      hStatePar.accountMap spotOut hreadCodeStateNE
                                  obtain ⟨readGasWord, _, _, hreadReady⟩ :=
                                    endCageIlkX_readCallReady hloVat hspotOutSize
                                      hparOutSize rd9378 hreadCodeNE
                                  by_cases hdepthLtRead : I.depth.val < 1024
                                  · obtain ⟨cA_read, σ_read, zRead, readOut, AinRead,
                                        callGasRead, _, _, hΘRead, rd9445,
                                        hreadOutSize⟩ :=
                                      endCageIlkX_readPostStaticcall hreadReady
                                        hdepthLtRead
                                    rcases hΘRead with ⟨gRead'', ARead, hΘReadEq⟩
                                    have hdepthNeRead :
                                        evmParEvm.executionEnv.depth ≠ 1024 := by
                                      intro hbad
                                      have hbadI : I.depth = 1024 := by
                                        simpa [evmParEvm, evmSpotEvm, evmArtEvm,
                                          evmVatEvm, endCageIlkPostArtState, initState,
                                          storageStore_executionEnv] using hbad
                                      have hbadVal : I.depth.val = 1024 :=
                                        congrArg Fin.val hbadI
                                      omega
                                    let readTargetEvm :=
                                      EVM.address (endCageIlkSpotIlkPipAddr spotOut)
                                    have htgtRead :
                                        readTargetEvm =
                                          AccountAddress.ofUInt256
                                            (endCageIlkPipCallWord spotOut) := by
                                      calc
                                        readTargetEvm =
                                            EVM.address
                                              (AccountAddress.ofUInt256
                                                (endCageIlkPipCallWord spotOut)) := by
                                          simp [readTargetEvm,
                                            endCageIlkPipAddr_eq_ofUInt256]
                                        _ =
                                            AccountAddress.ofUInt256
                                              (endCageIlkPipCallWord spotOut) :=
                                          endCageIlkAddress_ofUInt256
                                            (endCageIlkPipCallWord spotOut)
                                    obtain ⟨σ_read_solm, A_read_solm, hcallReadSolmRaw,
                                        hAccountsRead, hSubstateRead⟩ :=
                                      endCallMade_accountMapEquiv_with_substate
                                        (cfg := config) (evm_evm := evmParEvm)
                                        (evm_solm := evmParSolm) (tgt := readTargetEvm)
                                        (targetWord := endCageIlkPipCallWord spotOut)
                                        (name := "read") (args := [])
                                        (cA' := cA_read) (σ' := σ_read)
                                        (A' := ARead) (A_in := AinRead)
                                        (z := zRead) (out := readOut)
                                        (g'' := gRead'') (callGas := callGasRead)
                                        (mem :=
                                          endCageIlkReadCalldataMem I vatOut spotOut parOut)
                                        (inOff := endFlowVatIlksOutPtr)
                                        (inSize := endCageIlkNoArgInSize)
                                        (callPerm := false)
                                        hdepthNeRead htgtRead
                                        (endCageIlkReadEncode_eq I vatOut spotOut parOut
                                          hloVat hspotOutSize hparOutSize)
                                        (by
                                          simpa [evmParEvm, evmSpotEvm, evmArtEvm,
                                            evmVatEvm, endCageIlkPostArtState, initState,
                                            storageStore_accountMap, storageStore_createdAccounts,
                                            storageStore_executionEnv, hperm] using hΘReadEq)
                                        hStatePar.accountMap
                                        (by
                                          simp [evmParEvm, evmParSolm, evmSpotEvm,
                                            evmSpotSolm, evmArtEvm, evmArtSolm, evmVatEvm,
                                            evmVatSolm, evmSolm, endCageIlkPostArtState,
                                            initState])
                                        hStatePar.createdAccounts.symm
                                        (by
                                          simp [evmParEvm, evmParSolm, evmSpotEvm,
                                            evmSpotSolm, evmArtEvm, evmArtSolm, evmVatEvm,
                                            evmVatSolm, evmSolm, endCageIlkPostArtState,
                                            initState])
                                        (by
                                          simp [evmParEvm, evmParSolm, evmSpotEvm,
                                            evmSpotSolm, evmArtEvm, evmArtSolm, evmVatEvm,
                                            evmVatSolm, evmSolm, endCageIlkPostArtState,
                                            initState])
                                        hStatePar.executionEnv.symm
                                    have hcallReadSolm :
                                        typedCallViaEVM config evmParSolm
                                          (EVM.address (endCageIlkSpotIlkPipAddr spotOut))
                                          "read" 0 []
                                          (zRead,
                                            { evmParSolm with
                                              accountMap := σ_read_solm
                                              substate := A_read_solm
                                              createdAccounts := cA_read },
                                            readOut) false := by
                                      simpa [readTargetEvm] using hcallReadSolmRaw
                                    cases zRead
                                    · have rd9445Fail := rd9445
                                      simp only [Bool.false_eq_true, if_false] at rd9445Fail
                                      have htailRead :=
                                        endCageIlkTailAfterParReverts_readFailure
                                          (evmPar := evmParSolm)
                                          (evmRead :=
                                            { evmParSolm with
                                              accountMap := σ_read_solm
                                              substate := A_read_solm
                                              createdAccounts := cA_read })
                                          (I := I) (vatOut := vatOut) (spotOut := spotOut)
                                          (parOut := parOut) (readOut := readOut)
                                          hreadCodeSolmNE hcallReadSolm
                                      have hbody := bodyRevertFromPip
                                        (tailPipFromParTail htailRead)
                                      exact
                                        (endCageIlkX_readCallFailed
                                          (rdata := readOut) rd9445Fail hreadOutSize)
                                          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                                    · let evmReadSolm :=
                                        { evmParSolm with
                                          accountMap := σ_read_solm
                                          substate := A_read_solm
                                          createdAccounts := cA_read }
                                      let evmReadEvm :=
                                        { evmParEvm with
                                          accountMap := σ_read
                                          substate := ARead
                                          createdAccounts := cA_read }
                                      have hStateRead :
                                          EVMStateEquiv evmReadEvm evmReadSolm := by
                                        refine ⟨?_, ?_, ?_⟩
                                        · simpa [evmReadEvm, evmReadSolm] using
                                            hStatePar.executionEnv
                                        · simp [evmReadEvm, evmReadSolm]
                                        · simpa [evmReadEvm, evmReadSolm] using
                                            hAccountsRead
                                      have rd9445Ok := rd9445
                                      simp only [if_true] at rd9445Ok
                                      obtain ⟨_, _, rd9463⟩ :=
                                        endCageIlkX_readCallSucceeded
                                          (g := Sat256.ofUInt256 g) (rdata := readOut)
                                          rd9445Ok
                                      by_cases hshortRead : readOut.size < 32
                                      · have htailRead :=
                                          endCageIlkTailAfterParReverts_readDecodeShort
                                            (evmPar := evmParSolm) (evmRead := evmReadSolm)
                                            (I := I) (vatOut := vatOut) (spotOut := spotOut)
                                            (parOut := parOut) (readOut := readOut)
                                            hreadCodeSolmNE
                                            (by simpa [evmReadSolm] using hcallReadSolm)
                                            hshortRead
                                        have hbody := bodyRevertFromPip
                                          (tailPipFromParTail htailRead)
                                        exact
                                          (endCageIlkX_readReturnDecodeShort hloVat
                                            hspotOutSize hparOutSize rd9463 hshortRead
                                            hreadOutSize)
                                            |>.reEquivExecutionRevert hcode hdispatch hdecode
                                              hbody
                                      · have hloRead : 32 ≤ readOut.size :=
                                          Nat.le_of_not_gt hshortRead
                                        obtain ⟨_, _, rd9486⟩ :=
                                          endCageIlkX_readReturnDecodeOk hloVat hspotOutSize
                                            hparOutSize rd9463 hloRead hreadOutSize
                                        by_cases hoverMul :
                                            UInt256.size ≤
                                              (endCageIlkReturnWord parOut).toNat *
                                                endWadWord.toNat
                                        · have htailWdiv :=
                                            endCageIlkTailReverts_wdivMulOverflow
                                              evmReadSolm I vatOut spotOut parOut readOut
                                              hloRead hoverMul
                                          have htailRead :=
                                            endCageIlkTailAfterParReadOk
                                              (evmPar := evmParSolm) (evmRead := evmReadSolm)
                                              (I := I) (vatOut := vatOut) (spotOut := spotOut)
                                              (parOut := parOut) (readOut := readOut)
                                              hreadCodeSolmNE
                                              (by simpa [evmReadSolm] using hcallReadSolm)
                                              hloRead htailWdiv
                                          have hbody := bodyRevertFromPip
                                            (tailPipFromParTail htailRead)
                                          exact
                                            (endCageIlkX_wdivMulOverflow
                                              (vatOut := vatOut) hoverMul rd9486)
                                              |>.reEquivExecutionRevert hcode hdispatch hdecode
                                                hbody
                                        · have hfitMul :
                                            (endCageIlkReturnWord parOut).toNat *
                                                endWadWord.toNat <
                                              UInt256.size :=
                                            Nat.lt_of_not_ge hoverMul
                                          by_cases hy :
                                              endCageIlkReturnWord readOut = ⟨0⟩
                                          · have htailWdiv :=
                                              endCageIlkTailReverts_wdivDivZero
                                                evmReadSolm I vatOut spotOut parOut readOut
                                                hloRead hfitMul hy
                                            have htailRead :=
                                              endCageIlkTailAfterParReadOk
                                                (evmPar := evmParSolm)
                                                (evmRead := evmReadSolm) (I := I)
                                                (vatOut := vatOut) (spotOut := spotOut)
                                                (parOut := parOut) (readOut := readOut)
                                                hreadCodeSolmNE
                                                (by simpa [evmReadSolm] using hcallReadSolm)
                                                hloRead htailWdiv
                                            have hbody := bodyRevertFromPip
                                              (tailPipFromParTail htailRead)
                                            have hinvalidOr :=
                                              endCageIlkX_wdivDivZeroInvalid
                                                (g := Sat256.ofUInt256 g) (vatOut := vatOut)
                                                hfitMul hy rd9486
                                            rcases hinvalidOr with hoog | hinvalid
                                            · exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by
                                                rw [← hcode] at hoog
                                                simpa [initState, Sat256.ofUInt256] using hoog))
                                            · have hxi :
                                                  Ξ cA gh bl σ_evm σ₀ g A I =
                                                    .error .InvalidInstruction :=
                                                Xi_error_of_X (g := g) (by
                                                  rw [← hcode] at hinvalid
                                                  simpa [initState, Sat256.ofUInt256] using
                                                    hinvalid)
                                              exact reEquiv_execution hdispatch hdecode hbody
                                                (execResultsEquiv.invalidHalt hxi rfl)
                                          · have htailWdiv :=
                                              endCageIlkTailReturns evmReadSolm I vatOut
                                                spotOut parOut readOut hsz36 hloRead hfitMul hy
                                            have htailRead :=
                                              endCageIlkTailAfterParReadOk
                                                (evmPar := evmParSolm)
                                                (evmRead := evmReadSolm) (I := I)
                                                (vatOut := vatOut) (spotOut := spotOut)
                                                (parOut := parOut) (readOut := readOut)
                                                hreadCodeSolmNE
                                                (by simpa [evmReadSolm] using hcallReadSolm)
                                                hloRead htailWdiv
                                            have htailPip := tailPipFromParTail htailRead
                                            have hbody := bodyReturnFromPip htailPip
                                            obtain ⟨_, _, rd9490⟩ :=
                                              endCageIlkX_wdivReturns
                                                (vatOut := vatOut) hfitMul hy rd9486
                                            have hret :=
                                              endCageIlkX_finish
                                                (g := Sat256.ofUInt256 g) hperm hsz36
                                                hloVat hspotOutSize hparOutSize hreadOutSize
                                                rd9490
                                            have hStatePost :
                                                EVMStateEquiv
                                                  (endCageIlkPostTagState evmReadEvm I
                                                    (endCageIlkTagVWord parOut readOut))
                                                  (endCageIlkPostTagState evmReadSolm I
                                                    (endCageIlkTagVWord parOut readOut)) := by
                                              simpa [endCageIlkPostTagState] using
                                                hStateRead.storageStore_codeOwner
                                                  (endCageIlkTagSlot I)
                                                  (val₁ :=
                                                    endCageIlkTagVWord parOut readOut)
                                                  (val₂ :=
                                                    endCageIlkTagVWord parOut readOut) rfl
                                            exact hret.reEquivExecutionGenEVMStateEquiv
                                              (evm'_evm :=
                                                endCageIlkPostTagState evmReadEvm I
                                                  (endCageIlkTagVWord parOut readOut))
                                              (evm'_solm :=
                                                endCageIlkPostTagState evmReadSolm I
                                                  (endCageIlkTagVWord parOut readOut))
                                              hcode hdispatch hdecode hbody
                                              (by
                                                simp [evmReadEvm, endCageIlkPostTagState,
                                                  storageStore_createdAccounts])
                                              (by
                                                simpa [evmReadEvm, endCageIlkPostTagState,
                                                  evmParEvm, evmSpotEvm, evmArtEvm,
                                                  evmVatEvm, endCageIlkPostArtState,
                                                  initState, storageStore_executionEnv,
                                                  storageStore_accountMap,
                                                  endCageIlkPostTagAccountMap] using
                                                  accountMapEquiv.refl
                                                    (endCageIlkPostTagAccountMap σ_read I
                                                      (endCageIlkTagVWord parOut readOut)))
                                              hStatePost
                                              (by
                                                simpa [cageIlkTransition] using
                                                  (returnEquiv.fallthrough
                                                    (o := ByteArray.empty) (r := none)
                                                    (t := []) (dvs := []) rfl
                                                    (by native_decide) (by native_decide)))
                                  · rw [not_lt] at hdepthLtRead
                                    have hdepthEqRead : I.depth = 1024 :=
                                      Fin.ext (by have := I.depth.isLt; omega)
                                    obtain ⟨_, _, rd9445⟩ :=
                                      endCageIlkX_readStaticcallDepthLimit
                                        (g := Sat256.ofUInt256 g) hreadReady hdepthEqRead
                                    let readTargetSolm :=
                                      EVM.address (endCageIlkSpotIlkPipAddr spotOut)
                                    let A_read :=
                                      (evmParSolm.addAccessedAccount readTargetSolm).substate
                                    have hcallReadSolm :
                                        typedCallViaEVM config evmParSolm readTargetSolm
                                          "read" 0 []
                                          (false, { evmParSolm with substate := A_read },
                                            ByteArray.empty) false := by
                                      simpa [readTargetSolm, A_read, evmParSolm] using
                                        (callNotMade_depthLimit (cfg := config)
                                          (evm := evmParSolm) (tgt := readTargetSolm)
                                          (name := "read") (args := []) (callPerm := false)
                                          (endCageIlkReadEncode_eq I vatOut spotOut parOut
                                            hloVat hspotOutSize hparOutSize)
                                          (by
                                            simpa [evmParSolm, evmSpotSolm, evmArtSolm,
                                              evmVatSolm, evmSolm, endCageIlkPostArtState,
                                              initState, storageStore_executionEnv] using
                                              hdepthEqRead))
                                    have htailRead :=
                                      endCageIlkTailAfterParReverts_readFailure
                                        (evmPar := evmParSolm)
                                        (evmRead := { evmParSolm with substate := A_read })
                                        (I := I) (vatOut := vatOut) (spotOut := spotOut)
                                        (parOut := parOut) (readOut := ByteArray.empty)
                                        hreadCodeSolmNE
                                        (by simpa [readTargetSolm, A_read] using
                                          hcallReadSolm)
                                    have hbody := bodyRevertFromPip
                                      (tailPipFromParTail htailRead)
                                    exact
                                      (endCageIlkX_readCallFailed
                                        (rdata := ByteArray.empty) rd9445 (by native_decide))
                                        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                          · rw [not_lt] at hdepthLtPar
                            have hdepthEqPar : I.depth = 1024 :=
                              Fin.ext (by have := I.depth.isLt; omega)
                            obtain ⟨_, _, rd9337⟩ :=
                              endCageIlkX_parStaticcallDepthLimit
                                (g := Sat256.ofUInt256 g) hparReady hdepthEqPar
                            let parTargetSolm :=
                              EVM.address
                                (AccountAddress.ofNat
                                  (endCageIlkSpotWord evmSpotSolm.accountMap
                                    evmSpotSolm.executionEnv).toNat)
                            let A_par :=
                              (evmSpotSolm.addAccessedAccount parTargetSolm).substate
                            have hcallParSolm :
                                typedCallViaEVM config evmSpotSolm parTargetSolm "par" 0 []
                                  (false, { evmSpotSolm with substate := A_par },
                                    ByteArray.empty) false := by
                              simpa [parTargetSolm, A_par, evmSpotSolm] using
                                (callNotMade_depthLimit (cfg := config) (evm := evmSpotSolm)
                                  (tgt := parTargetSolm) (name := "par") (args := [])
                                  (callPerm := false)
                                  (endCageIlkParEncode_eq I vatOut spotOut hloVat hspotOutSize)
                                  (by
                                    simpa [evmSpotSolm, evmArtSolm, evmVatSolm, evmSolm,
                                      endCageIlkPostArtState, initState,
                                      storageStore_executionEnv] using hdepthEqPar))
                            have htailPip :=
                              endCageIlkTailAfterSpotReverts_parFailure
                                (evmSpot := evmSpotSolm)
                                (evmPar := { evmSpotSolm with substate := A_par })
                                (I := I) (vatOut := vatOut) (spotOut := spotOut)
                                (parOut := ByteArray.empty) hparCodeSolmNE hcallParSolm
                            have htail :
                                ExecBlock config
                                  { contract := contract, locals := endCageIlkStoreVatIlk I vatOut }
                                  evmVatSolm
                                  ([ .assign .storage (ArtRef (.var "ilk"))
                                      (.tupleGet (.var "vatIlk") 0) ] ++
                                  checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0)
                                    [.var "ilk"] "spotIlk" (perm := false) ++
                                  [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
                                  checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) []
                                    "parV" (perm := false) ++
                                  checkedExternalCallStmts (.var "pip") "read" (.intLit 0) []
                                    "pipRead" (perm := false) ++
                                  [ .internalCall "wdiv"
                                      [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
                                    .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
                                  .reverted := by
                              simpa [evmSpotSolm, evmArtSolm] using
                                endCageIlkTailFromVatSpotOk
                                  (evmVat := evmVatSolm) (evmSpot := evmSpotSolm)
                                  (I := I) (vatOut := vatOut) (spotOut := spotOut)
                                  hsz36 hspotCodeSolmNE
                                  (by simpa [evmSpotSolm, evmArtSolm] using hcallSpotSolm)
                                  hloSpot htailPip
                            have hbody :
                                ExecTransitionBody config contract evmSolm (endCageIlkStore I)
                                  cageIlkTransition.body .reverted := by
                              simpa [evmVatSolm, evmSolm] using
                                endCageIlkBodyReverts_vatIlksOkTailReverted
                                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                                  (A := A) (I := I) (g := g)
                                  (evmVat := evmVatSolm) (vatOut := vatOut)
                                  hwv hsz36 hliveSolm htagSolm hvatCodeSolmNE
                                  (by simpa [evmVatSolm, evmSolm] using hcallSolm)
                                  hloVat htail
                            exact (endCageIlkX_parCallFailed
                              (rdata := ByteArray.empty) rd9337 (by native_decide))
                              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                  · rw [not_lt] at hdepthLtSpot
                    have hdepthEqSpot : I.depth = 1024 :=
                      Fin.ext (by have := I.depth.isLt; omega)
                    obtain ⟨_, _, rd9217⟩ :=
                      endCageIlkX_spotIlksStaticcallDepthLimit
                        (g := Sat256.ofUInt256 g) hspotReady hdepthEqSpot
                    let spotTargetSolm :=
                      EVM.address
                        (AccountAddress.ofNat
                          (endCageIlkSpotWord evmArtSolm.accountMap
                            evmArtSolm.executionEnv).toNat)
                    let A_spot :=
                      (evmArtSolm.addAccessedAccount spotTargetSolm).substate
                    have hcallSpotSolm :
                        typedCallViaEVM config evmArtSolm spotTargetSolm "spotIlks" 0
                          [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
                          (false, { evmArtSolm with substate := A_spot }, ByteArray.empty)
                          false := by
                      simpa [spotTargetSolm, A_spot, evmArtSolm, endCageIlkPostArtState,
                        storageStore_executionEnv] using
                        (callNotMade_depthLimit (cfg := config) (evm := evmArtSolm)
                          (tgt := spotTargetSolm) (name := "spotIlks")
                          (args := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
                          (callPerm := false)
                          (endCageIlkSpotIlksEncode_eq I vatOut hsz36 hloVat)
                          (by
                            simpa [evmArtSolm, evmVatSolm, evmSolm, endCageIlkPostArtState,
                              initState, storageStore_executionEnv] using hdepthEqSpot))
                    have htail :
                        ExecBlock config
                          { contract := contract, locals := endCageIlkStoreVatIlk I vatOut }
                          evmVatSolm
                          ([ .assign .storage (ArtRef (.var "ilk"))
                              (.tupleGet (.var "vatIlk") 0) ] ++
                          checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0)
                            [.var "ilk"] "spotIlk" (perm := false) ++
                          [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
                          checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) []
                            "parV" (perm := false) ++
                          checkedExternalCallStmts (.var "pip") "read" (.intLit 0) []
                            "pipRead" (perm := false) ++
                          [ .internalCall "wdiv"
                              [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
                            .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
                          .reverted := by
                      simpa [spotTargetSolm, A_spot, evmArtSolm] using
                        endCageIlkTailFromVatReverts_spotFailure
                          (evmVat := evmVatSolm)
                          (evmSpot := { evmArtSolm with substate := A_spot })
                          (I := I) (vatOut := vatOut) (spotOut := ByteArray.empty)
                          hsz36 hspotCodeSolmNE hcallSpotSolm
                    have hbody :
                        ExecTransitionBody config contract evmSolm (endCageIlkStore I)
                          cageIlkTransition.body .reverted := by
                      simpa [evmVatSolm, evmSolm] using
                        endCageIlkBodyReverts_vatIlksOkTailReverted
                          (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                          (A := A) (I := I) (g := g)
                          (evmVat := evmVatSolm) (vatOut := vatOut)
                          hwv hsz36 hliveSolm htagSolm hvatCodeSolmNE
                          (by simpa [evmVatSolm, evmSolm] using hcallSolm)
                          hloVat htail
                    exact (endCageIlkX_spotIlksCallFailed
                      (vatOut := vatOut) (rdata := ByteArray.empty) rd9217 (by native_decide))
                      |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · rw [not_lt] at hdepthLt
            have hdepthEq : I.depth = 1024 :=
              Fin.ext (by have := I.depth.isLt; omega)
            obtain ⟨_, _, rd9081⟩ :=
              endCageIlkX_vatIlksCallDepthLimit
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
                  (endFlowVatIlksEncode_eq I hsz36
                    (twoWordHashMem_size_96 (endCageIlkIlkWord I) ⟨12⟩
                      solcFreePtrMem_size))
                  (by simpa [evmSolm, initState] using hdepthEq))
            have hbody :
                ExecTransitionBody config contract evmSolm (endCageIlkStore I)
                  cageIlkTransition.body .reverted := by
              simpa [evmSolm, A_vat] using
                endCageIlkBodyReverts_vatIlksCallFailed
                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                  (A := A) (I := I) (g := g)
                  (evmVat := { evmSolm with substate := A_vat })
                  (out := ByteArray.empty)
                  hwv hsz36 hliveSolm htagSolm hvatCodeSolmNE hcallSolm
            exact (endCageIlkX_vatIlksCallFailed rd9081 (by native_decide))
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have htagSolm : endCageIlkTagWord σ_solm I ≠ ⟨0⟩ := by
          intro hbad
          exact htag (by rw [htagCouple, hbad])
        have hbody :
            ExecTransitionBody config contract evmSolm (endCageIlkStore I)
              cageIlkTransition.body .reverted := by
          simpa [evmSolm] using
            endCageIlkBodyReverts_tagNonzero
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
              (A := A) (I := I) (g := g) hwv hsz36 hliveSolm htagSolm
        exact (endCageIlkX_tagNonzero (g := Sat256.ofUInt256 g) hsz36 hlive htag hbodyReach)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hliveSolm : endCageIlkLiveWord σ_solm I ≠ ⟨0⟩ := by
        intro hbad
        exact hlive (by rw [hliveCouple, hbad])
      have hbody :
          ExecTransitionBody config contract evmSolm (endCageIlkStore I)
            cageIlkTransition.body .reverted := by
        simpa [evmSolm] using
          endCageIlkBodyReverts_liveNonzero
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hwv hliveSolm
      exact (endCageIlkX_liveNonzero (g := Sat256.ofUInt256 g) hlive hbodyReach)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · exact endCageIlkBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.End
