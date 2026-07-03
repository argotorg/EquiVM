import Examples.BytesStoreLite.FullPushChunkCalldataWords
import Examples.BytesStoreLite.StorageLoopFacts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace BytesStoreLite

theorem bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    {cA gh bl σinit τ σ₀ A I} {g : Sat256}
    {header ret : UInt256} {rest : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) mem aw rdata (cA, τ) k C)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hret : (D_J bytesStoreLiteBytecode 0).contains ret = true)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ret
      (UInt256.div header ⟨2⟩ :: rest)
      mem aw rdata (cA, τ) k C := by
  obtain ⟨_, _, rd2246⟩ := hreach
  have rd2259 := evm_run rd2246 with [
    jumpdest, push1 ⟨1⟩, dup2, dup2, shr, swap1, dup3, and, dup1, push2 ⟨2266⟩]
  have rd2266 := rd2259.jumpiT (by native_decide) hflag (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2288 := evm_run rd2266 with [
    jumpdest, push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨2296⟩]
  rw [bytesStoreLite_shiftRight_one_eq_div_two] at rd2288
  have rd2296 := rd2288.jumpiT (by native_decide) hvalid (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd2296 with [
    jumpdest, pop, swap2, swap1, pop, raw jump (by native_decide) hret
      (by simp only [List.length_cons]; omega)]⟩

theorem bytesStoreLiteLongDataWordsLoopStride_zero_ofNat :
    ∀ i, BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) i =
      UInt256.ofNat (32 * i)
  | 0 => rfl
  | i + 1 => by
      simp [BytesStoreLiteCore.longDataWordsLoopStride,
        bytesStoreLiteLongDataWordsLoopStride_zero_ofNat i,
        BytesStoreLiteCore.u256_32_add_ofNat]
      congr 1

theorem bytesStoreLitePushChunkLongPushArray_of_post_header {evm : EVM.State}
    (oldLen header oldBytesLen : UInt256) (value : ByteArray)
    (hvalueSize : ¬ value.size < 32)
    (hloadLen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = oldLen)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
        evm.executionEnv.codeOwner
        (chunksDataBase + oldLen) = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : oldBytesLen = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid :
      UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt oldBytesLen ⟨32⟩) ≠ ⟨0⟩) :
    pushArray? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract,
        locals := (∅ : Store).insert "value" (.bytes value) }
      evm chunksRef (some (.bytes value)) =
      .ok (Solm.EVM.storageStore
        (writeSolidityBytesDataWordsFrom
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
          (chunksDataBase + oldLen) value 0 (solidityBytesDataWordCount value.size))
        evm.executionEnv.codeOwner (chunksDataBase + oldLen)
        (solidityBytesHeaderWord value.size)) := by
  let evmLen :=
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩)
  have hloadLoc :
      storageLocLoad evm (uint256Loc ⟨1⟩) = .int (Int.ofNat oldLen.toNat) := by
    rw [bytesStoreLiteStorageLocLoad_uint256, hloadLen]
  have hstoreLen :
      storageLocStore evm (uint256Loc ⟨1⟩) (.int (Int.ofNat oldLen.toNat + 1)) =
        some evmLen := by
    simpa [evmLen] using bytesStoreLiteStorageLocStore_uint256_addOne evm ⟨1⟩ oldLen
  have hpackedLen : checkBytesPacked (chunksDataBase + oldLen) evmLen = true :=
    checkBytesPacked_of_storageLoad_land_one_zero
      (by simpa [evmLen, storageStore_executionEnv] using hloadElemLen) hflag
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmLen
        { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
        .bytes (.bytes value) =
        .ok (Solm.EVM.storageStore
          (writeSolidityBytesDataWordsFrom evmLen (chunksDataBase + oldLen) value 0
            (solidityBytesDataWordCount value.size))
          (writeSolidityBytesDataWordsFrom evmLen (chunksDataBase + oldLen) value 0
            (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
          (chunksDataBase + oldLen) (solidityBytesHeaderWord value.size)) := by
    exact bytesStoreLiteWriteChunkLongPacked (evm := evmLen)
      oldLen header oldBytesLen value hvalueSize
      (by simpa [evmLen, storageStore_executionEnv] using hloadElemLen)
      hpackedLen hflag hlen hvalid
  rw [pushArray?, bytesStoreLiteChunksResolveValue evm value]
  simp only [bytesStoreLiteConfig, bytesStoreLiteStorageLayout, solidityStorageLayout,
    bytesStoreLiteLayout, EvalResult.ofOption, EvalResult.bind, bind]
  simp only [List.nil_append]
  rw [hloadLoc]
  simp only
  rw [hstoreLen]
  change writeStorage? bytesStoreLiteConfig evmLen
      { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
      .bytes (.bytes value) =
    .ok (Solm.EVM.storageStore
      (writeSolidityBytesDataWordsFrom evmLen (chunksDataBase + oldLen) value 0
        (solidityBytesDataWordCount value.size))
      evm.executionEnv.codeOwner (chunksDataBase + oldLen)
      (solidityBytesHeaderWord value.size))
  rw [hwrite]
  simp [evmLen, storageStore_executionEnv,
    writeSolidityBytesDataWordsFrom_executionEnv]

theorem bytesStoreLitePushChunkLongPushArray_of_ne {evm : EVM.State}
    (oldLen header oldBytesLen : UInt256) (value : ByteArray)
    (hne : chunksDataBase + oldLen ≠ (⟨1⟩ : UInt256))
    (hvalueSize : ¬ value.size < 32)
    (hloadLen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = oldLen)
    (hloadElem :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (chunksDataBase + oldLen) = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : oldBytesLen = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid :
      UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt oldBytesLen ⟨32⟩) ≠ ⟨0⟩) :
    pushArray? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract,
        locals := (∅ : Store).insert "value" (.bytes value) }
      evm chunksRef (some (.bytes value)) =
      .ok (Solm.EVM.storageStore
        (writeSolidityBytesDataWordsFrom
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
          (chunksDataBase + oldLen) value 0 (solidityBytesDataWordCount value.size))
        evm.executionEnv.codeOwner (chunksDataBase + oldLen)
        (solidityBytesHeaderWord value.size)) := by
  exact bytesStoreLitePushChunkLongPushArray_of_post_header (evm := evm)
    oldLen header oldBytesLen value hvalueSize hloadLen
    (bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evm) oldLen header hne hloadElem)
    hflag hlen hvalid

theorem bytesStoreLitePushChunkLongOldLongPushArray_of_post_header {evm : EVM.State}
    (oldLen header oldBytesLen : UInt256) (value : ByteArray)
    (hvalueSize : ¬ value.size < 32)
    (hloadLen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = oldLen)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
        evm.executionEnv.codeOwner
        (chunksDataBase + oldLen) = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : oldBytesLen = UInt256.div header ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt oldBytesLen ⟨32⟩) ≠ ⟨0⟩) :
    pushArray? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract,
        locals := (∅ : Store).insert "value" (.bytes value) }
      evm chunksRef (some (.bytes value)) =
      .ok (Solm.EVM.storageStore
        (writeSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom
            (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
            (chunksDataBase + oldLen)
            (solidityBytesDataWordCount value.size)
            (solidityBytesDataWordCount oldBytesLen.toNat -
              solidityBytesDataWordCount value.size))
          (chunksDataBase + oldLen) value 0 (solidityBytesDataWordCount value.size))
        (writeSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom
            (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
            (chunksDataBase + oldLen)
            (solidityBytesDataWordCount value.size)
            (solidityBytesDataWordCount oldBytesLen.toNat -
              solidityBytesDataWordCount value.size))
          (chunksDataBase + oldLen) value 0
          (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
        (chunksDataBase + oldLen) (solidityBytesHeaderWord value.size)) := by
  let evmLen :=
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩)
  have hloadLoc :
      storageLocLoad evm (uint256Loc ⟨1⟩) = .int (Int.ofNat oldLen.toNat) := by
    rw [bytesStoreLiteStorageLocLoad_uint256, hloadLen]
  have hstoreLen :
      storageLocStore evm (uint256Loc ⟨1⟩) (.int (Int.ofNat oldLen.toNat + 1)) =
        some evmLen := by
    simpa [evmLen] using bytesStoreLiteStorageLocStore_uint256_addOne evm ⟨1⟩ oldLen
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmLen
        { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
        .bytes (.bytes value) =
        .ok (Solm.EVM.storageStore
          (writeSolidityBytesDataWordsFrom
            (clearSolidityBytesDataWordsFrom evmLen (chunksDataBase + oldLen)
              (solidityBytesDataWordCount value.size)
              (solidityBytesDataWordCount oldBytesLen.toNat -
                solidityBytesDataWordCount value.size))
            (chunksDataBase + oldLen) value 0 (solidityBytesDataWordCount value.size))
          (writeSolidityBytesDataWordsFrom
            (clearSolidityBytesDataWordsFrom evmLen (chunksDataBase + oldLen)
              (solidityBytesDataWordCount value.size)
              (solidityBytesDataWordCount oldBytesLen.toNat -
                solidityBytesDataWordCount value.size))
            (chunksDataBase + oldLen) value 0
            (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
          (chunksDataBase + oldLen) (solidityBytesHeaderWord value.size)) := by
    exact bytesStoreLiteWriteChunkLongFromLongPrepared (evm := evmLen)
      oldLen header oldBytesLen value hvalueSize
      (by simpa [evmLen, storageStore_executionEnv] using hloadElemLen) hflag hlen hvalid
  rw [pushArray?, bytesStoreLiteChunksResolveValue evm value]
  simp only [bytesStoreLiteConfig, bytesStoreLiteStorageLayout, solidityStorageLayout,
    bytesStoreLiteLayout, EvalResult.ofOption, EvalResult.bind, bind]
  simp only [List.nil_append]
  rw [hloadLoc]
  simp only
  rw [hstoreLen]
  change writeStorage? bytesStoreLiteConfig evmLen
      { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
      .bytes (.bytes value) =
    .ok (Solm.EVM.storageStore
      (writeSolidityBytesDataWordsFrom
        (clearSolidityBytesDataWordsFrom evmLen (chunksDataBase + oldLen)
          (solidityBytesDataWordCount value.size)
          (solidityBytesDataWordCount oldBytesLen.toNat -
            solidityBytesDataWordCount value.size))
        (chunksDataBase + oldLen) value 0 (solidityBytesDataWordCount value.size))
      (writeSolidityBytesDataWordsFrom
        (clearSolidityBytesDataWordsFrom evmLen (chunksDataBase + oldLen)
          (solidityBytesDataWordCount value.size)
          (solidityBytesDataWordCount oldBytesLen.toNat -
            solidityBytesDataWordCount value.size))
        (chunksDataBase + oldLen) value 0
        (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
      (chunksDataBase + oldLen)
      (solidityBytesHeaderWord value.size))
  rw [hwrite]

theorem bytesStoreLitePushChunkLongOldLongPushArray_of_ne {evm : EVM.State}
    (oldLen header oldBytesLen : UInt256) (value : ByteArray)
    (hne : chunksDataBase + oldLen ≠ (⟨1⟩ : UInt256))
    (hvalueSize : ¬ value.size < 32)
    (hloadLen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = oldLen)
    (hloadElem :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (chunksDataBase + oldLen) = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : oldBytesLen = UInt256.div header ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt oldBytesLen ⟨32⟩) ≠ ⟨0⟩) :
    pushArray? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract,
        locals := (∅ : Store).insert "value" (.bytes value) }
      evm chunksRef (some (.bytes value)) =
      .ok (Solm.EVM.storageStore
        (writeSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom
            (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
            (chunksDataBase + oldLen)
            (solidityBytesDataWordCount value.size)
            (solidityBytesDataWordCount oldBytesLen.toNat -
              solidityBytesDataWordCount value.size))
          (chunksDataBase + oldLen) value 0 (solidityBytesDataWordCount value.size))
        (writeSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom
            (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
            (chunksDataBase + oldLen)
            (solidityBytesDataWordCount value.size)
            (solidityBytesDataWordCount oldBytesLen.toNat -
              solidityBytesDataWordCount value.size))
          (chunksDataBase + oldLen) value 0
          (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
        (chunksDataBase + oldLen) (solidityBytesHeaderWord value.size)) := by
  exact bytesStoreLitePushChunkLongOldLongPushArray_of_post_header (evm := evm)
    oldLen header oldBytesLen value hvalueSize hloadLen
    (bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evm) oldLen header hne hloadElem)
    hflag hlen hvalid

theorem bytesStoreLitePushChunkShortOldLongPushArray_of_post_header {evm : EVM.State}
    (oldLen header oldBytesLen : UInt256) (value : ByteArray)
    (hvalueSize : value.size < 32)
    (hloadLen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = oldLen)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
        evm.executionEnv.codeOwner
        (chunksDataBase + oldLen) = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : oldBytesLen = UInt256.div header ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt oldBytesLen ⟨32⟩) ≠ ⟨0⟩) :
    pushArray? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract,
        locals := (∅ : Store).insert "value" (.bytes value) }
      evm chunksRef (some (.bytes value)) =
      .ok (Solm.EVM.storageStore
        (clearSolidityBytesDataWordsFrom
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
          (chunksDataBase + oldLen) 0 ((oldBytesLen.toNat + 31) / 32))
        (clearSolidityBytesDataWordsFrom
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
          (chunksDataBase + oldLen) 0 ((oldBytesLen.toNat + 31) / 32)).executionEnv.codeOwner
        (chunksDataBase + oldLen) (solidityShortBytesWord value)) := by
  let evmLen :=
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩)
  have hloadLoc :
      storageLocLoad evm (uint256Loc ⟨1⟩) = .int (Int.ofNat oldLen.toNat) := by
    rw [bytesStoreLiteStorageLocLoad_uint256, hloadLen]
  have hstoreLen :
      storageLocStore evm (uint256Loc ⟨1⟩) (.int (Int.ofNat oldLen.toNat + 1)) =
        some evmLen := by
    simpa [evmLen] using bytesStoreLiteStorageLocStore_uint256_addOne evm ⟨1⟩ oldLen
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmLen
        { base := "chunks", steps := [.aindex (.int (Int.ofNat oldLen.toNat))] }
        .bytes (.bytes value) =
        .ok (Solm.EVM.storageStore
          (clearSolidityBytesDataWordsFrom evmLen (chunksDataBase + oldLen) 0
            ((oldBytesLen.toNat + 31) / 32))
          (clearSolidityBytesDataWordsFrom evmLen (chunksDataBase + oldLen) 0
            ((oldBytesLen.toNat + 31) / 32)).executionEnv.codeOwner
          (chunksDataBase + oldLen) (solidityShortBytesWord value)) := by
    exact bytesStoreLiteWriteChunkShortFromLongPrepared (evm := evmLen)
      oldLen header oldBytesLen value hvalueSize
      (by simpa [evmLen, storageStore_executionEnv] using hloadElemLen) hflag hlen hvalid
  rw [pushArray?, bytesStoreLiteChunksResolveValue evm value]
  simp only [bytesStoreLiteConfig, bytesStoreLiteStorageLayout, solidityStorageLayout,
    bytesStoreLiteLayout, EvalResult.ofOption, EvalResult.bind, bind]
  simp only [List.nil_append]
  rw [hloadLoc]
  simp only
  rw [hstoreLen]
  simpa [evmLen, storageStore_executionEnv, clearSolidityBytesDataWordsFrom_executionEnv]
    using hwrite

theorem bytesStoreLitePushChunkShortOldLongPushArray_of_ne {evm : EVM.State}
    (oldLen header oldBytesLen : UInt256) (value : ByteArray)
    (hne : chunksDataBase + oldLen ≠ (⟨1⟩ : UInt256))
    (hvalueSize : value.size < 32)
    (hloadLen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = oldLen)
    (hloadElem :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (chunksDataBase + oldLen) = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : oldBytesLen = UInt256.div header ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt oldBytesLen ⟨32⟩) ≠ ⟨0⟩) :
    pushArray? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract,
        locals := (∅ : Store).insert "value" (.bytes value) }
      evm chunksRef (some (.bytes value)) =
      .ok (Solm.EVM.storageStore
        (clearSolidityBytesDataWordsFrom
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
          (chunksDataBase + oldLen) 0 ((oldBytesLen.toNat + 31) / 32))
        (clearSolidityBytesDataWordsFrom
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
          (chunksDataBase + oldLen) 0 ((oldBytesLen.toNat + 31) / 32)).executionEnv.codeOwner
        (chunksDataBase + oldLen) (solidityShortBytesWord value)) := by
  exact bytesStoreLitePushChunkShortOldLongPushArray_of_post_header (evm := evm)
    oldLen header oldBytesLen value hvalueSize hloadLen
    (bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evm) oldLen header hne hloadElem)
    hflag hlen hvalid

theorem accountMapEquiv_clearDataWordsForwardFrom_shift_bytesLikeBase
    {owner : AccountAddress} {σ τ : AccountMap} (baseSlot : UInt256) :
    ∀ (offset : Nat) (idx : UInt256) (fuel : Nat),
      accountMapEquiv σ τ →
      accountMapEquiv
        (clearDataWordsForwardFrom owner σ
          (bytesLikeDataBase baseSlot + UInt256.ofNat offset) idx fuel)
        (clearDataWordsForwardFrom owner τ
          (bytesLikeDataBase baseSlot) (UInt256.ofNat offset + idx) fuel)
  | offset, idx, 0, hAccounts => by
      simpa [clearDataWordsForwardFrom] using hAccounts
  | offset, idx, fuel + 1, hAccounts => by
      simp [clearDataWordsForwardFrom]
      have hslot :
          (bytesLikeDataBase baseSlot + UInt256.ofNat offset) + idx =
            bytesLikeDataBase baseSlot + (UInt256.ofNat offset + idx) := by
        exact u256_add_assoc (bytesLikeDataBase baseSlot) (UInt256.ofNat offset) idx
      have hstep := accountMapEquiv_sstoreAccountMap owner
        (bytesLikeDataBase baseSlot + (UInt256.ofNat offset + idx)) (⟨0⟩ : UInt256)
        hAccounts
      have htail := accountMapEquiv_clearDataWordsForwardFrom_shift_bytesLikeBase
        (owner := owner) (σ := sstoreAccountMap owner σ
          ((bytesLikeDataBase baseSlot + UInt256.ofNat offset) + idx) ⟨0⟩)
        (τ := sstoreAccountMap owner τ
          (bytesLikeDataBase baseSlot + (UInt256.ofNat offset + idx)) ⟨0⟩)
        baseSlot offset ((⟨1⟩ : UInt256) + idx) fuel
        (by simpa [hslot] using hstep)
      have hidx :
          UInt256.ofNat offset + ((⟨1⟩ : UInt256) + idx) =
            (⟨1⟩ : UInt256) + (UInt256.ofNat offset + idx) := by
        rw [u256_add_comm (UInt256.ofNat offset) ((⟨1⟩ : UInt256) + idx)]
        rw [u256_add_assoc]
        rw [u256_add_comm idx (UInt256.ofNat offset)]
      simpa [hidx] using htail

theorem accountMapEquiv_pushChunkLongNoTailStorageFromLen
    {I : ExecutionEnv} {len payloadStart oldLen : UInt256}
    {σ_evm_len σ_solm_len : AccountMap}
    (hAccounts : accountMapEquiv σ_evm_len σ_solm_len)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (hsize : (BytesStoreLiteCore.setDecodedValueBytes I).size = len.toNat)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hmod : len.toNat % 32 = 0)
    (hheader :
      solidityBytesHeaderWord (BytesStoreLiteCore.setDecodedValueBytes I).size =
        len * (⟨2⟩ : UInt256) + ⟨1⟩) :
    let baseSlot : UInt256 := chunksDataBase + oldLen
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm_len
          (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32))
        baseSlot (len * (⟨2⟩ : UInt256) + ⟨1⟩))
      (sstoreAccountMap I.codeOwner
        (solidityDataWordsForwardFrom I.codeOwner σ_solm_len baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) 0
          (solidityBytesDataWordCount (BytesStoreLiteCore.setDecodedValueBytes I).size))
        baseSlot
        (solidityBytesHeaderWord (BytesStoreLiteCore.setDecodedValueBytes I).size)) := by
  dsimp only
  let baseSlot : UInt256 := chunksDataBase + oldLen
  have hdataFuelEq :
      solidityBytesDataWordCount (BytesStoreLiteCore.setDecodedValueBytes I).size =
        len.toNat / 32 := by
    unfold solidityBytesDataWordCount
    rw [hsize]
    have hdiv := Nat.div_add_mod len.toNat 32
    omega
  have hbridgeEvm :
      accountMapEquiv
        (solidityDataWordsForwardFrom I.codeOwner σ_evm_len baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) 0 (len.toNat / 32))
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm_len
          (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32)) := by
    exact accountMapEquiv_solidityDataWordsForwardFrom_calldataLongDataForwardFrom_full_zero
      (I := I) (len := len) (payloadStart := payloadStart) (owner := I.codeOwner)
      (baseSlot := baseSlot) hsrc haddrBound hsize hlenAbi hpayloadStart hoffMax
      (τ := σ_evm_len) (fuel := len.toNat / 32) (by omega)
  have hcong :
      accountMapEquiv
        (solidityDataWordsForwardFrom I.codeOwner σ_evm_len baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) 0 (len.toNat / 32))
        (solidityDataWordsForwardFrom I.codeOwner σ_solm_len baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) 0 (len.toNat / 32)) := by
    exact accountMapEquiv_solidityDataWordsForwardFrom
      (owner := I.codeOwner) (τ := σ_evm_len) (σ := σ_solm_len)
      (baseSlot := baseSlot) (bytes := BytesStoreLiteCore.setDecodedValueBytes I)
      (idx := 0) (len.toNat / 32) hAccounts
  have hdata :
      accountMapEquiv
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm_len
          (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
        (solidityDataWordsForwardFrom I.codeOwner σ_solm_len baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) 0 (len.toNat / 32)) :=
    accountMapEquiv.trans (accountMapEquiv.symm hbridgeEvm) hcong
  have hstored :=
    accountMapEquiv_sstoreAccountMap I.codeOwner baseSlot
      (len * (⟨2⟩ : UInt256) + ⟨1⟩) hdata
  simpa [baseSlot, hdataFuelEq, hheader] using hstored

theorem accountMapEquiv_pushChunkLongTailStorageFromLen
    {I : ExecutionEnv} {len payloadStart oldLen : UInt256}
    {σ_evm_len σ_solm_len : AccountMap}
    (hAccounts : accountMapEquiv σ_evm_len σ_solm_len)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (htailAddr :
      (payloadStart + UInt256.ofNat (32 * (len.toNat / 32))).toNat =
        payloadStart.toNat + 32 * (len.toNat / 32))
    (hsize : (BytesStoreLiteCore.setDecodedValueBytes I).size = len.toNat)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlong : ¬ len.toNat < 32)
    (hmod : len.toNat % 32 ≠ 0)
    (hheader :
      solidityBytesHeaderWord (BytesStoreLiteCore.setDecodedValueBytes I).size =
        len * (⟨2⟩ : UInt256) + ⟨1⟩) :
    let baseSlot : UInt256 := chunksDataBase + oldLen
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm_len
            (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase baseSlot)
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataTailMaskedWord
            (bytesStoreLiteCalldataLongDataWord I payloadStart
              (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
              0) len))
        baseSlot (len * (⟨2⟩ : UInt256) + ⟨1⟩))
      (sstoreAccountMap I.codeOwner
        (solidityDataWordsForwardFrom I.codeOwner σ_solm_len baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) 0
          (solidityBytesDataWordCount (BytesStoreLiteCore.setDecodedValueBytes I).size))
        baseSlot
        (solidityBytesHeaderWord (BytesStoreLiteCore.setDecodedValueBytes I).size)) := by
  dsimp only
  let baseSlot : UInt256 := chunksDataBase + oldLen
  let fullFuel : Nat := len.toNat / 32
  have hdataFuelEq :
      solidityBytesDataWordCount (BytesStoreLiteCore.setDecodedValueBytes I).size =
        fullFuel + 1 := by
    unfold solidityBytesDataWordCount
    dsimp [fullFuel]
    rw [hsize]
    have hdiv := Nat.div_add_mod len.toNat 32
    have hremLt := Nat.mod_lt len.toNat (by decide : 0 < 32)
    have hremPos : 0 < len.toNat % 32 := Nat.pos_of_ne_zero hmod
    omega
  have hbridgeEvm :
      accountMapEquiv
        (solidityDataWordsForwardFrom I.codeOwner σ_evm_len baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) 0 fullFuel)
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm_len
          (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fullFuel) := by
    exact accountMapEquiv_solidityDataWordsForwardFrom_calldataLongDataForwardFrom_full_zero
      (I := I) (len := len) (payloadStart := payloadStart) (owner := I.codeOwner)
      (baseSlot := baseSlot) hsrc haddrBound hsize hlenAbi hpayloadStart hoffMax
      (τ := σ_evm_len) (fuel := fullFuel) (by dsimp [fullFuel]; omega)
  have hcong :
      accountMapEquiv
        (solidityDataWordsForwardFrom I.codeOwner σ_evm_len baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) 0 fullFuel)
        (solidityDataWordsForwardFrom I.codeOwner σ_solm_len baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) 0 fullFuel) := by
    exact accountMapEquiv_solidityDataWordsForwardFrom
      (owner := I.codeOwner) (τ := σ_evm_len) (σ := σ_solm_len)
      (baseSlot := baseSlot) (bytes := BytesStoreLiteCore.setDecodedValueBytes I)
      (idx := 0) fullFuel hAccounts
  have hdataFull :
      accountMapEquiv
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm_len
          (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fullFuel)
        (solidityDataWordsForwardFrom I.codeOwner σ_solm_len baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) 0 fullFuel) :=
    accountMapEquiv.trans (accountMapEquiv.symm hbridgeEvm) hcong
  have htailWord :
      BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (UInt256.ofNat (32 * fullFuel)) 0) len =
        uInt256OfByteArray
          ((BytesStoreLiteCore.setDecodedValueBytes I).readWithPadding (fullFuel * 32) 32) := by
    simpa [fullFuel, Nat.mul_comm] using
      bytesStoreLiteCalldataLongDataTailMaskedWord_eq_decoded_tail
        (I := I) (len := len) (payloadStart := payloadStart)
        htailAddr hsrc hsize hlenAbi hpayloadStart hoffMax hlong hmod
  have hslotEq :
      BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase baseSlot) fullFuel =
        solidityBytesDataSlot baseSlot fullFuel := by
    exact bytesStoreLiteLongDataWordsLoopSlot_bytesLikeDataBase baseSlot fullFuel
  have htailStore :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm_len
            (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fullFuel)
          (BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase baseSlot) fullFuel)
          (BytesStoreLiteCore.longDataTailMaskedWord
            (bytesStoreLiteCalldataLongDataWord I payloadStart
              (UInt256.ofNat (32 * fullFuel)) 0) len))
        (solidityDataWordsForwardFrom I.codeOwner σ_solm_len baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) 0 (fullFuel + 1)) := by
    have hsplit :
        solidityDataWordsForwardFrom I.codeOwner σ_solm_len baseSlot
            (BytesStoreLiteCore.setDecodedValueBytes I) 0 (fullFuel + 1) =
          sstoreAccountMap I.codeOwner
            (solidityDataWordsForwardFrom I.codeOwner σ_solm_len baseSlot
              (BytesStoreLiteCore.setDecodedValueBytes I) 0 fullFuel)
            (solidityBytesDataSlot baseSlot fullFuel)
            (uInt256OfByteArray
              ((BytesStoreLiteCore.setDecodedValueBytes I).readWithPadding (fullFuel * 32) 32)) := by
      have happ := solidityDataWordsForwardFrom_append I.codeOwner σ_solm_len baseSlot
        (BytesStoreLiteCore.setDecodedValueBytes I) 0 fullFuel 1
      rw [happ]
      simp [solidityDataWordsForwardFrom]
    rw [hsplit]
    simpa [hslotEq, htailWord] using
      accountMapEquiv_sstoreAccountMap I.codeOwner
        (BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase baseSlot) fullFuel)
        (BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (UInt256.ofNat (32 * fullFuel)) 0) len)
        hdataFull
  have hstored :=
    accountMapEquiv_sstoreAccountMap I.codeOwner baseSlot
      (len * (⟨2⟩ : UInt256) + ⟨1⟩) htailStore
  simpa [baseSlot, fullFuel, hdataFuelEq, hheader,
    bytesStoreLiteLongDataWordsLoopStride_zero_ofNat] using hstored

theorem accountMapEquiv_pushChunkLongNoTailStorage
    {I : ExecutionEnv} {len payloadStart oldLen : UInt256}
    {σ_evm σ_solm : AccountMap}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (hsize : (BytesStoreLiteCore.setDecodedValueBytes I).size = len.toNat)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hmod : len.toNat % 32 = 0)
    (hheader :
      solidityBytesHeaderWord (BytesStoreLiteCore.setDecodedValueBytes I).size =
        len * (⟨2⟩ : UInt256) + ⟨1⟩) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner
          (sstoreAccountMap I.codeOwner σ_evm ⟨1⟩ (oldLen + ⟨1⟩))
          (bytesLikeDataBase (chunksDataBase + oldLen)) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32))
        (chunksDataBase + oldLen) (len * (⟨2⟩ : UInt256) + ⟨1⟩))
      (sstoreAccountMap I.codeOwner
        (solidityDataWordsForwardFrom I.codeOwner
          (sstoreAccountMap I.codeOwner σ_solm ⟨1⟩ (oldLen + ⟨1⟩))
          (chunksDataBase + oldLen) (BytesStoreLiteCore.setDecodedValueBytes I) 0
          (solidityBytesDataWordCount (BytesStoreLiteCore.setDecodedValueBytes I).size))
        (chunksDataBase + oldLen)
        (solidityBytesHeaderWord (BytesStoreLiteCore.setDecodedValueBytes I).size)) := by
  let lenSlotVal : UInt256 := oldLen + ⟨1⟩
  let baseSlot : UInt256 := chunksDataBase + oldLen
  let σ_evm_len := sstoreAccountMap I.codeOwner σ_evm ⟨1⟩ lenSlotVal
  let σ_solm_len := sstoreAccountMap I.codeOwner σ_solm ⟨1⟩ lenSlotVal
  have hlenAccounts : accountMapEquiv σ_evm_len σ_solm_len := by
    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨1⟩ lenSlotVal hAccounts
  have hdataFuelEq :
      solidityBytesDataWordCount (BytesStoreLiteCore.setDecodedValueBytes I).size =
        len.toNat / 32 := by
    unfold solidityBytesDataWordCount
    rw [hsize]
    have hdiv := Nat.div_add_mod len.toNat 32
    omega
  have hbridgeEvm :
      accountMapEquiv
        (solidityDataWordsForwardFrom I.codeOwner σ_evm_len baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) 0 (len.toNat / 32))
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm_len
          (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32)) := by
    exact accountMapEquiv_solidityDataWordsForwardFrom_calldataLongDataForwardFrom_full_zero
      (I := I) (len := len) (payloadStart := payloadStart) (owner := I.codeOwner)
      (baseSlot := baseSlot) hsrc haddrBound hsize hlenAbi hpayloadStart hoffMax
      (τ := σ_evm_len) (fuel := len.toNat / 32) (by omega)
  have hcong :
      accountMapEquiv
        (solidityDataWordsForwardFrom I.codeOwner σ_evm_len baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) 0 (len.toNat / 32))
        (solidityDataWordsForwardFrom I.codeOwner σ_solm_len baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) 0 (len.toNat / 32)) := by
    exact accountMapEquiv_solidityDataWordsForwardFrom
      (owner := I.codeOwner) (τ := σ_evm_len) (σ := σ_solm_len)
      (baseSlot := baseSlot) (bytes := BytesStoreLiteCore.setDecodedValueBytes I)
      (idx := 0) (len.toNat / 32) hlenAccounts
  have hdata :
      accountMapEquiv
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm_len
          (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
        (solidityDataWordsForwardFrom I.codeOwner σ_solm_len baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) 0 (len.toNat / 32)) :=
    accountMapEquiv.trans (accountMapEquiv.symm hbridgeEvm) hcong
  have hstored :=
    accountMapEquiv_sstoreAccountMap I.codeOwner baseSlot
      (len * (⟨2⟩ : UInt256) + ⟨1⟩) hdata
  simpa [baseSlot, σ_evm_len, σ_solm_len, lenSlotVal, hdataFuelEq, hheader] using hstored

theorem accountMapEquiv_pushChunkLongNoTailStorageOldLongNoClear
    {I : ExecutionEnv} {len payloadStart oldLen oldBytesLen : UInt256}
    {σ_evm σ_solm : AccountMap}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (hsize : (BytesStoreLiteCore.setDecodedValueBytes I).size = len.toNat)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hmod : len.toNat % 32 = 0)
    (hheader :
      solidityBytesHeaderWord (BytesStoreLiteCore.setDecodedValueBytes I).size =
        len * (⟨2⟩ : UInt256) + ⟨1⟩)
    (holdLenLe : oldBytesLen.toNat ≤ len.toNat) :
    let value : ByteArray := BytesStoreLiteCore.setDecodedValueBytes I
    let header : UInt256 := solidityBytesHeaderWord value.size
    let oldFuel : Nat := (oldBytesLen.toNat + 31) / 32
    let clearFuel : Nat := (value.size + 31) / 32
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner
          (sstoreAccountMap I.codeOwner σ_evm ⟨1⟩ (oldLen + ⟨1⟩))
          (bytesLikeDataBase (chunksDataBase + oldLen)) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32))
        (chunksDataBase + oldLen) (len * (⟨2⟩ : UInt256) + ⟨1⟩))
      (sstoreAccountMap I.codeOwner
        (solidityDataWordsForwardFrom I.codeOwner
          (clearDataWordsForwardFrom I.codeOwner
            (sstoreAccountMap I.codeOwner σ_solm ⟨1⟩ (oldLen + ⟨1⟩))
            (bytesLikeDataBase (chunksDataBase + oldLen)) (UInt256.ofNat clearFuel)
            (oldFuel - clearFuel))
          (chunksDataBase + oldLen) value 0 clearFuel)
        (chunksDataBase + oldLen) header) := by
  dsimp only
  let value : ByteArray := BytesStoreLiteCore.setDecodedValueBytes I
  let header : UInt256 := solidityBytesHeaderWord value.size
  let oldFuel : Nat := (oldBytesLen.toNat + 31) / 32
  let clearFuel : Nat := (value.size + 31) / 32
  have hbridge := accountMapEquiv_pushChunkLongNoTailStorage
    (I := I) (len := len) (payloadStart := payloadStart) (oldLen := oldLen)
    (σ_evm := σ_evm) (σ_solm := σ_solm)
    hAccounts hsrc haddrBound hsize hlenAbi hpayloadStart hoffMax hmod hheader
  have hdataFuelEq :
      solidityBytesDataWordCount (BytesStoreLiteCore.setDecodedValueBytes I).size =
        len.toNat / 32 := by
    unfold solidityBytesDataWordCount
    rw [hsize]
    have hdiv := Nat.div_add_mod len.toNat 32
    omega
  have hclearFuelEq : clearFuel = len.toNat / 32 := by
    dsimp [clearFuel, value]
    rw [hsize]
    exact BytesStoreLiteCore.nat_ceil32_eq_div_of_mod_zero hmod
  have holdFuelLe : oldFuel ≤ len.toNat / 32 := by
    dsimp [oldFuel]
    rw [← BytesStoreLiteCore.nat_ceil32_eq_div_of_mod_zero hmod]
    exact BytesStoreLiteCore.nat_ceil32_le_ceil32 holdLenLe
  have htailClearZero : oldFuel - clearFuel = 0 := by
    omega
  have htailClearZero' : oldFuel - len.toNat / 32 = 0 := by
    omega
  have hsolmTarget :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (solidityDataWordsForwardFrom I.codeOwner
            (sstoreAccountMap I.codeOwner σ_solm ⟨1⟩ (oldLen + ⟨1⟩))
            (chunksDataBase + oldLen) value 0 (len.toNat / 32))
          (chunksDataBase + oldLen) header)
        (sstoreAccountMap I.codeOwner
          (solidityDataWordsForwardFrom I.codeOwner
            (clearDataWordsForwardFrom I.codeOwner
              (sstoreAccountMap I.codeOwner σ_solm ⟨1⟩ (oldLen + ⟨1⟩))
              (bytesLikeDataBase (chunksDataBase + oldLen)) (UInt256.ofNat clearFuel)
              (oldFuel - clearFuel))
            (chunksDataBase + oldLen) value 0 clearFuel)
          (chunksDataBase + oldLen) header) := by
    simpa [value, header, hclearFuelEq, htailClearZero, htailClearZero',
      clearDataWordsForwardFrom] using
      accountMapEquiv_refl
        (sstoreAccountMap I.codeOwner
          (solidityDataWordsForwardFrom I.codeOwner
            (sstoreAccountMap I.codeOwner σ_solm ⟨1⟩ (oldLen + ⟨1⟩))
            (chunksDataBase + oldLen) value 0 (len.toNat / 32))
          (chunksDataBase + oldLen) header)
  exact accountMapEquiv.trans (by simpa [value, header, hdataFuelEq] using hbridge) hsolmTarget

theorem accountMapEquiv_pushChunkLongTailStorage
    {I : ExecutionEnv} {len payloadStart oldLen : UInt256}
    {σ_evm σ_solm : AccountMap}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (htailAddr :
      (payloadStart + UInt256.ofNat (32 * (len.toNat / 32))).toNat =
        payloadStart.toNat + 32 * (len.toNat / 32))
    (hsize : (BytesStoreLiteCore.setDecodedValueBytes I).size = len.toNat)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlong : ¬ len.toNat < 32)
    (hmod : len.toNat % 32 ≠ 0)
    (hheader :
      solidityBytesHeaderWord (BytesStoreLiteCore.setDecodedValueBytes I).size =
        len * (⟨2⟩ : UInt256) + ⟨1⟩) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner
            (sstoreAccountMap I.codeOwner σ_evm ⟨1⟩ (oldLen + ⟨1⟩))
            (bytesLikeDataBase (chunksDataBase + oldLen)) payloadStart (⟨0⟩ : UInt256) I
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase (chunksDataBase + oldLen))
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataTailMaskedWord
            (bytesStoreLiteCalldataLongDataWord I payloadStart
              (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
              0) len))
        (chunksDataBase + oldLen) (len * (⟨2⟩ : UInt256) + ⟨1⟩))
      (sstoreAccountMap I.codeOwner
        (solidityDataWordsForwardFrom I.codeOwner
          (sstoreAccountMap I.codeOwner σ_solm ⟨1⟩ (oldLen + ⟨1⟩))
          (chunksDataBase + oldLen) (BytesStoreLiteCore.setDecodedValueBytes I) 0
          (solidityBytesDataWordCount (BytesStoreLiteCore.setDecodedValueBytes I).size))
        (chunksDataBase + oldLen)
        (solidityBytesHeaderWord (BytesStoreLiteCore.setDecodedValueBytes I).size)) := by
  let lenSlotVal : UInt256 := oldLen + ⟨1⟩
  let baseSlot : UInt256 := chunksDataBase + oldLen
  let fullFuel : Nat := len.toNat / 32
  let σ_evm_len := sstoreAccountMap I.codeOwner σ_evm ⟨1⟩ lenSlotVal
  let σ_solm_len := sstoreAccountMap I.codeOwner σ_solm ⟨1⟩ lenSlotVal
  have hlenAccounts : accountMapEquiv σ_evm_len σ_solm_len := by
    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨1⟩ lenSlotVal hAccounts
  have hdataFuelEq :
      solidityBytesDataWordCount (BytesStoreLiteCore.setDecodedValueBytes I).size =
        fullFuel + 1 := by
    unfold solidityBytesDataWordCount
    dsimp [fullFuel]
    rw [hsize]
    have hdiv := Nat.div_add_mod len.toNat 32
    have hremLt := Nat.mod_lt len.toNat (by decide : 0 < 32)
    have hremPos : 0 < len.toNat % 32 := Nat.pos_of_ne_zero hmod
    omega
  have hbridgeEvm :
      accountMapEquiv
        (solidityDataWordsForwardFrom I.codeOwner σ_evm_len baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) 0 fullFuel)
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm_len
          (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fullFuel) := by
    exact accountMapEquiv_solidityDataWordsForwardFrom_calldataLongDataForwardFrom_full_zero
      (I := I) (len := len) (payloadStart := payloadStart) (owner := I.codeOwner)
      (baseSlot := baseSlot) hsrc haddrBound hsize hlenAbi hpayloadStart hoffMax
      (τ := σ_evm_len) (fuel := fullFuel) (by dsimp [fullFuel]; omega)
  have hcong :
      accountMapEquiv
        (solidityDataWordsForwardFrom I.codeOwner σ_evm_len baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) 0 fullFuel)
        (solidityDataWordsForwardFrom I.codeOwner σ_solm_len baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) 0 fullFuel) := by
    exact accountMapEquiv_solidityDataWordsForwardFrom
      (owner := I.codeOwner) (τ := σ_evm_len) (σ := σ_solm_len)
      (baseSlot := baseSlot) (bytes := BytesStoreLiteCore.setDecodedValueBytes I)
      (idx := 0) fullFuel hlenAccounts
  have hdataFull :
      accountMapEquiv
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm_len
          (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fullFuel)
        (solidityDataWordsForwardFrom I.codeOwner σ_solm_len baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) 0 fullFuel) :=
    accountMapEquiv.trans (accountMapEquiv.symm hbridgeEvm) hcong
  have htailWord :
      BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (UInt256.ofNat (32 * fullFuel)) 0) len =
        uInt256OfByteArray
          ((BytesStoreLiteCore.setDecodedValueBytes I).readWithPadding (fullFuel * 32) 32) := by
    simpa [fullFuel, Nat.mul_comm] using
      bytesStoreLiteCalldataLongDataTailMaskedWord_eq_decoded_tail
        (I := I) (len := len) (payloadStart := payloadStart)
        htailAddr hsrc hsize hlenAbi hpayloadStart hoffMax hlong hmod
  have hslotEq :
      BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase baseSlot) fullFuel =
        solidityBytesDataSlot baseSlot fullFuel := by
    exact bytesStoreLiteLongDataWordsLoopSlot_bytesLikeDataBase baseSlot fullFuel
  have htailStore :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm_len
            (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fullFuel)
          (BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase baseSlot) fullFuel)
          (BytesStoreLiteCore.longDataTailMaskedWord
            (bytesStoreLiteCalldataLongDataWord I payloadStart
              (UInt256.ofNat (32 * fullFuel)) 0) len))
        (solidityDataWordsForwardFrom I.codeOwner σ_solm_len baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) 0 (fullFuel + 1)) := by
    have hsplit :
        solidityDataWordsForwardFrom I.codeOwner σ_solm_len baseSlot
            (BytesStoreLiteCore.setDecodedValueBytes I) 0 (fullFuel + 1) =
          sstoreAccountMap I.codeOwner
            (solidityDataWordsForwardFrom I.codeOwner σ_solm_len baseSlot
              (BytesStoreLiteCore.setDecodedValueBytes I) 0 fullFuel)
            (solidityBytesDataSlot baseSlot fullFuel)
            (uInt256OfByteArray
              ((BytesStoreLiteCore.setDecodedValueBytes I).readWithPadding (fullFuel * 32) 32)) := by
      have happ := solidityDataWordsForwardFrom_append I.codeOwner σ_solm_len baseSlot
        (BytesStoreLiteCore.setDecodedValueBytes I) 0 fullFuel 1
      rw [happ]
      simp [solidityDataWordsForwardFrom]
    rw [hsplit]
    simpa [hslotEq, htailWord] using
      accountMapEquiv_sstoreAccountMap I.codeOwner
        (BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase baseSlot) fullFuel)
        (BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (UInt256.ofNat (32 * fullFuel)) 0) len)
        hdataFull
  have hstored :=
    accountMapEquiv_sstoreAccountMap I.codeOwner baseSlot
      (len * (⟨2⟩ : UInt256) + ⟨1⟩) htailStore
  simpa [baseSlot, σ_evm_len, σ_solm_len, lenSlotVal, fullFuel, hdataFuelEq, hheader,
    bytesStoreLiteLongDataWordsLoopStride_zero_ofNat] using hstored

theorem accountMapEquiv_pushChunkLongTailStorageOldLongNoClear
    {I : ExecutionEnv} {len payloadStart oldLen oldBytesLen : UInt256}
    {σ_evm σ_solm : AccountMap}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (htailAddr :
      (payloadStart + UInt256.ofNat (32 * (len.toNat / 32))).toNat =
        payloadStart.toNat + 32 * (len.toNat / 32))
    (hsize : (BytesStoreLiteCore.setDecodedValueBytes I).size = len.toNat)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlong : ¬ len.toNat < 32)
    (hmod : len.toNat % 32 ≠ 0)
    (hheader :
      solidityBytesHeaderWord (BytesStoreLiteCore.setDecodedValueBytes I).size =
        len * (⟨2⟩ : UInt256) + ⟨1⟩)
    (holdLenLe : oldBytesLen.toNat ≤ len.toNat) :
    let value : ByteArray := BytesStoreLiteCore.setDecodedValueBytes I
    let header : UInt256 := solidityBytesHeaderWord value.size
    let oldFuel : Nat := (oldBytesLen.toNat + 31) / 32
    let clearFuel : Nat := (value.size + 31) / 32
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner
            (sstoreAccountMap I.codeOwner σ_evm ⟨1⟩ (oldLen + ⟨1⟩))
            (bytesLikeDataBase (chunksDataBase + oldLen)) payloadStart (⟨0⟩ : UInt256) I
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase (chunksDataBase + oldLen))
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataTailMaskedWord
            (bytesStoreLiteCalldataLongDataWord I payloadStart
              (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
              0) len))
        (chunksDataBase + oldLen) (len * (⟨2⟩ : UInt256) + ⟨1⟩))
      (sstoreAccountMap I.codeOwner
        (solidityDataWordsForwardFrom I.codeOwner
          (clearDataWordsForwardFrom I.codeOwner
            (sstoreAccountMap I.codeOwner σ_solm ⟨1⟩ (oldLen + ⟨1⟩))
            (bytesLikeDataBase (chunksDataBase + oldLen)) (UInt256.ofNat clearFuel)
            (oldFuel - clearFuel))
          (chunksDataBase + oldLen) value 0 clearFuel)
        (chunksDataBase + oldLen) header) := by
  dsimp only
  let value : ByteArray := BytesStoreLiteCore.setDecodedValueBytes I
  let header : UInt256 := solidityBytesHeaderWord value.size
  let oldFuel : Nat := (oldBytesLen.toNat + 31) / 32
  let clearFuel : Nat := (value.size + 31) / 32
  let fullFuel : Nat := len.toNat / 32
  have hbridge := accountMapEquiv_pushChunkLongTailStorage
    (I := I) (len := len) (payloadStart := payloadStart) (oldLen := oldLen)
    (σ_evm := σ_evm) (σ_solm := σ_solm)
    hAccounts hsrc haddrBound htailAddr hsize hlenAbi hpayloadStart hoffMax hlong hmod
    hheader
  have hdataFuelEq :
      solidityBytesDataWordCount (BytesStoreLiteCore.setDecodedValueBytes I).size =
        fullFuel + 1 := by
    unfold solidityBytesDataWordCount
    dsimp [fullFuel]
    rw [hsize]
    have hdiv := Nat.div_add_mod len.toNat 32
    have hremLt := Nat.mod_lt len.toNat (by decide : 0 < 32)
    have hremPos : 0 < len.toNat % 32 := Nat.pos_of_ne_zero hmod
    omega
  have hclearFuelEq : clearFuel = (len.toNat + 31) / 32 := by
    dsimp [clearFuel, value]
    rw [hsize]
  have holdFuelLe : oldFuel ≤ (len.toNat + 31) / 32 := by
    dsimp [oldFuel]
    exact BytesStoreLiteCore.nat_ceil32_le_ceil32 holdLenLe
  have htailClearZero : oldFuel - clearFuel = 0 := by
    omega
  have htailClearZero' : oldFuel - (len.toNat + 31) / 32 = 0 := by
    omega
  have hceilTail : (len.toNat + 31) / 32 = fullFuel + 1 := by
    dsimp [fullFuel]
    have hdiv := Nat.div_add_mod len.toNat 32
    have hremLt := Nat.mod_lt len.toNat (by decide : 0 < 32)
    have hremPos : 0 < len.toNat % 32 := Nat.pos_of_ne_zero hmod
    omega
  have htailClearZero'' : oldFuel - (fullFuel + 1) = 0 := by
    omega
  have hsolmTarget :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (solidityDataWordsForwardFrom I.codeOwner
            (sstoreAccountMap I.codeOwner σ_solm ⟨1⟩ (oldLen + ⟨1⟩))
            (chunksDataBase + oldLen) value 0 (fullFuel + 1))
          (chunksDataBase + oldLen) header)
        (sstoreAccountMap I.codeOwner
          (solidityDataWordsForwardFrom I.codeOwner
            (clearDataWordsForwardFrom I.codeOwner
              (sstoreAccountMap I.codeOwner σ_solm ⟨1⟩ (oldLen + ⟨1⟩))
              (bytesLikeDataBase (chunksDataBase + oldLen)) (UInt256.ofNat clearFuel)
              (oldFuel - clearFuel))
            (chunksDataBase + oldLen) value 0 clearFuel)
          (chunksDataBase + oldLen) header) := by
    simpa [value, header, hclearFuelEq, htailClearZero, htailClearZero',
      htailClearZero'', hceilTail, fullFuel, clearDataWordsForwardFrom] using
      accountMapEquiv_refl
        (sstoreAccountMap I.codeOwner
          (solidityDataWordsForwardFrom I.codeOwner
            (sstoreAccountMap I.codeOwner σ_solm ⟨1⟩ (oldLen + ⟨1⟩))
            (chunksDataBase + oldLen) value 0 (fullFuel + 1))
          (chunksDataBase + oldLen) header)
  exact accountMapEquiv.trans
    (by simpa [value, header, fullFuel, hdataFuelEq] using hbridge)
    hsolmTarget

theorem bytesStoreLiteX_pushChunkLongNoTailReachReturnWordSplit
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
    let slot : UInt256 := chunksDataBase + oldLen
    let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
    let σ' : AccountMap :=
      sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σLen
          (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨263⟩
      [(σ'.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)),
        bytesStoreLiteSelWord I]
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ') k C := by
  dsimp only
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
  let slot : UInt256 := chunksDataBase + oldLen
  let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
  let σ' : AccountMap :=
    sstoreAccountMap I.codeOwner
      (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σLen
        (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
      slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  have hbranch := bytesStoreLiteX_pushChunkShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart)
    hperm hreach hlenMax hflag hvalid
  have hwrite := bytesStoreLiteX_writeBytesNewLongNoTailFromWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (τ := σLen) (slot := slot) (payloadStart := payloadStart) (len := len)
    (ret := ⟨1617⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty)
    hperm
    (by simpa [oldLen, slot, σLen] using hbranch)
    hlong hnoTailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hret := bytesStoreLiteX_pushChunkReturnFromHelperRetSplit
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := σ') (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (slot := slot) (payloadStart := payloadStart) (len := len)
    (sel := bytesStoreLiteSelWord I)
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [oldLen, slot, σLen, σ'] using hwrite)
  simpa [oldLen, slot, σLen, σ', bytesStoreLiteClearCurrentHashAw3] using hret

theorem bytesStoreLiteWordAt0Mem_wordAt0Mem_read64
    (slot : UInt256) :
    (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  exact bytesStoreLiteWordAt0Mem_read64 slot
    (wordAt0Mem_size_96 (⟨1⟩ : UInt256) solcFreePtrMem_size)
    (bytesStoreLiteWordAt0Mem_read64 (⟨1⟩ : UInt256)
      solcFreePtrMem_size solcFreePtrMem_read64)

theorem bytesStoreLiteWordAt0Mem_wordAt0Mem_wordAt0Mem_read64
    (slot : UInt256) :
    (wordAt0Mem slot (wordAt0Mem slot
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  exact bytesStoreLiteWordAt0Mem_read64 slot
    (wordAt0Mem_size_96 slot
      (wordAt0Mem_size_96 (⟨1⟩ : UInt256) solcFreePtrMem_size))
    (bytesStoreLiteWordAt0Mem_wordAt0Mem_read64 slot)

theorem bytesStoreLiteX_writeBytesCleanupOldLongLongToLoop {cA gh bl σinit σ σ₀ A I}
    {g : Sat256} {slot oldLen len ret : UInt256} {tail : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2302⟩
      (slot :: oldLen :: len :: ret :: tail) mem aw rdata (cA, σ) k C)
    (holdLong : UInt256.gt oldLen ⟨31⟩ = ⟨1⟩)
    (hgtOldNew : UInt256.gt oldLen len = ⟨1⟩)
    (hlong : UInt256.lt len ⟨32⟩ = ⟨0⟩)
    (hov : tail.length + 16 ≤ 1024) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2359⟩
      (⟨0⟩ ::
        UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩) ::
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ::
        slot :: oldLen :: len :: ret :: tail)
      (wordAt0Mem slot mem)
      (BytesStoreLiteCore.clearCurrentHashAw aw) rdata (cA, σ) k C := by
  obtain ⟨_, _, rd2302⟩ := hreach
  have hslotHash :
      UInt256.ofNat
          (fromByteArrayBigEndian (ffi.KEC ((wordAt0Mem slot mem).readWithPadding 0 32))) =
        bytesLikeDataBase slot := by
    rw [wordAt0Mem_read0, bytesLikeDataBase, uInt256OfByteArray_eq]
  have rd2308 := evm_run rd2302 with [
    jumpdest, push1 ⟨31⟩, dup3, gt, iszero, push2 ⟨1809⟩]
  have rd2310 := rd2308.jumpiNT (by native_decide)
    (by rw [holdLong]; decide)
    (by simp only [List.length_cons]; omega)
  have rd2318 := evm_run rd2310 with [dup3, dup3, gt, iszero, push2 ⟨1809⟩]
  have rd2320 := rd2318.jumpiNT (by native_decide)
    (by rw [hgtOldNew]; decide)
    (by simp only [List.length_cons]; omega)
  have rd2343 := evm_run rd2320 with [
    dup1, push0,
    raw mstore (Cₘ (BytesStoreLiteCore.clearCurrentBaseAw aw) - Cₘ aw)
      (wordAt0Mem slot mem)
      (BytesStoreLiteCore.clearCurrentBaseAw aw) (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          BytesStoreLiteCore.clearCurrentBaseAw])
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256
      (Cₘ (BytesStoreLiteCore.clearCurrentHashAw aw) -
        Cₘ (BytesStoreLiteCore.clearCurrentBaseAw aw))
      (bytesLikeDataBase slot)
      (BytesStoreLiteCore.clearCurrentHashAw aw) (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          BytesStoreLiteCore.clearCurrentHashAw, BytesStoreLiteCore.clearCurrentBaseAw])
      hslotHash (by rfl) (by evm_ov),
    push1 ⟨31⟩, dup5, add, push1 ⟨5⟩, shr, push1 ⟨32⟩, dup6, lt, iszero,
    push2 ⟨2345⟩]
  have rd2345 := rd2343.jumpiT (by native_decide)
    (by rw [hlong]; decide)
    (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd2345 with [
    jumpdest, swap1, dup2, add, swap1, push1 ⟨31⟩, dup5, add,
    push1 ⟨5⟩, shr, sub, push0]⟩

theorem bytesStoreLiteX_writeBytesCleanupOldLongShortToLoop {cA gh bl σinit σ σ₀ A I}
    {g : Sat256} {slot oldLen len ret : UInt256} {tail : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2302⟩
      (slot :: oldLen :: len :: ret :: tail) mem aw rdata (cA, σ) k C)
    (holdLong : UInt256.gt oldLen ⟨31⟩ = ⟨1⟩)
    (hgtOldNew : UInt256.gt oldLen len = ⟨1⟩)
    (hshort : UInt256.lt len ⟨32⟩ = ⟨1⟩)
    (hov : tail.length + 16 ≤ 1024) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2359⟩
      (⟨0⟩ ::
        UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩ ::
        ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ::
        slot :: oldLen :: len :: ret :: tail)
      (wordAt0Mem slot mem)
      (BytesStoreLiteCore.clearCurrentHashAw aw) rdata (cA, σ) k C := by
  obtain ⟨_, _, rd2302⟩ := hreach
  have hslotHash :
      UInt256.ofNat
          (fromByteArrayBigEndian (ffi.KEC ((wordAt0Mem slot mem).readWithPadding 0 32))) =
        bytesLikeDataBase slot := by
    rw [wordAt0Mem_read0, bytesLikeDataBase, uInt256OfByteArray_eq]
  have rd2308 := evm_run rd2302 with [
    jumpdest, push1 ⟨31⟩, dup3, gt, iszero, push2 ⟨1809⟩]
  have rd2310 := rd2308.jumpiNT (by native_decide)
    (by rw [holdLong]; decide)
    (by simp only [List.length_cons]; omega)
  have rd2318 := evm_run rd2310 with [dup3, dup3, gt, iszero, push2 ⟨1809⟩]
  have rd2320 := rd2318.jumpiNT (by native_decide)
    (by rw [hgtOldNew]; decide)
    (by simp only [List.length_cons]; omega)
  have rd2343 := evm_run rd2320 with [
    dup1, push0,
    raw mstore (Cₘ (BytesStoreLiteCore.clearCurrentBaseAw aw) - Cₘ aw)
      (wordAt0Mem slot mem)
      (BytesStoreLiteCore.clearCurrentBaseAw aw) (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          BytesStoreLiteCore.clearCurrentBaseAw])
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256
      (Cₘ (BytesStoreLiteCore.clearCurrentHashAw aw) -
        Cₘ (BytesStoreLiteCore.clearCurrentBaseAw aw))
      (bytesLikeDataBase slot)
      (BytesStoreLiteCore.clearCurrentHashAw aw) (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          BytesStoreLiteCore.clearCurrentHashAw, BytesStoreLiteCore.clearCurrentBaseAw])
      hslotHash (by rfl) (by evm_ov),
    push1 ⟨31⟩, dup5, add, push1 ⟨5⟩, shr, push1 ⟨32⟩, dup6, lt, iszero,
    push2 ⟨2345⟩]
  have rd2345 := rd2343.jumpiNT (by native_decide)
    (by rw [hshort]; decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by
    have hrd := evm_run rd2345 with [
      pop, push0, jumpdest, swap1, dup2, add, swap1, push1 ⟨31⟩, dup5, add,
      push1 ⟨5⟩, shr, sub, push0]
    exact hrd⟩

theorem bytesStoreLiteX_pushChunkShortOldLongReachWriteBranchWithLoopSchedule
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart oldStoredLen : UInt256}
    {fuel : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          ((sstoreAccountMap I.codeOwner σ ⟨1⟩
            (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD
                (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hshort : len.toNat < 32)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ i)
          (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩)) =
        ⟨0⟩)
    (hdone :
      UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ fuel)
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩) =
        ⟨0⟩) :
    let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
    let slot : UInt256 := chunksDataBase + oldLen
    let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [slot, payloadStart, len, ⟨1617⟩, slot, ⟨0⟩, len, payloadStart, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, clearDataWordsForwardFrom I.codeOwner σLen
        ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩ fuel) k C := by
  dsimp only
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
  let slot : UInt256 := chunksDataBase + oldLen
  let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
  let header : UInt256 :=
    (σLen.find? I.codeOwner |>.option ⟨0⟩
      (fun acc => acc.storage.findD slot ⟨0⟩))
  have hdecoder := bytesStoreLiteX_pushChunkReachWriteHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    hperm hreach hlenMax
  have hstoredEq : UInt256.div header ⟨2⟩ = oldStoredLen := by
    simpa [header, slot, oldLen, σLen] using holdStoredLen.symm
  have hvalidHeader :
      UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [header, slot, oldLen, σLen, hstoredEq] using hvalid
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σLen) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header) (ret := ⟨2637⟩)
    (rest := [len, ⟨2643⟩, slot, payloadStart, len, ⟨1617⟩, slot, ⟨0⟩,
      len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty)
    (by simpa [header, slot, oldLen, σLen] using hdecoder)
    (by simpa [header, slot, oldLen, σLen] using hflag)
    hvalidHeader
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2637₀⟩ := hdecoded
  obtain ⟨_, _, rd2637⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2637⟩
        [oldStoredLen, len, ⟨2643⟩, slot, payloadStart, len, ⟨1617⟩, slot, ⟨0⟩,
          len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σLen) k C := by
    exact ⟨_, _, by simpa [hstoredEq] using rd2637₀⟩
  have hcleanupReach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2302⟩
      [slot, oldStoredLen, len, ⟨2643⟩, slot, payloadStart, len, ⟨1617⟩, slot,
        ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σLen) k C := by
    exact ⟨_, _, evm_run rd2637 with [
      jumpdest, dup4, push2 ⟨2302⟩, jump (by native_decide)]⟩
  have hgt31 : UInt256.lt ⟨31⟩ oldStoredLen ≠ ⟨0⟩ :=
    BytesStoreLiteCore.clearCurrentLongValid_gt31
      (header := header) (len := oldStoredLen)
      (by simpa [header, slot, oldLen, σLen] using hflag)
      (by simpa [header, slot, oldLen, σLen] using hvalid)
  have holdLong : UInt256.gt oldStoredLen ⟨31⟩ = ⟨1⟩ := by
    rw [show UInt256.gt oldStoredLen ⟨31⟩ = UInt256.lt ⟨31⟩ oldStoredLen from rfl]
    exact BytesStoreLiteCore.clearCurrent_ult_eq_one_of_ne_zero hgt31
  have holdGtNat : 31 < oldStoredLen.toNat := by
    simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using
      ult_ne_zero_toNat_lt hgt31
  have hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩ :=
    ugt_one (by omega)
  have hshortWord : UInt256.lt len ⟨32⟩ = ⟨1⟩ :=
    ult_one (by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
  have hloopEntry := bytesStoreLiteX_writeBytesCleanupOldLongShortToLoop
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σLen) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (oldLen := oldStoredLen)
    (len := len) (ret := ⟨2643⟩)
    (tail := [slot, payloadStart, len, ⟨1617⟩, slot, ⟨0⟩, len, payloadStart,
      ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty)
    hcleanupReach holdLong hgtOldNew hshortWord
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hloop := bytesStoreLiteX_setClearDataWordsLoopGenerated
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σLen) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (idx := (⟨0⟩ : UInt256))
    (count := UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩)
    (base := (⟨0⟩ : UInt256) + bytesLikeDataBase slot)
    (dead₀ := slot) (dead₁ := oldStoredLen) (dead₂ := len)
    (ret := (⟨2643⟩ : UInt256))
    (rest := [slot, payloadStart, len, ⟨1617⟩, slot, ⟨0⟩, len, payloadStart,
      ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (fuel := fuel)
    hperm hloopEntry hcontinue hdone (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  simpa [oldLen, slot, σLen] using hloop

theorem bytesStoreLiteX_pushChunkShortOldLongReachWriteBranch
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          ((sstoreAccountMap I.codeOwner σ ⟨1⟩
            (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD
                (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hshort : len.toNat < 32) :
    let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
    let slot : UInt256 := chunksDataBase + oldLen
    let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [slot, payloadStart, len, ⟨1617⟩, slot, ⟨0⟩, len, payloadStart, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, clearDataWordsForwardFrom I.codeOwner σLen
        ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat) k C := by
  let count := UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩
  have hcontinue : ∀ i, i < count.toNat →
      UInt256.isZero
        (UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ i) count) =
          ⟨0⟩ := by
    intro i hi
    have hidx : (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ i).toNat = i := by
      rw [BytesStoreLiteCore.clearDataWordsLoopIndex_zero_ofNat]
      exact ulit_toNat' i (lt_trans hi count.val.isLt)
    have hlt : UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ i) count = ⟨1⟩ :=
      ult_one (by simpa [hidx] using hi)
    rw [hlt]
    decide
  have hdone :
      UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ count.toNat) count =
        ⟨0⟩ := by
    rw [BytesStoreLiteCore.clearDataWordsLoopIndex_zero_ofNat, u256_ofNat_toNat count]
    exact ult_zero (a := count) (b := count) (Nat.le_refl _)
  simpa [count] using
    bytesStoreLiteX_pushChunkShortOldLongReachWriteBranchWithLoopSchedule
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (len := len) (payloadStart := payloadStart)
      (oldStoredLen := oldStoredLen) (fuel := count.toNat)
      hperm hreach hlenMax hflag holdStoredLen hvalid hshort hcontinue hdone

theorem bytesStoreLiteX_pushChunkReturnFromShortWriteSplit {cA gh bl σinit σ σ₀ A I}
    {g : Sat256} {slot payloadStart len sel : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2688⟩
      [UInt256.gt len ⟨31⟩, ⟨0⟩, slot, payloadStart, len, ⟨1617⟩,
        slot, ⟨0⟩, len, payloadStart, ⟨263⟩, sel]
      mem aw rdata (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨263⟩
      [(σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)), sel]
      mem aw rdata (cA, σ) k C := by
  obtain ⟨_, _, rd2688⟩ := hreach
  have rd2572 := evm_run rd2688 with [push2 ⟨2572⟩, jump (by native_decide)]
  have rd1617 := evm_run rd2572 with [
    jumpdest, pop, pop, pop, pop, pop, jump (by native_decide)]
  exact bytesStoreLiteX_pushChunkReturnFromHelperRetSplit
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (payloadStart := payloadStart)
    (len := len) (sel := sel) (mem := mem) (aw := aw) (rdata := rdata)
    ⟨_, _, rd1617⟩

theorem bytesStoreLiteX_pushChunkEmptyWriteHeaderGeneric {cA gh bl σinit σ σ₀ A I}
    {g : Sat256} {slot payloadStart len sel : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2669⟩
      [⟨0⟩, UInt256.gt len ⟨31⟩, ⟨0⟩, slot, payloadStart, len, ⟨1617⟩,
        slot, ⟨0⟩, len, payloadStart, ⟨263⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hlenZero : len = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2688⟩
      [UInt256.gt len ⟨31⟩, ⟨0⟩, slot, payloadStart, len, ⟨1617⟩,
        slot, ⟨0⟩, len, payloadStart, ⟨263⟩, sel]
      mem aw rdata (cA, sstoreAccountMap I.codeOwner σ slot ⟨0⟩) k C := by
  obtain ⟨_, _, rd2669⟩ := hreach
  have rd2687pre := evm_run rd2669 with [
    jumpdest, push0, not, push1 ⟨3⟩, dup8, swap1, shl, shr, not, and,
    push1 ⟨1⟩, dup7, swap1, shl, lor, dup4]
  obtain ⟨_, _, rd2688₀⟩ := rd2687pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [initState, hlenZero] using rd2688₀⟩

theorem bytesStoreLiteX_pushChunkShortOldLongReachReturnWordSplit
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          ((sstoreAccountMap I.codeOwner σ ⟨1⟩
            (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD
                (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
    let slot : UInt256 := chunksDataBase + oldLen
    let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σLen
        ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
    let storedWord : UInt256 :=
      UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          (uInt256OfByteArray (I.calldata.readBytes payloadStart.toNat 32)))
    let σ' : AccountMap := sstoreAccountMap I.codeOwner σClear slot storedWord
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨263⟩
      [(σ'.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)),
        bytesStoreLiteSelWord I]
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σ') k C := by
  dsimp only
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
  let slot : UInt256 := chunksDataBase + oldLen
  let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σLen
      ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  let storedWord : UInt256 :=
    UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
      (UInt256.land
        (UInt256.lnot
          (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
        (uInt256OfByteArray (I.calldata.readBytes payloadStart.toNat 32)))
  let σ' : AccountMap := sstoreAccountMap I.codeOwner σClear slot storedWord
  have hbranch := bytesStoreLiteX_pushChunkShortOldLongReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (oldStoredLen := oldStoredLen)
    hperm hreach hlenMax hflag holdStoredLen hvalid hshort
  have hwrite := bytesStoreLiteX_writeBytesNewShortNonemptyWriteHeader
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σClear) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (payloadStart := payloadStart)
    (len := len) (ret := ⟨1617⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    hperm (by simpa [oldLen, slot, σLen, σClear] using hbranch) hnz hshort
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hret := bytesStoreLiteX_pushChunkReturnFromShortWriteSplit
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := σ') (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (slot := slot) (payloadStart := payloadStart) (len := len)
    (sel := bytesStoreLiteSelWord I)
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [oldLen, slot, σLen, σClear, storedWord, σ'] using hwrite)
  simpa [oldLen, slot, σLen, σClear, storedWord, σ'] using hret

theorem bytesStoreLiteX_pushChunkShortOldLongReturnsSplit
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          ((sstoreAccountMap I.codeOwner σ ⟨1⟩
            (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD
                (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
    let slot : UInt256 := chunksDataBase + oldLen
    let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σLen
        ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
    let storedWord : UInt256 :=
      UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          (uInt256OfByteArray (I.calldata.readBytes payloadStart.toNat 32)))
    let σ' : AccountMap := sstoreAccountMap I.codeOwner σClear slot storedWord
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
      (UInt256.toByteArray
        (σ'.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩))) := by
  dsimp only
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
  let slot : UInt256 := chunksDataBase + oldLen
  let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σLen
      ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  let storedWord : UInt256 :=
    UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
      (UInt256.land
        (UInt256.lnot
          (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
        (uInt256OfByteArray (I.calldata.readBytes payloadStart.toNat 32)))
  let σ' : AccountMap := sstoreAccountMap I.codeOwner σClear slot storedWord
  exact bytesStoreLiteX_returnWord263OfMemState
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (wordAt0Mem_size_96 slot
      (wordAt0Mem_size_96 (⟨1⟩ : UInt256) solcFreePtrMem_size))
    (bytesStoreLiteWordAt0Mem_wordAt0Mem_read64 slot)
    (by
      simpa [oldLen, slot, σLen, σClear, storedWord, σ'] using
        bytesStoreLiteX_pushChunkShortOldLongReachReturnWordSplit
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) (len := len) (payloadStart := payloadStart)
          (oldStoredLen := oldStoredLen)
          hperm hreach hlenMax hflag holdStoredLen hvalid hnz hshort)

theorem bytesStoreLiteX_pushChunkEmptyOldLongReachReturnWordSplit
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          ((sstoreAccountMap I.codeOwner σ ⟨1⟩
            (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD
                (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩) :
    let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
    let slot : UInt256 := chunksDataBase + oldLen
    let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σLen
        ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
    let σ' : AccountMap := sstoreAccountMap I.codeOwner σClear slot ⟨0⟩
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨263⟩
      [(σ'.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)),
        bytesStoreLiteSelWord I]
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σ') k C := by
  dsimp only
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
  let slot : UInt256 := chunksDataBase + oldLen
  let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σLen
      ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  let σ' : AccountMap := sstoreAccountMap I.codeOwner σClear slot ⟨0⟩
  have hshort : len.toNat < 32 := by
    rw [hlenZero]
    decide
  have hbranch := bytesStoreLiteX_pushChunkShortOldLongReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (oldStoredLen := oldStoredLen)
    hperm hreach hlenMax hflag holdStoredLen hvalid hshort
  have hpacked := bytesStoreLiteX_writeBytesNewEmptyReachPackedHeader
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σClear) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (payloadStart := payloadStart)
    (len := len) (ret := ⟨1617⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [oldLen, slot, σLen, σClear] using hbranch)
    hlenZero
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hwrite := bytesStoreLiteX_pushChunkEmptyWriteHeaderGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σClear) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (payloadStart := payloadStart)
    (len := len) (sel := bytesStoreLiteSelWord I)
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    hperm
    (by simpa [oldLen, slot, σLen, σClear] using hpacked)
    hlenZero
  have hret := bytesStoreLiteX_pushChunkReturnFromShortWriteSplit
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := σ') (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (slot := slot) (payloadStart := payloadStart) (len := len)
    (sel := bytesStoreLiteSelWord I)
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [oldLen, slot, σLen, σClear, σ'] using hwrite)
  simpa [oldLen, slot, σLen, σClear, σ'] using hret

theorem bytesStoreLiteX_pushChunkEmptyOldLongReturnsSplit
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          ((sstoreAccountMap I.codeOwner σ ⟨1⟩
            (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD
                (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩) :
    let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
    let slot : UInt256 := chunksDataBase + oldLen
    let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σLen
        ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
    let σ' : AccountMap := sstoreAccountMap I.codeOwner σClear slot ⟨0⟩
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
      (UInt256.toByteArray
        (σ'.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩))) := by
  dsimp only
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
  let slot : UInt256 := chunksDataBase + oldLen
  let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σLen
      ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  let σ' : AccountMap := sstoreAccountMap I.codeOwner σClear slot ⟨0⟩
  exact bytesStoreLiteX_returnWord263OfMemState
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (wordAt0Mem_size_96 slot
      (wordAt0Mem_size_96 (⟨1⟩ : UInt256) solcFreePtrMem_size))
    (bytesStoreLiteWordAt0Mem_wordAt0Mem_read64 slot)
    (by
      simpa [oldLen, slot, σLen, σClear, σ'] using
        bytesStoreLiteX_pushChunkEmptyOldLongReachReturnWordSplit
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) (len := len) (payloadStart := payloadStart)
          (oldStoredLen := oldStoredLen)
          hperm hreach hlenMax hflag holdStoredLen hvalid hlenZero)

theorem bytesStoreLiteX_pushChunkLongHeaderNoClearReachWriteBranch
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          ((sstoreAccountMap I.codeOwner σ ⟨1⟩
            (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD
                (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩) :
    let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
    let slot : UInt256 := chunksDataBase + oldLen
    let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [slot, payloadStart, len, ⟨1617⟩, slot, ⟨0⟩, len, payloadStart, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σLen) k C := by
  dsimp only
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
  let slot : UInt256 := chunksDataBase + oldLen
  let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
  let header : UInt256 :=
    (σLen.find? I.codeOwner |>.option ⟨0⟩
      (fun acc => acc.storage.findD slot ⟨0⟩))
  have hdecoder := bytesStoreLiteX_pushChunkReachWriteHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    hperm hreach hlenMax
  have hstoredEq : UInt256.div header ⟨2⟩ = oldStoredLen := by
    simpa [header, slot, oldLen, σLen] using holdStoredLen.symm
  have hvalidHeader :
      UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [header, slot, oldLen, σLen, hstoredEq] using hvalid
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σLen) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header) (ret := ⟨2637⟩)
    (rest := [len, ⟨2643⟩, slot, payloadStart, len, ⟨1617⟩, slot, ⟨0⟩,
      len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty)
    (by simpa [header, slot, oldLen, σLen] using hdecoder)
    (by simpa [header, slot, oldLen, σLen] using hflag)
    hvalidHeader
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2637₀⟩ := hdecoded
  obtain ⟨_, _, rd2637⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2637⟩
        [oldStoredLen, len, ⟨2643⟩, slot, payloadStart, len, ⟨1617⟩, slot, ⟨0⟩,
          len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σLen) k C := by
    exact ⟨_, _, by simpa [hstoredEq] using rd2637₀⟩
  have hcleanupReach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2302⟩
      [slot, oldStoredLen, len, ⟨2643⟩, slot, payloadStart, len, ⟨1617⟩, slot,
        ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σLen) k C := by
    exact ⟨_, _, evm_run rd2637 with [
      jumpdest, dup4, push2 ⟨2302⟩, jump (by native_decide)]⟩
  have hgt31 : UInt256.lt ⟨31⟩ oldStoredLen ≠ ⟨0⟩ :=
    BytesStoreLiteCore.clearCurrentLongValid_gt31
      (header := header) (len := oldStoredLen)
      (by simpa [header, slot, oldLen, σLen] using hflag)
      (by simpa [header, slot, oldLen, σLen] using hvalid)
  have holdLong : UInt256.gt oldStoredLen ⟨31⟩ = ⟨1⟩ := by
    rw [show UInt256.gt oldStoredLen ⟨31⟩ = UInt256.lt ⟨31⟩ oldStoredLen from rfl]
    exact BytesStoreLiteCore.clearCurrent_ult_eq_one_of_ne_zero hgt31
  simpa [oldLen, slot, σLen] using
    bytesStoreLiteX_writeBytesCleanupOldLongNoClear
      (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σLen) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (slot := slot) (oldLen := oldStoredLen)
      (len := len) (ret := ⟨2643⟩)
      (tail := [slot, payloadStart, len, ⟨1617⟩, slot, ⟨0⟩, len, payloadStart,
        ⟨263⟩, bytesStoreLiteSelWord I])
      (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
      (rdata := ByteArray.empty)
      hcleanupReach holdLong hgtOldNew (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_pushChunkLongHeaderClearReachWriteBranchWithLoopSchedule
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart oldStoredLen : UInt256}
    {fuel : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          ((sstoreAccountMap I.codeOwner σ ⟨1⟩
            (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD
                (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ i)
          (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
            (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩))) = ⟨0⟩)
    (hdone :
      UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ fuel)
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)) = ⟨0⟩) :
    let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
    let slot : UInt256 := chunksDataBase + oldLen
    let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [slot, payloadStart, len, ⟨1617⟩, slot, ⟨0⟩, len, payloadStart, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, clearDataWordsForwardFrom I.codeOwner σLen
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩ fuel) k C := by
  dsimp only
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
  let slot : UInt256 := chunksDataBase + oldLen
  let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
  let header : UInt256 :=
    (σLen.find? I.codeOwner |>.option ⟨0⟩
      (fun acc => acc.storage.findD slot ⟨0⟩))
  have hdecoder := bytesStoreLiteX_pushChunkReachWriteHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    hperm hreach hlenMax
  have hstoredEq : UInt256.div header ⟨2⟩ = oldStoredLen := by
    simpa [header, slot, oldLen, σLen] using holdStoredLen.symm
  have hvalidHeader :
      UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [header, slot, oldLen, σLen, hstoredEq] using hvalid
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σLen) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header) (ret := ⟨2637⟩)
    (rest := [len, ⟨2643⟩, slot, payloadStart, len, ⟨1617⟩, slot, ⟨0⟩,
      len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty)
    (by simpa [header, slot, oldLen, σLen] using hdecoder)
    (by simpa [header, slot, oldLen, σLen] using hflag)
    hvalidHeader
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2637₀⟩ := hdecoded
  obtain ⟨_, _, rd2637⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2637⟩
        [oldStoredLen, len, ⟨2643⟩, slot, payloadStart, len, ⟨1617⟩, slot, ⟨0⟩,
          len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σLen) k C := by
    exact ⟨_, _, by simpa [hstoredEq] using rd2637₀⟩
  have hcleanupReach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2302⟩
      [slot, oldStoredLen, len, ⟨2643⟩, slot, payloadStart, len, ⟨1617⟩, slot,
        ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σLen) k C := by
    exact ⟨_, _, evm_run rd2637 with [
      jumpdest, dup4, push2 ⟨2302⟩, jump (by native_decide)]⟩
  have hgt31 : UInt256.lt ⟨31⟩ oldStoredLen ≠ ⟨0⟩ :=
    BytesStoreLiteCore.clearCurrentLongValid_gt31
      (header := header) (len := oldStoredLen)
      (by simpa [header, slot, oldLen, σLen] using hflag)
      (by simpa [header, slot, oldLen, σLen] using hvalid)
  have holdLong : UInt256.gt oldStoredLen ⟨31⟩ = ⟨1⟩ := by
    rw [show UInt256.gt oldStoredLen ⟨31⟩ = UInt256.lt ⟨31⟩ oldStoredLen from rfl]
    exact BytesStoreLiteCore.clearCurrent_ult_eq_one_of_ne_zero hgt31
  have hlongWord : UInt256.lt len ⟨32⟩ = ⟨0⟩ :=
    ult_zero (by
      have hle : 32 ≤ len.toNat := Nat.le_of_not_gt hlong
      simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hle)
  have hloopEntry := bytesStoreLiteX_writeBytesCleanupOldLongLongToLoop
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σLen) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (oldLen := oldStoredLen)
    (len := len) (ret := ⟨2643⟩)
    (tail := [slot, payloadStart, len, ⟨1617⟩, slot, ⟨0⟩, len, payloadStart,
      ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty)
    hcleanupReach holdLong hgtOldNew hlongWord
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hloop := bytesStoreLiteX_setClearDataWordsLoopGenerated
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σLen) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (idx := (⟨0⟩ : UInt256))
    (count := UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩))
    (base := UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot)
    (dead₀ := slot) (dead₁ := oldStoredLen) (dead₂ := len)
    (ret := (⟨2643⟩ : UInt256))
    (rest := [slot, payloadStart, len, ⟨1617⟩, slot, ⟨0⟩, len, payloadStart,
      ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (fuel := fuel)
    hperm hloopEntry hcontinue hdone (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  simpa [oldLen, slot, σLen] using hloop

theorem bytesStoreLiteX_pushChunkLongHeaderClearReachWriteBranch
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          ((sstoreAccountMap I.codeOwner σ ⟨1⟩
            (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD
                (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32) :
    let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
    let slot : UInt256 := chunksDataBase + oldLen
    let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [slot, payloadStart, len, ⟨1617⟩, slot, ⟨0⟩, len, payloadStart, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, clearDataWordsForwardFrom I.codeOwner σLen
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat) k C := by
  let count := UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
    (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)
  have hcontinue : ∀ i, i < count.toNat →
      UInt256.isZero
        (UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ i) count) =
          ⟨0⟩ := by
    intro i hi
    have hidx : (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ i).toNat = i := by
      rw [BytesStoreLiteCore.clearDataWordsLoopIndex_zero_ofNat]
      exact ulit_toNat' i (lt_trans hi count.val.isLt)
    have hlt : UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ i) count = ⟨1⟩ :=
      ult_one (by simpa [hidx] using hi)
    rw [hlt]
    decide
  have hdone :
      UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ count.toNat) count =
        ⟨0⟩ := by
    rw [BytesStoreLiteCore.clearDataWordsLoopIndex_zero_ofNat, u256_ofNat_toNat count]
    exact ult_zero (a := count) (b := count) (Nat.le_refl _)
  simpa [count] using
    bytesStoreLiteX_pushChunkLongHeaderClearReachWriteBranchWithLoopSchedule
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (len := len) (payloadStart := payloadStart)
      (oldStoredLen := oldStoredLen) (fuel := count.toNat)
      hperm hreach hlenMax hflag holdStoredLen hvalid hgtOldNew hlong
      hcontinue hdone

theorem bytesStoreLiteX_pushChunkLongNoTailOldLongClearReachReturnWordSplit
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          ((sstoreAccountMap I.codeOwner σ ⟨1⟩
            (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD
                (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
    let slot : UInt256 := chunksDataBase + oldLen
    let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σLen
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
    let σ' : AccountMap :=
      sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
          (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨263⟩
      [(σ'.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)),
        bytesStoreLiteSelWord I]
      (wordAt0Mem slot (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ') k C := by
  dsimp only
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
  let slot : UInt256 := chunksDataBase + oldLen
  let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σLen
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
  let σ' : AccountMap :=
    sstoreAccountMap I.codeOwner
      (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
        (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
      slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  have hbranch := bytesStoreLiteX_pushChunkLongHeaderClearReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (oldStoredLen := oldStoredLen)
    hperm hreach hlenMax hflag holdStoredLen hvalid hgtOldNew hlong
  have hwrite := bytesStoreLiteX_writeBytesNewLongNoTailFromWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (τ := σClear) (slot := slot) (payloadStart := payloadStart) (len := len)
    (ret := ⟨1617⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    hperm
    (by simpa [oldLen, slot, σLen, σClear] using hbranch)
    hlong hnoTailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hret := bytesStoreLiteX_pushChunkReturnFromHelperRetSplit
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := σ') (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (slot := slot) (payloadStart := payloadStart) (len := len)
    (sel := bytesStoreLiteSelWord I)
    (mem := wordAt0Mem slot (wordAt0Mem slot
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
    (aw := BytesStoreLiteCore.clearCurrentHashAw
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)))
    (rdata := ByteArray.empty)
    (by simpa [oldLen, slot, σLen, σClear, σ'] using hwrite)
  simpa [oldLen, slot, σLen, σClear, σ', bytesStoreLiteClearCurrentHashAw3] using hret

theorem bytesStoreLiteX_pushChunkLongNoTailOldLongClearReturnsSplit
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          ((sstoreAccountMap I.codeOwner σ ⟨1⟩
            (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD
                (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
    let slot : UInt256 := chunksDataBase + oldLen
    let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σLen
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
    let σ' : AccountMap :=
      sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
          (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
      (UInt256.toByteArray
        (σ'.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩))) := by
  dsimp only
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
  let slot : UInt256 := chunksDataBase + oldLen
  let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σLen
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
  let σ' : AccountMap :=
    sstoreAccountMap I.codeOwner
      (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
        (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
      slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  exact bytesStoreLiteX_returnWord263OfMemState
    (mem := wordAt0Mem slot (wordAt0Mem slot
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
    (wordAt0Mem_size_96 slot
      (wordAt0Mem_size_96 slot
        (wordAt0Mem_size_96 (⟨1⟩ : UInt256) solcFreePtrMem_size)))
    (bytesStoreLiteWordAt0Mem_wordAt0Mem_wordAt0Mem_read64 slot)
    (by
      simpa [oldLen, slot, σLen, σClear, σ'] using
        bytesStoreLiteX_pushChunkLongNoTailOldLongClearReachReturnWordSplit
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) (len := len) (payloadStart := payloadStart)
          (oldStoredLen := oldStoredLen)
          hperm hreach hlenMax hflag holdStoredLen hvalid hgtOldNew hlong hnoTailMod)

theorem bytesStoreLiteX_pushChunkLongTailOldLongClearReachReturnWordSplit
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          ((sstoreAccountMap I.codeOwner σ ⟨1⟩
            (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD
                (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
    let slot : UInt256 := chunksDataBase + oldLen
    let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σLen
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
    let σ' : AccountMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
            (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
          (BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32))
          (BytesStoreLiteCore.longDataTailMaskedWord
            (bytesStoreLiteCalldataLongDataWord I payloadStart
              (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
              0) len))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨263⟩
      [(σ'.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)),
        bytesStoreLiteSelWord I]
      (wordAt0Mem slot (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ') k C := by
  dsimp only
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
  let slot : UInt256 := chunksDataBase + oldLen
  let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σLen
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
  let σ' : AccountMap :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
          (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
        (BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32))
        (BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
            0) len))
      slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  have hbranch := bytesStoreLiteX_pushChunkLongHeaderClearReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (oldStoredLen := oldStoredLen)
    hperm hreach hlenMax hflag holdStoredLen hvalid hgtOldNew hlong
  have hwrite := bytesStoreLiteX_writeBytesNewLongTailFromWriteBranchSplit
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (τ := σClear) (slot := slot) (payloadStart := payloadStart) (len := len)
    (ret := ⟨1617⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    hperm
    (by simpa [oldLen, slot, σLen, σClear] using hbranch)
    hlong htailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hret := bytesStoreLiteX_pushChunkReturnFromHelperRetSplit
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := σ') (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (slot := slot) (payloadStart := payloadStart) (len := len)
    (sel := bytesStoreLiteSelWord I)
    (mem := wordAt0Mem slot (wordAt0Mem slot
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
    (aw := BytesStoreLiteCore.clearCurrentHashAw
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)))
    (rdata := ByteArray.empty)
    (by simpa [oldLen, slot, σLen, σClear, σ'] using hwrite)
  simpa [oldLen, slot, σLen, σClear, σ', bytesStoreLiteClearCurrentHashAw3] using hret

theorem bytesStoreLiteX_pushChunkLongTailOldLongClearReturnsSplit
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          ((sstoreAccountMap I.codeOwner σ ⟨1⟩
            (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD
                (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
    let slot : UInt256 := chunksDataBase + oldLen
    let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σLen
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
    let σ' : AccountMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
            (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
          (BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32))
          (BytesStoreLiteCore.longDataTailMaskedWord
            (bytesStoreLiteCalldataLongDataWord I payloadStart
              (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
              0) len))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
      (UInt256.toByteArray
        (σ'.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩))) := by
  dsimp only
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
  let slot : UInt256 := chunksDataBase + oldLen
  let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σLen
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
  let σ' : AccountMap :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
          (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
        (BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32))
        (BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
            0) len))
      slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  exact bytesStoreLiteX_returnWord263OfMemState
    (mem := wordAt0Mem slot (wordAt0Mem slot
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
    (wordAt0Mem_size_96 slot
      (wordAt0Mem_size_96 slot
        (wordAt0Mem_size_96 (⟨1⟩ : UInt256) solcFreePtrMem_size)))
    (bytesStoreLiteWordAt0Mem_wordAt0Mem_wordAt0Mem_read64 slot)
    (by
      simpa [oldLen, slot, σLen, σClear, σ'] using
        bytesStoreLiteX_pushChunkLongTailOldLongClearReachReturnWordSplit
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) (len := len) (payloadStart := payloadStart)
          (oldStoredLen := oldStoredLen)
          hperm hreach hlenMax hflag holdStoredLen hvalid hgtOldNew hlong htailMod)

theorem bytesStoreLiteX_pushChunkLongNoTailOldLongNoClearReachReturnWordSplit
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          ((sstoreAccountMap I.codeOwner σ ⟨1⟩
            (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD
                (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
    let slot : UInt256 := chunksDataBase + oldLen
    let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
    let σ' : AccountMap :=
      sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σLen
          (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨263⟩
      [(σ'.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)),
        bytesStoreLiteSelWord I]
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ') k C := by
  dsimp only
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
  let slot : UInt256 := chunksDataBase + oldLen
  let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
  let σ' : AccountMap :=
    sstoreAccountMap I.codeOwner
      (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σLen
        (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
      slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  have hbranch := bytesStoreLiteX_pushChunkLongHeaderNoClearReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (oldStoredLen := oldStoredLen)
    hperm hreach hlenMax hflag holdStoredLen hvalid hgtOldNew
  have hwrite := bytesStoreLiteX_writeBytesNewLongNoTailFromWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (τ := σLen) (slot := slot) (payloadStart := payloadStart) (len := len)
    (ret := ⟨1617⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty)
    hperm
    (by simpa [oldLen, slot, σLen] using hbranch)
    hlong hnoTailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hret := bytesStoreLiteX_pushChunkReturnFromHelperRetSplit
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := σ') (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (slot := slot) (payloadStart := payloadStart) (len := len)
    (sel := bytesStoreLiteSelWord I)
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [oldLen, slot, σLen, σ'] using hwrite)
  simpa [oldLen, slot, σLen, σ', bytesStoreLiteClearCurrentHashAw3] using hret

theorem bytesStoreLiteX_pushChunkLongNoTailReturnsSplit
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
    let slot : UInt256 := chunksDataBase + oldLen
    let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
    let σ' : AccountMap :=
      sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σLen
          (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
      (UInt256.toByteArray
        (σ'.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩))) := by
  dsimp only
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
  let slot : UInt256 := chunksDataBase + oldLen
  let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
  let σ' : AccountMap :=
    sstoreAccountMap I.codeOwner
      (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σLen
        (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
      slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  exact bytesStoreLiteX_returnWord263OfMemState
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (wordAt0Mem_size_96 slot
      (wordAt0Mem_size_96 (⟨1⟩ : UInt256) solcFreePtrMem_size))
    (bytesStoreLiteWordAt0Mem_wordAt0Mem_read64 slot)
    (by
      simpa [oldLen, slot, σLen, σ'] using
        bytesStoreLiteX_pushChunkLongNoTailReachReturnWordSplit
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) (len := len) (payloadStart := payloadStart)
          hperm hreach hlenMax hflag hvalid hlong hnoTailMod)

theorem bytesStoreLiteX_pushChunkLongNoTailOldLongNoClearReturnsSplit
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          ((sstoreAccountMap I.codeOwner σ ⟨1⟩
            (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD
                (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
    let slot : UInt256 := chunksDataBase + oldLen
    let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
    let σ' : AccountMap :=
      sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σLen
          (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
      (UInt256.toByteArray
        (σ'.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩))) := by
  dsimp only
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
  let slot : UInt256 := chunksDataBase + oldLen
  let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
  let σ' : AccountMap :=
    sstoreAccountMap I.codeOwner
      (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σLen
        (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
      slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  exact bytesStoreLiteX_returnWord263OfMemState
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (wordAt0Mem_size_96 slot
      (wordAt0Mem_size_96 (⟨1⟩ : UInt256) solcFreePtrMem_size))
    (bytesStoreLiteWordAt0Mem_wordAt0Mem_read64 slot)
    (by
      simpa [oldLen, slot, σLen, σ'] using
        bytesStoreLiteX_pushChunkLongNoTailOldLongNoClearReachReturnWordSplit
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) (len := len) (payloadStart := payloadStart)
          (oldStoredLen := oldStoredLen)
          hperm hreach hlenMax hflag holdStoredLen hvalid hgtOldNew hlong hnoTailMod)

theorem bytesStoreLiteX_pushChunkLongTailReachReturnWordSplit
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
    let slot : UInt256 := chunksDataBase + oldLen
    let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
    let σ' : AccountMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σLen
            (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
          (BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32))
          (BytesStoreLiteCore.longDataTailMaskedWord
            (bytesStoreLiteCalldataLongDataWord I payloadStart
              (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
              0) len))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨263⟩
      [(σ'.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)),
        bytesStoreLiteSelWord I]
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ') k C := by
  dsimp only
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
  let slot : UInt256 := chunksDataBase + oldLen
  let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
  let σ' : AccountMap :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σLen
          (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
        (BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32))
        (BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
            0) len))
      slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  have hbranch := bytesStoreLiteX_pushChunkShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart)
    hperm hreach hlenMax hflag hvalid
  have hwrite := bytesStoreLiteX_writeBytesNewLongTailFromWriteBranchSplit
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (τ := σLen) (slot := slot) (payloadStart := payloadStart) (len := len)
    (ret := ⟨1617⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty)
    hperm
    (by simpa [oldLen, slot, σLen] using hbranch)
    hlong htailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hret := bytesStoreLiteX_pushChunkReturnFromHelperRetSplit
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := σ') (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (slot := slot) (payloadStart := payloadStart) (len := len)
    (sel := bytesStoreLiteSelWord I)
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [oldLen, slot, σLen, σ'] using hwrite)
  simpa [oldLen, slot, σLen, σ', bytesStoreLiteClearCurrentHashAw3] using hret

theorem bytesStoreLiteX_pushChunkLongTailOldLongNoClearReachReturnWordSplit
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          ((sstoreAccountMap I.codeOwner σ ⟨1⟩
            (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD
                (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
    let slot : UInt256 := chunksDataBase + oldLen
    let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
    let σ' : AccountMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σLen
            (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
          (BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32))
          (BytesStoreLiteCore.longDataTailMaskedWord
            (bytesStoreLiteCalldataLongDataWord I payloadStart
              (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
              0) len))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨263⟩
      [(σ'.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)),
        bytesStoreLiteSelWord I]
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ') k C := by
  dsimp only
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
  let slot : UInt256 := chunksDataBase + oldLen
  let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
  let σ' : AccountMap :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σLen
          (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
        (BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32))
        (BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
            0) len))
      slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  have hbranch := bytesStoreLiteX_pushChunkLongHeaderNoClearReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (oldStoredLen := oldStoredLen)
    hperm hreach hlenMax hflag holdStoredLen hvalid hgtOldNew
  have hwrite := bytesStoreLiteX_writeBytesNewLongTailFromWriteBranchSplit
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (τ := σLen) (slot := slot) (payloadStart := payloadStart) (len := len)
    (ret := ⟨1617⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty)
    hperm
    (by simpa [oldLen, slot, σLen] using hbranch)
    hlong htailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hret := bytesStoreLiteX_pushChunkReturnFromHelperRetSplit
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := σ') (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (slot := slot) (payloadStart := payloadStart) (len := len)
    (sel := bytesStoreLiteSelWord I)
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [oldLen, slot, σLen, σ'] using hwrite)
  simpa [oldLen, slot, σLen, σ', bytesStoreLiteClearCurrentHashAw3] using hret

theorem bytesStoreLiteX_pushChunkLongTailReturnsSplit
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ ⟨1⟩
                  (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
    let slot : UInt256 := chunksDataBase + oldLen
    let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
    let σ' : AccountMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σLen
            (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
          (BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32))
          (BytesStoreLiteCore.longDataTailMaskedWord
            (bytesStoreLiteCalldataLongDataWord I payloadStart
              (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
              0) len))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
      (UInt256.toByteArray
        (σ'.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩))) := by
  dsimp only
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
  let slot : UInt256 := chunksDataBase + oldLen
  let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
  let σ' : AccountMap :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σLen
          (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
        (BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32))
        (BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
            0) len))
      slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  exact bytesStoreLiteX_returnWord263OfMemState
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (wordAt0Mem_size_96 slot
      (wordAt0Mem_size_96 (⟨1⟩ : UInt256) solcFreePtrMem_size))
    (bytesStoreLiteWordAt0Mem_wordAt0Mem_read64 slot)
    (by
      simpa [oldLen, slot, σLen, σ'] using
        bytesStoreLiteX_pushChunkLongTailReachReturnWordSplit
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) (len := len) (payloadStart := payloadStart)
          hperm hreach hlenMax hflag hvalid hlong htailMod)

theorem bytesStoreLiteX_pushChunkLongTailOldLongNoClearReturnsSplit
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          ((sstoreAccountMap I.codeOwner σ ⟨1⟩
            (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD
                (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
    let slot : UInt256 := chunksDataBase + oldLen
    let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
    let σ' : AccountMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σLen
            (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
          (BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32))
          (BytesStoreLiteCore.longDataTailMaskedWord
            (bytesStoreLiteCalldataLongDataWord I payloadStart
              (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
              0) len))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
      (UInt256.toByteArray
        (σ'.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩))) := by
  dsimp only
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ I
  let slot : UInt256 := chunksDataBase + oldLen
  let σLen : AccountMap := sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)
  let σ' : AccountMap :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σLen
          (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
        (BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32))
        (BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
            0) len))
      slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  exact bytesStoreLiteX_returnWord263OfMemState
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (wordAt0Mem_size_96 slot
      (wordAt0Mem_size_96 (⟨1⟩ : UInt256) solcFreePtrMem_size))
    (bytesStoreLiteWordAt0Mem_wordAt0Mem_read64 slot)
    (by
      simpa [oldLen, slot, σLen, σ'] using
        bytesStoreLiteX_pushChunkLongTailOldLongNoClearReachReturnWordSplit
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) (len := len) (payloadStart := payloadStart)
          (oldStoredLen := oldStoredLen)
          hperm hreach hlenMax hflag holdStoredLen hvalid hgtOldNew hlong htailMod)


end BytesStoreLite
