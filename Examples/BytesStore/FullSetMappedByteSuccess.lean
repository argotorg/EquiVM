import Examples.BytesStore.FullSetMappedByte

/-!
# BytesStore — `setMappedByte(uint256,uint256,uint8)` success paths

Successful writes are split from the decoder/revert layer so the mapped-byte proof can be
iterated independently from the already-stable malformed and bounds cases.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace BytesStore

theorem bytesStoreSetMappedByteLongBaseHashMem (I : ExecutionEnv) (mem : ByteArray) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((wordAt0Mem (bytesStoreSetMappedByteSlot I) mem).readWithPadding 0 32))) =
      bytesLikeDataBase (bytesStoreSetMappedByteSlot I) := by
  rw [wordAt0Mem_read0]
  simpa [bytesLikeDataBase] using
    keccakSlot_eq (UInt256.toByteArray (bytesStoreSetMappedByteSlot I))

theorem bytesStoreSetMappedByteSlotHashMem (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ mem
          ).readWithPadding 0 64))) =
      bytesStoreSetMappedByteSlot I := by
  rw [twoWordHashMem_read0_64 (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ hmem]
  unfold bytesStoreSetMappedByteSlot bytesStoreSetMappedSlotOf mappedValueSlot
  rw [keyValueToWord_uint256]
  exact mappingSlot_single (bytesStoreSetMappedByteKeyWord I) ⟨4⟩

theorem bytesStoreX_setMappedByteShortReachStoreCommon {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨805⟩
      [len, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
        UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨848⟩
      [bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
        UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd805⟩ := hreach
  have hlt : UInt256.lt (bytesStoreSetMappedByteIndexWord I) len = ⟨1⟩ :=
    ult_one hbound
  have rd819 := evm_run rd805 with [
    jumpdest, dup2, lt, push2 ⟨819⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd821 := evm_run rd819 with [jumpdest, dup2]
  obtain ⟨_, _, rd822₀⟩ := rd821.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd822⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨822⟩
        [bytesStoreSetMappedByteHeaderWord σ I, bytesStoreSetMappedByteIndexWord I,
          bytesStoreSetMappedByteSlot I,
          UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
          bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreSetMappedByteHeaderWord, initState] using rd822₀⟩
  have rd848 := evm_run rd822 with [
    push1 ⟨1⟩, and, iszero, push2 ⟨848⟩,
    jumpiT (by
      rw [u256_land_comm, hflag]
      decide)
      (by native_decide)]
  exact ⟨_, _, rd848⟩

theorem bytesStoreX_setMappedByteLongReachStoreCommon {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨805⟩
      [len, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
        UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨848⟩
      [bytesStoreSetMappedByteLongWordIndex I, bytesStoreSetMappedByteLongDataSlot I,
        UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      (wordAt0Mem (bytesStoreSetMappedByteSlot I)
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd805⟩ := hreach
  have hlt : UInt256.lt (bytesStoreSetMappedByteIndexWord I) len = ⟨1⟩ :=
    ult_one hbound
  have hflagOne :
      UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩ = ⟨1⟩ :=
    u256_land_one_eq_one_of_ne_zero hflag
  have hslot := bytesStoreSetMappedByteLongBaseHashMem I
    (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
  have rd819 := evm_run rd805 with [
    jumpdest, dup2, lt, push2 ⟨819⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd821 := evm_run rd819 with [jumpdest, dup2]
  obtain ⟨_, _, rd822₀⟩ := rd821.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd822⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨822⟩
        [bytesStoreSetMappedByteHeaderWord σ I, bytesStoreSetMappedByteIndexWord I,
          bytesStoreSetMappedByteSlot I,
          UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
          bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreSetMappedByteHeaderWord, initState] using rd822₀⟩
  have rd847 := evm_run rd822 with [
    push1 ⟨1⟩, and, iszero, push2 ⟨848⟩,
    jumpiNT (by
      rw [u256_land_comm, hflagOne]
      decide),
    swap1, push0,
    raw mstore 0 (wordAt0Mem (bytesStoreSetMappedByteSlot I)
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem))
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256 0 (bytesLikeDataBase (bytesStoreSetMappedByteSlot I))
      (UInt256.ofNat 3)
      (by native_decide) mem_cost hslot (by native_decide) (by evm_ov),
    swap1, push1 ⟨32⟩, swap2, dup3, dup3, div, add, swap2, swap1]
  have rd848raw := RD.mod rd847 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa [bytesStoreSetMappedByteLongWordIndex,
      bytesStoreSetMappedByteLongDataSlot,
      u256_add_comm (UInt256.div (bytesStoreSetMappedByteIndexWord I) ⟨32⟩)
        (bytesLikeDataBase (bytesStoreSetMappedByteSlot I))] using rd848raw⟩

theorem bytesStoreX_setMappedByteShortStore {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨848⟩
      [bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
        UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨877⟩
      [⟨0⟩, bytesStoreSetMappedByteValueWord I,
        bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteKeyWord I,
        ⟨301⟩, bytesStoreSelWord I]
      (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteSlot I)
        (bytesStoreSetMappedByteShortStoredWord σ I)) k C := by
  obtain ⟨_, _, rd848⟩ := hreach
  have rd857 := evm_run rd848 with [
    jumpdest, push1 ⟨31⟩, sub, push2 ⟨256⟩, exp, dup2]
  obtain ⟨_, _, rd858₀⟩ := rd857.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd858⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨858⟩
        [bytesStoreSetMappedByteHeaderWord σ I,
          UInt256.exp ⟨256⟩ (UInt256.sub ⟨31⟩
            (bytesStoreSetMappedByteIndexWord I)),
          bytesStoreSetMappedByteSlot I,
          UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
          bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreSetMappedByteHeaderWord, initState] using rd858₀⟩
  have rd875 := evm_run rd858 with [
    dup2, push1 ⟨255⟩, mul, not, and, swap1,
    push1 ⟨1⟩, push1 ⟨248⟩, shl, dup5, div, mul, lor, swap1]
  obtain ⟨_, _, rd875'⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨875⟩
        [bytesStoreSetMappedByteSlot I,
          bytesStoreSetMappedByteShortStoredWord σ I,
          UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
          bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreSetMappedByteShortStoredWord,
        bytesStoreSetMappedByteShortScale] using rd875⟩
  obtain ⟨_, _, rd876₀⟩ := rd875'.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd876⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨876⟩
        [UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
          bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteSlot I)
          (bytesStoreSetMappedByteShortStoredWord σ I)) k C := by
    exact ⟨_, _, by simpa [sstoreAccountMap, initState] using rd876₀⟩
  exact ⟨_, _, evm_run rd876 with [pop]⟩

theorem bytesStoreX_setMappedByteLongStore {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨848⟩
      [bytesStoreSetMappedByteLongWordIndex I, bytesStoreSetMappedByteLongDataSlot I,
        UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      (wordAt0Mem (bytesStoreSetMappedByteSlot I)
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨877⟩
      [⟨0⟩, bytesStoreSetMappedByteValueWord I,
        bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteKeyWord I,
        ⟨301⟩, bytesStoreSelWord I]
      (wordAt0Mem (bytesStoreSetMappedByteSlot I)
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
        (bytesStoreSetMappedByteLongStoredWord σ I)) k C := by
  obtain ⟨_, _, rd848⟩ := hreach
  have rd857 := evm_run rd848 with [
    jumpdest, push1 ⟨31⟩, sub, push2 ⟨256⟩, exp, dup2]
  obtain ⟨_, _, rd858₀⟩ := rd857.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd858⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨858⟩
        [bytesStoreSetMappedByteLongOldWord σ I,
          UInt256.exp ⟨256⟩ (UInt256.sub ⟨31⟩
            (bytesStoreSetMappedByteLongWordIndex I)),
          bytesStoreSetMappedByteLongDataSlot I,
          UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
          bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
        (wordAt0Mem (bytesStoreSetMappedByteSlot I)
          (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem))
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreSetMappedByteLongOldWord, initState] using rd858₀⟩
  have rd875 := evm_run rd858 with [
    dup2, push1 ⟨255⟩, mul, not, and, swap1,
    push1 ⟨1⟩, push1 ⟨248⟩, shl, dup5, div, mul, lor, swap1]
  obtain ⟨_, _, rd875'⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨875⟩
        [bytesStoreSetMappedByteLongDataSlot I,
          bytesStoreSetMappedByteLongStoredWord σ I,
          UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
          bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
        (wordAt0Mem (bytesStoreSetMappedByteSlot I)
          (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem))
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreSetMappedByteLongStoredWord,
        bytesStoreSetMappedByteLongScale] using rd875⟩
  obtain ⟨_, _, rd876₀⟩ := rd875'.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd876⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨876⟩
        [UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
          bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
        (wordAt0Mem (bytesStoreSetMappedByteSlot I)
          (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem))
        (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
          (bytesStoreSetMappedByteLongStoredWord σ I)) k C := by
    exact ⟨_, _, by simpa [sstoreAccountMap, initState] using rd876₀⟩
  exact ⟨_, _, evm_run rd876 with [pop]⟩

theorem bytesStoreX_setMappedByteReturnReachLengthDecoderMem
    {cA gh bl σinit σ σ₀ A I} {g : Sat256} {mem : ByteArray}
    (hmem : mem.size = 96)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨877⟩
      [⟨0⟩, bytesStoreSetMappedByteValueWord I,
        bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteKeyWord I,
        ⟨301⟩, bytesStoreSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      [bytesStoreSetMappedByteHeaderWord σ I, ⟨905⟩,
        bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I, ⟨0⟩,
        bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd877⟩ := hreach
  have hslot := bytesStoreSetMappedByteSlotHashMem (I := I) hmem
  have rd895 := evm_run rd877 with [
    push1 ⟨4⟩, push0, dup6, dup2,
    raw mstore 0 (wordAt0Mem (bytesStoreSetMappedByteKeyWord I) mem)
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, add, swap1, dup2,
    raw mstore 0
      (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ mem)
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, add, push0,
    raw keccak256 0 (bytesStoreSetMappedByteSlot I) (UInt256.ofNat 3)
      (by native_decide) mem_cost hslot (by native_decide) (by evm_ov),
    dup4, dup2]
  obtain ⟨_, _, rd897₀⟩ := rd895.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd897⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨897⟩
        [bytesStoreSetMappedByteHeaderWord σ I,
          bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I, ⟨0⟩,
          bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
          bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ mem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreSetMappedByteHeaderWord, initState] using rd897₀⟩
  exact ⟨_, _, evm_run rd897 with [
    push2 ⟨905⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreX_setMappedByteShortWriteReturnReachLengthDecoder
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨805⟩
      [len, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
        UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteSlot I)
            (bytesStoreSetMappedByteShortStoredWord σ I)) I,
        ⟨905⟩, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
        ⟨0⟩, bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteSlot I)
        (bytesStoreSetMappedByteShortStoredWord σ I)) k C := by
  have h848 := bytesStoreX_setMappedByteShortReachStoreCommon
    (g := g) hreach hbound hflag
  have h877 := bytesStoreX_setMappedByteShortStore
    (g := g) h848 hperm
  exact bytesStoreX_setMappedByteReturnReachLengthDecoderMem
    (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteSlot I)
      (bytesStoreSetMappedByteShortStoredWord σ I))
    (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
    h877

theorem bytesStoreX_setMappedByteLongWriteReturnReachLengthDecoder
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨805⟩
      [len, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
        UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ I)) I,
        ⟨905⟩, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
        ⟨0⟩, bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩
        (wordAt0Mem (bytesStoreSetMappedByteSlot I)
          (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
        (bytesStoreSetMappedByteLongStoredWord σ I)) k C := by
  have h848 := bytesStoreX_setMappedByteLongReachStoreCommon
    (g := g) hreach hbound hflag
  have h877 := bytesStoreX_setMappedByteLongStore
    (g := g) h848 hperm
  exact bytesStoreX_setMappedByteReturnReachLengthDecoderMem
    (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
      (bytesStoreSetMappedByteLongStoredWord σ I))
    (wordAt0Mem_size_96 _ (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
    h877

theorem bytesStoreX_setMappedByteShortWriteReturnDecodedLength
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨805⟩
      [len, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
        UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hflagPost : UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteSlot I)
            (bytesStoreSetMappedByteShortStoredWord σ I)) I) ⟨1⟩ = ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteSlot I)
            (bytesStoreSetMappedByteShortStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStoreSetMappedByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteSlot I)
              (bytesStoreSetMappedByteShortStoredWord σ I)) I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨905⟩
      [UInt256.land (UInt256.div
          (bytesStoreSetMappedByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteSlot I)
              (bytesStoreSetMappedByteShortStoredWord σ I)) I) ⟨2⟩) ⟨127⟩,
        bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I, ⟨0⟩,
        bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteSlot I)
        (bytesStoreSetMappedByteShortStoredWord σ I)) k C := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteSlot I)
    (bytesStoreSetMappedByteShortStoredWord σ I)
  have hdec := bytesStoreX_setMappedByteShortWriteReturnReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag hperm
  have hdecoded := bytesStoreX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := bytesStoreSetMappedByteHeaderWord σ' I) (ret := ⟨905⟩)
    (rest := [bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
      ⟨0⟩, bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
      bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I])
    (mem := twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩
      (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [σ'] using hdec)
    (by simpa [σ'] using hflagPost)
    (by simpa [σ'] using hvalidPost)
    (by native_decide)
    (by simp)
  simpa [σ'] using hdecoded

theorem bytesStoreX_setMappedByteLongWriteReturnDecodedLength
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨805⟩
      [len, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
        UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hflagPost : UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreSetMappedByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
              (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨905⟩
      [UInt256.div
          (bytesStoreSetMappedByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
              (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨2⟩,
        bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I, ⟨0⟩,
        bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩
        (wordAt0Mem (bytesStoreSetMappedByteSlot I)
          (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
        (bytesStoreSetMappedByteLongStoredWord σ I)) k C := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
    (bytesStoreSetMappedByteLongStoredWord σ I)
  have hdec := bytesStoreX_setMappedByteLongWriteReturnReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag hperm
  have hdecoded := bytesStoreX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := bytesStoreSetMappedByteHeaderWord σ' I) (ret := ⟨905⟩)
    (rest := [bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
      ⟨0⟩, bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
      bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I])
    (mem := twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩
      (wordAt0Mem (bytesStoreSetMappedByteSlot I)
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [σ'] using hdec)
    (by simpa [σ'] using hflagPost)
    (by simpa [σ'] using hvalidPost)
    (by native_decide)
    (by simp)
  simpa [σ'] using hdecoded

theorem bytesStoreX_setMappedByteLongWriteReturnDecodedPostLongLength
    {cA gh bl σ σ₀ A I} {g : Sat256} {len lenPost : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨805⟩
      [len, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
        UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hlenPost : lenPost = UInt256.div
      (bytesStoreSetMappedByteHeaderWord
        (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
          (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨2⟩)
    (hflagPost : UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreSetMappedByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
              (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨905⟩
      [lenPost, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I, ⟨0⟩,
        bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩
        (wordAt0Mem (bytesStoreSetMappedByteSlot I)
          (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
        (bytesStoreSetMappedByteLongStoredWord σ I)) k C := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
    (bytesStoreSetMappedByteLongStoredWord σ I)
  have hdec := bytesStoreX_setMappedByteLongWriteReturnReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag hperm
  have hdecoded := bytesStoreX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := bytesStoreSetMappedByteHeaderWord σ' I) (ret := ⟨905⟩)
    (rest := [bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
      ⟨0⟩, bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
      bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I])
    (mem := twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩
      (wordAt0Mem (bytesStoreSetMappedByteSlot I)
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [σ'] using hdec)
    (by simpa [σ'] using hflagPost)
    (by simpa [σ'] using hvalidPost)
    (by native_decide)
    (by simp)
  simpa [σ', hlenPost] using hdecoded

theorem bytesStoreX_setMappedByteLongWriteReturnDecodedShortLength
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨805⟩
      [len, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
        UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hflagPost : UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨1⟩ = ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStoreSetMappedByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
              (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨905⟩
      [UInt256.land (UInt256.div
          (bytesStoreSetMappedByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
              (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨2⟩) ⟨127⟩,
        bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I, ⟨0⟩,
        bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩
        (wordAt0Mem (bytesStoreSetMappedByteSlot I)
          (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
        (bytesStoreSetMappedByteLongStoredWord σ I)) k C := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
    (bytesStoreSetMappedByteLongStoredWord σ I)
  have hdec := bytesStoreX_setMappedByteLongWriteReturnReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag hperm
  have hdecoded := bytesStoreX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := bytesStoreSetMappedByteHeaderWord σ' I) (ret := ⟨905⟩)
    (rest := [bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
      ⟨0⟩, bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
      bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I])
    (mem := twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩
      (wordAt0Mem (bytesStoreSetMappedByteSlot I)
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [σ'] using hdec)
    (by simpa [σ'] using hflagPost)
    (by simpa [σ'] using hvalidPost)
    (by native_decide)
    (by simp)
  simpa [σ'] using hdecoded

theorem bytesStoreX_setMappedByteLongWriteReturnLongMalformed
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨805⟩
      [len, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
        UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hflagPost : UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hbadPost : UInt256.sub (UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreSetMappedByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
              (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨2⟩) ⟨32⟩) = ⟨0⟩)
    (hperm : I.perm = true) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
    (bytesStoreSetMappedByteLongStoredWord σ I)
  have hdec := bytesStoreX_setMappedByteLongWriteReturnReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag hperm
  exact bytesStoreX_bytesLengthDecoderLongMalformedMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := bytesStoreSetMappedByteHeaderWord σ' I) (ret := ⟨905⟩)
    (rest := [bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
      ⟨0⟩, bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
      bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I])
    (mem := twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩
      (wordAt0Mem (bytesStoreSetMappedByteSlot I)
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)))
    (by simpa [σ'] using hdec)
    (by simpa [σ'] using hflagPost)
    (by simpa [σ'] using hbadPost)
    (by simp)

theorem bytesStoreX_setMappedByteLongWriteReturnShortMalformed
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨805⟩
      [len, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
        UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hflagPost : UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨1⟩ = ⟨0⟩)
    (hbadPost : UInt256.sub (UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStoreSetMappedByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
              (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨2⟩) ⟨127⟩) ⟨32⟩) =
          ⟨0⟩)
    (hperm : I.perm = true) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
    (bytesStoreSetMappedByteLongStoredWord σ I)
  have hdec := bytesStoreX_setMappedByteLongWriteReturnReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag hperm
  exact bytesStoreX_bytesLengthDecoderShortMalformedMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := bytesStoreSetMappedByteHeaderWord σ' I) (ret := ⟨905⟩)
    (rest := [bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
      ⟨0⟩, bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
      bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I])
    (mem := twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩
      (wordAt0Mem (bytesStoreSetMappedByteSlot I)
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)))
    (by simpa [σ'] using hdec)
    (by simpa [σ'] using hflagPost)
    (by simpa [σ'] using hbadPost)
    (by simp)

theorem bytesStoreX_setMappedByteShortReadReturnToWrapper
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len header : UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨905⟩
      [len, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I, ⟨0⟩,
        bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hheader :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreSetMappedByteSlot I) ⟨0⟩)) = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreSetMappedByteIndexWord I) header)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreSetMappedByteValueWord I) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨301⟩
      [bytesStoreSetMappedByteValueWord I, bytesStoreSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
  obtain ⟨_, _, rd905⟩ := hreach
  have hlt : UInt256.lt (bytesStoreSetMappedByteIndexWord I) len = ⟨1⟩ :=
    ult_one hbound
  have rd919 := evm_run rd905 with [
    jumpdest, dup2, lt, push2 ⟨919⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd921 := evm_run rd919 with [jumpdest, dup2]
  obtain ⟨_, _, rd922₀⟩ := rd921.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd922⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨922⟩
        [header, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
          ⟨0⟩, bytesStoreSetMappedByteValueWord I,
          bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteKeyWord I,
          ⟨301⟩, bytesStoreSelWord I]
        mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [initState, hheader] using rd922₀⟩
  have rd948 := evm_run rd922 with [
    push1 ⟨1⟩, and, iszero, push2 ⟨948⟩,
    jumpiT (by
      rw [u256_land_comm, hflag]
      decide)
      (by native_decide)]
  have rd950 := evm_run rd948 with [jumpdest, swap1]
  obtain ⟨_, _, rd951₀⟩ := rd950.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd951⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨951⟩
        [header, bytesStoreSetMappedByteIndexWord I, ⟨0⟩,
          bytesStoreSetMappedByteValueWord I,
          bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteKeyWord I,
          ⟨301⟩, bytesStoreSelWord I]
        mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [initState, hheader] using rd951₀⟩
  have rd957 := evm_run rd951 with [
    push1 ⟨1⟩, push1 ⟨248⟩, shl, swap2]
  have rd958 := RD.byte rd957 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd301 := evm_run rd958 with [
    mul, push1 ⟨248⟩, shr,
    swap5, swap4, pop, pop, pop, pop, jump (by native_decide)]
  exact ⟨_, _, by simpa [hbyte] using rd301⟩

theorem bytesStoreX_setMappedByteLongReadReturnToWrapper
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len header dataWord : UInt256}
    {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨905⟩
      [len, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I, ⟨0⟩,
        bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hheader :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreSetMappedByteSlot I) ⟨0⟩)) = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hdata :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreSetMappedByteLongDataSlot I) ⟨0⟩)) =
          dataWord)
    (hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreSetMappedByteLongWordIndex I) dataWord)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreSetMappedByteValueWord I) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨301⟩
      [bytesStoreSetMappedByteValueWord I, bytesStoreSelWord I]
      (wordAt0Mem (bytesStoreSetMappedByteSlot I) mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
  obtain ⟨_, _, rd905⟩ := hreach
  have hlt : UInt256.lt (bytesStoreSetMappedByteIndexWord I) len = ⟨1⟩ :=
    ult_one hbound
  have hflagOne : UInt256.land header ⟨1⟩ = ⟨1⟩ :=
    u256_land_one_eq_one_of_ne_zero hflag
  have hslot := bytesStoreSetMappedByteLongBaseHashMem I mem
  have rd919 := evm_run rd905 with [
    jumpdest, dup2, lt, push2 ⟨919⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd921 := evm_run rd919 with [jumpdest, dup2]
  obtain ⟨_, _, rd922₀⟩ := rd921.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd922⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨922⟩
        [header, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
          ⟨0⟩, bytesStoreSetMappedByteValueWord I,
          bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteKeyWord I,
          ⟨301⟩, bytesStoreSelWord I]
        mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [initState, hheader] using rd922₀⟩
  have rd947 := evm_run rd922 with [
    push1 ⟨1⟩, and, iszero, push2 ⟨948⟩,
    jumpiNT (by
      rw [u256_land_comm, hflagOne]
      decide),
    swap1, push0,
    raw mstore 0 (wordAt0Mem (bytesStoreSetMappedByteSlot I) mem)
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256 0 (bytesLikeDataBase (bytesStoreSetMappedByteSlot I))
      (UInt256.ofNat 3)
      (by native_decide) mem_cost hslot (by native_decide) (by evm_ov),
    swap1, push1 ⟨32⟩, swap2, dup3, dup3, div, add, swap2, swap1]
  have rd948raw := RD.mod rd947 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd948⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨948⟩
        [bytesStoreSetMappedByteLongWordIndex I,
          bytesStoreSetMappedByteLongDataSlot I, ⟨0⟩,
          bytesStoreSetMappedByteValueWord I,
          bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteKeyWord I,
          ⟨301⟩, bytesStoreSelWord I]
        (wordAt0Mem (bytesStoreSetMappedByteSlot I) mem)
        (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreSetMappedByteLongWordIndex,
        bytesStoreSetMappedByteLongDataSlot,
        u256_add_comm (UInt256.div (bytesStoreSetMappedByteIndexWord I) ⟨32⟩)
          (bytesLikeDataBase (bytesStoreSetMappedByteSlot I))] using rd948raw⟩
  have rd950 := evm_run rd948 with [jumpdest, swap1]
  obtain ⟨_, _, rd951₀⟩ := rd950.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd951⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨951⟩
        [dataWord, bytesStoreSetMappedByteLongWordIndex I, ⟨0⟩,
          bytesStoreSetMappedByteValueWord I,
          bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteKeyWord I,
          ⟨301⟩, bytesStoreSelWord I]
        (wordAt0Mem (bytesStoreSetMappedByteSlot I) mem)
        (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [initState, hdata] using rd951₀⟩
  have rd957 := evm_run rd951 with [
    push1 ⟨1⟩, push1 ⟨248⟩, shl, swap2]
  have rd958 := RD.byte rd957 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd301 := evm_run rd958 with [
    mul, push1 ⟨248⟩, shr,
    swap5, swap4, pop, pop, pop, pop, jump (by native_decide)]
  exact ⟨_, _, by simpa [hbyte] using rd301⟩

theorem bytesStoreX_setMappedBytePanic32MemFromReach
    {cA gh bl σinit σ σ₀ A I} {g : Sat256} {stk : List UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2579⟩ stk
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hov : stk.length + 3 ≤ 1024) :
    RDrev bytesStoreBytecode g (initState cA gh bl σinit σ₀ g A I) := by
  obtain ⟨_, _, rd2579⟩ := hreach
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
        bytesStoreFullPanicSelectorWord := by
    decide
  have rd2591₀ := evm_run rd2579 with [
    jumpdest, push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0]
  have rd2591 := rd2591₀
  rw [hsel] at rd2591
  exact evm_run rd2591 with [
    raw mstore 0 (bytesStoreFullPanic22Mem1From mem) (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨0x32⟩, push1 ⟨4⟩,
    raw mstore 0 (bytesStoreFullPanicMemFrom ⟨0x32⟩ mem) (UInt256.ofNat 3)
      (by native_decide)
      mem_cost
      (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨36⟩, push0,
    raw rev 0 (by native_decide) mem_cost
      (by evm_ov)]

theorem bytesStoreX_setMappedByteReturnOobLength
    {cA gh bl σinit σ σ₀ A I} {g : Sat256} {len : UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨905⟩
      [len, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I, ⟨0⟩,
        bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : ¬ (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat) :
    RDrev bytesStoreBytecode g (initState cA gh bl σinit σ₀ g A I) := by
  obtain ⟨_, _, rd905⟩ := hreach
  have hlt : UInt256.lt (bytesStoreSetMappedByteIndexWord I) len = ⟨0⟩ :=
    ult_zero (by omega)
  have rd2579 := evm_run rd905 with [
    jumpdest, dup2, lt, push2 ⟨919⟩,
    jumpiNT (by simpa using hlt),
    push2 ⟨919⟩, push2 ⟨2579⟩, jump (by native_decide)]
  exact bytesStoreX_setMappedBytePanic32MemFromReach ⟨_, _, rd2579⟩
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setMappedByteShortReadReturn
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len header : UInt256} {mem : ByteArray}
    (hsize : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨905⟩
      [len, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I, ⟨0⟩,
        bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hheader :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreSetMappedByteSlot I) ⟨0⟩)) = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreSetMappedByteIndexWord I) header)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreSetMappedByteValueWord I)
    (hcanon : UInt256.land (bytesStoreSetMappedByteValueWord I) ⟨255⟩ =
      bytesStoreSetMappedByteValueWord I) :
    RDret bytesStoreBytecode g (initState cA gh bl σinit σ₀ g A I) (cA, τ)
      (UInt256.toByteArray (bytesStoreSetMappedByteValueWord I)) := by
  have h301 := bytesStoreX_setMappedByteShortReadReturnToWrapper
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (τ := τ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := len) (header := header) (mem := mem)
    hreach hbound hheader hflag hbyte
  have hret := bytesStoreX_returnUInt8_301OfMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ := τ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := bytesStoreSetMappedByteValueWord I)
    (mem := mem) hsize hread64 h301
  simpa [hcanon] using hret

theorem bytesStoreX_setMappedByteLongReadReturn
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len header dataWord : UInt256}
    {mem : ByteArray}
    (hsize : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨905⟩
      [len, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I, ⟨0⟩,
        bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hheader :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreSetMappedByteSlot I) ⟨0⟩)) = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hdata :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreSetMappedByteLongDataSlot I) ⟨0⟩)) =
          dataWord)
    (hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreSetMappedByteLongWordIndex I) dataWord)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreSetMappedByteValueWord I)
    (hcanon : UInt256.land (bytesStoreSetMappedByteValueWord I) ⟨255⟩ =
      bytesStoreSetMappedByteValueWord I) :
    RDret bytesStoreBytecode g (initState cA gh bl σinit σ₀ g A I) (cA, τ)
      (UInt256.toByteArray (bytesStoreSetMappedByteValueWord I)) := by
  have h301 := bytesStoreX_setMappedByteLongReadReturnToWrapper
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (τ := τ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := len) (header := header)
    (dataWord := dataWord) (mem := mem) hreach hbound hheader hflag hdata hbyte
  have hret := bytesStoreX_returnUInt8_301OfMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ := τ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := bytesStoreSetMappedByteValueWord I)
    (mem := wordAt0Mem (bytesStoreSetMappedByteSlot I) mem)
    (wordAt0Mem_size_96 _ hsize)
    (bytesStoreWordAt0Mem_read64 _ hsize hread64)
    h301
  simpa [hcanon] using hret

theorem bytesStoreX_setMappedByteShortSuccessReturn
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256} {acc : Account}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨772⟩
      [bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len =
      UInt256.land (UInt256.div (bytesStoreSetMappedByteHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetMappedByteHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hacc : σ.find? I.codeOwner = some acc) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteSlot I)
        (bytesStoreSetMappedByteShortStoredWord σ I))
      (UInt256.toByteArray (bytesStoreSetMappedByteValueWord I)) := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteSlot I)
    (bytesStoreSetMappedByteShortStoredWord σ I)
  have hdec := bytesStoreX_setMappedByteReachLengthDecoder (g := g) hreach
  have h805Raw := bytesStoreX_bytesLengthDecoderShortValidMem
    (A := A) (I := I) (g := g) hdec hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h805 :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨805⟩
        [len, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
          UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
          bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    simpa [hlen] using h805Raw
  have hheaderPost :
      bytesStoreSetMappedByteHeaderWord σ' I =
        bytesStoreSetMappedByteShortStoredWord σ I := by
    dsimp [σ', bytesStoreSetMappedByteHeaderWord]
    exact sstoreAccountMap_storage_findD_self_of_find_some_any σ I.codeOwner acc
      (bytesStoreSetMappedByteSlot I)
      (bytesStoreSetMappedByteShortStoredWord σ I) hacc
  have hflagPost :
      UInt256.land (bytesStoreSetMappedByteHeaderWord σ' I) ⟨1⟩ = ⟨0⟩ := by
    rw [hheaderPost, bytesStoreSetMappedByteShortStoredWord_flag_eq
      (σ := σ) (I := I) (len := len) hshort hbound, hflag]
  have hltLen : UInt256.lt len ⟨32⟩ = ⟨1⟩ := by
    exact ult_one (by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
  have hvalidLen : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hltLen]
    native_decide
  have hlenPost :
      UInt256.land (UInt256.div (bytesStoreSetMappedByteHeaderWord σ' I) ⟨2⟩) ⟨127⟩ =
        len := by
    rw [hheaderPost, bytesStoreSetMappedByteShortStoredWord_shortLen_eq
      (σ := σ) (I := I) (len := len) hshort hbound]
    exact hlen.symm
  have hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreSetMappedByteHeaderWord σ' I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStoreSetMappedByteHeaderWord σ' I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflagPost, hlenPost] using hvalidLen
  have hreadRaw := bytesStoreX_setMappedByteShortWriteReturnDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) h805 hbound hflag
    (by simpa [σ'] using hflagPost)
    (by simpa [σ'] using hvalidPost)
    hperm
  have hread :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨905⟩
        [len, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I, ⟨0⟩,
          bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
          bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩
          (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem))
        (UInt256.ofNat 3) ByteArray.empty (cA, σ') k C := by
    simpa [σ', hlenPost] using hreadRaw
  have hheader :
      ((σ'.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreSetMappedByteSlot I) ⟨0⟩)) =
          bytesStoreSetMappedByteShortStoredWord σ I := by
    simpa [σ'] using
      sstoreAccountMap_storage_findD_self_of_find_some_any σ I.codeOwner acc
        (bytesStoreSetMappedByteSlot I)
        (bytesStoreSetMappedByteShortStoredWord σ I) hacc
  have hbyteAt :
      UInt256.byteAt (bytesStoreSetMappedByteIndexWord I)
          (bytesStoreSetMappedByteShortStoredWord σ I) =
        bytesStoreSetMappedByteValueWord I :=
    bytesStoreSetMappedByteShortStoredWord_byteAt
      (σ := σ) (I := I) (len := len) hcanon hshort hbound
  have hbyte :
      UInt256.shiftRight
        (UInt256.mul
          (UInt256.byteAt (bytesStoreSetMappedByteIndexWord I)
            (bytesStoreSetMappedByteShortStoredWord σ I))
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreSetMappedByteValueWord I := by
    rw [hbyteAt]
    exact bytesStoreSetMappedByteValueHighMulShiftRight hcanon
  have hret := bytesStoreX_setMappedByteShortReadReturn
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := len)
    (header := bytesStoreSetMappedByteShortStoredWord σ I)
    (mem := twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩
      (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem))
    (twoWordHashMem_size_96 _ _
      (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
    (twoWordHashMem_read64 _ _
      (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
      (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64))
    hread hbound hheader
    (by simpa [hheaderPost] using hflagPost)
    hbyte
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  simpa [σ'] using hret

theorem bytesStoreX_setMappedByteLongSuccessReturn_of_post_header
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256} {acc : Account}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨772⟩
      [bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreSetMappedByteHeaderWord σ I) ⟨2⟩)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetMappedByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
      ⟨0⟩)
    (hlenPost : len = UInt256.div
      (bytesStoreSetMappedByteHeaderWord
        (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
          (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨2⟩)
    (hflagPost : UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreSetMappedByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
              (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hheaderPost :
      bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ I)) I =
        bytesStoreSetMappedByteHeaderWord σ I)
    (hperm : I.perm = true)
    (hacc : σ.find? I.codeOwner = some acc) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
        (bytesStoreSetMappedByteLongStoredWord σ I))
      (UInt256.toByteArray (bytesStoreSetMappedByteValueWord I)) := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
    (bytesStoreSetMappedByteLongStoredWord σ I)
  have hdec := bytesStoreX_setMappedByteReachLengthDecoder (g := g) hreach
  have h805Raw := bytesStoreX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := g) hdec hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h805 :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨805⟩
        [len, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
          UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
          bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    simpa [hlen] using h805Raw
  have hreadRaw := bytesStoreX_setMappedByteLongWriteReturnDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) h805 hbound hflag
    (by simpa [σ'] using hflagPost)
    (by simpa [σ'] using hvalidPost)
    hperm
  have hread :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨905⟩
        [len, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I, ⟨0⟩,
          bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
          bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩
          (wordAt0Mem (bytesStoreSetMappedByteSlot I)
            (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)))
        (UInt256.ofNat 3) ByteArray.empty (cA, σ') k C := by
    simpa [σ', hlenPost] using hreadRaw
  have hheader :
      ((σ'.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreSetMappedByteSlot I) ⟨0⟩)) =
          bytesStoreSetMappedByteHeaderWord σ I := by
    simpa [σ', bytesStoreSetMappedByteHeaderWord] using hheaderPost
  have hdata :
      ((σ'.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreSetMappedByteLongDataSlot I) ⟨0⟩)) =
          bytesStoreSetMappedByteLongStoredWord σ I := by
    simpa [σ'] using
      sstoreAccountMap_storage_findD_self_of_find_some_any σ I.codeOwner acc
        (bytesStoreSetMappedByteLongDataSlot I)
        (bytesStoreSetMappedByteLongStoredWord σ I) hacc
  have hbyteAt :
      UInt256.byteAt (bytesStoreSetMappedByteLongWordIndex I)
          (bytesStoreSetMappedByteLongStoredWord σ I) =
        bytesStoreSetMappedByteValueWord I :=
    bytesStoreSetMappedByteLongStoredWord_byteAt (σ := σ) (I := I) hcanon
  have hbyte :
      UInt256.shiftRight
        (UInt256.mul
          (UInt256.byteAt (bytesStoreSetMappedByteLongWordIndex I)
            (bytesStoreSetMappedByteLongStoredWord σ I))
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreSetMappedByteValueWord I := by
    rw [hbyteAt]
    exact bytesStoreSetMappedByteValueHighMulShiftRight hcanon
  let readMem : ByteArray :=
    twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩
      (wordAt0Mem (bytesStoreSetMappedByteSlot I)
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem))
  have hreadMemSize : readMem.size = 96 := by
    exact twoWordHashMem_size_96 _ _
      (wordAt0Mem_size_96 _
        (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
  have hreadMem64 :
      readMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    exact twoWordHashMem_read64 _ _
      (wordAt0Mem_size_96 _
        (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
      (bytesStoreWordAt0Mem_read64 _
        (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
        (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64))
  have hret := bytesStoreX_setMappedByteLongReadReturn
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := len)
    (header := bytesStoreSetMappedByteHeaderWord σ I)
    (dataWord := bytesStoreSetMappedByteLongStoredWord σ I)
    (mem := readMem)
    hreadMemSize hreadMem64
    (by simpa [readMem] using hread)
    hbound hheader hflag hdata hbyte
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  simpa [σ', readMem] using hret

theorem bytesStoreX_setMappedByteLongLongSuccessReturn
    {cA gh bl σ σ₀ A I} {g : Sat256} {len lenPost : UInt256} {acc : Account}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨805⟩
      [len, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
        UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hlenPost : lenPost = UInt256.div
      (bytesStoreSetMappedByteHeaderWord
        (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
          (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨2⟩)
    (hflagPost : UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreSetMappedByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
              (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hboundPost : (bytesStoreSetMappedByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hacc : σ.find? I.codeOwner = some acc) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
        (bytesStoreSetMappedByteLongStoredWord σ I))
      (UInt256.toByteArray (bytesStoreSetMappedByteValueWord I)) := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
    (bytesStoreSetMappedByteLongStoredWord σ I)
  let header' : UInt256 :=
    Option.option ⟨0⟩
      (fun acc => Batteries.RBMap.findD acc.storage (bytesStoreSetMappedByteSlot I) ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  let dataWord' : UInt256 :=
    Option.option ⟨0⟩
      (fun acc =>
        Batteries.RBMap.findD acc.storage (bytesStoreSetMappedByteLongDataSlot I) ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  have hread := bytesStoreX_setMappedByteLongWriteReturnDecodedPostLongLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (lenPost := lenPost)
    hreach hbound hflag hlenPost hflagPost hvalidPost hperm
  have hheader : header' = bytesStoreSetMappedByteHeaderWord σ' I := by
    rfl
  have hdata : dataWord' = bytesStoreSetMappedByteLongStoredWord σ I := by
    simpa [dataWord', σ'] using
      sstoreAccountMap_storage_findD_self_of_find_some_any σ I.codeOwner acc
        (bytesStoreSetMappedByteLongDataSlot I)
        (bytesStoreSetMappedByteLongStoredWord σ I) hacc
  have hbyteAt :
      UInt256.byteAt (bytesStoreSetMappedByteLongWordIndex I) dataWord' =
        bytesStoreSetMappedByteValueWord I := by
    rw [hdata]
    exact bytesStoreSetMappedByteLongStoredWord_byteAt
      (σ := σ) (I := I) hcanon
  have hbyte :
      UInt256.shiftRight
        (UInt256.mul
          (UInt256.byteAt (bytesStoreSetMappedByteLongWordIndex I) dataWord')
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreSetMappedByteValueWord I := by
    rw [hbyteAt]
    exact bytesStoreSetMappedByteValueHighMulShiftRight hcanon
  let readMem : ByteArray :=
    twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩
      (wordAt0Mem (bytesStoreSetMappedByteSlot I)
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem))
  have hreadMemSize : readMem.size = 96 := by
    exact twoWordHashMem_size_96 _ _
      (wordAt0Mem_size_96 _
        (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
  have hreadMem64 :
      readMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    exact twoWordHashMem_read64 _ _
      (wordAt0Mem_size_96 _
        (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
      (bytesStoreWordAt0Mem_read64 _
        (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
        (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64))
  have hret := bytesStoreX_setMappedByteLongReadReturn
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := lenPost)
    (header := header') (dataWord := dataWord') (mem := readMem)
    hreadMemSize hreadMem64
    (by simpa [readMem] using hread)
    hboundPost
    hheader
    (by simpa [hheader, σ'] using hflagPost)
    (by rfl)
    hbyte
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  simpa [σ', readMem] using hret

theorem bytesStoreX_setMappedByteLongShortSuccessReturn
    {cA gh bl σ σ₀ A I} {g : Sat256} {len lenPost : UInt256} {acc : Account}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨805⟩
      [len, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
        UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
        bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
      (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hlenPost : lenPost = UInt256.land (UInt256.div
      (bytesStoreSetMappedByteHeaderWord
        (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
          (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨2⟩) ⟨127⟩)
    (hflagPost : UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨1⟩ = ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStoreSetMappedByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
              (bytesStoreSetMappedByteLongStoredWord σ I)) I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hboundPost : (bytesStoreSetMappedByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hacc : σ.find? I.codeOwner = some acc) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
        (bytesStoreSetMappedByteLongStoredWord σ I))
      (UInt256.toByteArray (bytesStoreSetMappedByteValueWord I)) := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedByteLongDataSlot I)
    (bytesStoreSetMappedByteLongStoredWord σ I)
  let header' : UInt256 :=
    Option.option ⟨0⟩
      (fun acc => Batteries.RBMap.findD acc.storage (bytesStoreSetMappedByteSlot I) ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  have hread := bytesStoreX_setMappedByteLongWriteReturnDecodedShortLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len)
    hreach hbound hflag hflagPost hvalidPost hperm
  have hheaderStored : header' = bytesStoreSetMappedByteLongStoredWord σ I := by
    by_cases hEq :
        bytesStoreSetMappedByteSlot I = bytesStoreSetMappedByteLongDataSlot I
    · simpa [header', σ', bytesStoreSetMappedByteHeaderWord, hEq] using
        sstoreAccountMap_storage_findD_self_of_find_some_any σ I.codeOwner acc
          (bytesStoreSetMappedByteLongDataSlot I)
          (bytesStoreSetMappedByteLongStoredWord σ I) hacc
    · have hheaderOld :
          bytesStoreSetMappedByteHeaderWord σ' I =
            bytesStoreSetMappedByteHeaderWord σ I := by
        simpa [σ', bytesStoreSetMappedByteHeaderWord,
          bytesStoreSetMappedByteLongDataSlot] using
          bytesStoreBytesHeaderWordAfterDataSstore_eq_of_before_of_ne
            (σ := σ) (I := I) (baseSlot := bytesStoreSetMappedByteSlot I)
            (idx := bytesStoreSetMappedByteIndexWord I)
            (val := bytesStoreSetMappedByteLongStoredWord σ I) hEq (by rfl)
      have hzeroOld :
          UInt256.land (bytesStoreSetMappedByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩ := by
        rw [← hheaderOld]
        simpa [σ', header', bytesStoreSetMappedByteHeaderWord] using hflagPost
      exact False.elim (hflag hzeroOld)
  have hvalid0 :
      UInt256.sub ⟨0⟩ (UInt256.lt lenPost ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlenPost, hflagPost] using hvalidPost
  have hshortPost : lenPost.toNat < 32 :=
    solidityShortBytesValid_lt32 hvalid0
  have hidxLt32 : (bytesStoreSetMappedByteIndexWord I).toNat < 32 :=
    lt_trans hboundPost hshortPost
  have hbyteAt :
      UInt256.byteAt (bytesStoreSetMappedByteIndexWord I) header' =
        bytesStoreSetMappedByteValueWord I := by
    rw [hheaderStored]
    exact bytesStoreSetMappedByteLongStoredWord_byteAt_index_of_lt32
      (σ := σ) (I := I) hcanon hidxLt32
  have hbyte :
      UInt256.shiftRight
        (UInt256.mul
          (UInt256.byteAt (bytesStoreSetMappedByteIndexWord I) header')
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreSetMappedByteValueWord I := by
    rw [hbyteAt]
    exact bytesStoreSetMappedByteValueHighMulShiftRight hcanon
  let readMem : ByteArray :=
    twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩
      (wordAt0Mem (bytesStoreSetMappedByteSlot I)
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem))
  have hreadMemSize : readMem.size = 96 := by
    exact twoWordHashMem_size_96 _ _
      (wordAt0Mem_size_96 _
        (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
  have hreadMem64 :
      readMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    exact twoWordHashMem_read64 _ _
      (wordAt0Mem_size_96 _
        (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
      (bytesStoreWordAt0Mem_read64 _
        (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
        (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64))
  have hret := bytesStoreX_setMappedByteShortReadReturn
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := lenPost) (header := header')
    (mem := readMem) hreadMemSize hreadMem64
    (by simpa [readMem, hlenPost] using hread) hboundPost (by rfl)
    (by simpa [header', σ'] using hflagPost) hbyte
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  simpa [σ', readMem] using hret

theorem bytesStoreSetMappedByteShortSuccessRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len =
      UInt256.land (UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetMappedByteSelector_size hsel
  have hreach := bytesStoreReachSetMappedByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨319⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetMappedByteEntryPc] using hreach
  have hreachBody := bytesStoreX_setMappedByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreDispatch_setMappedByte (cd := I.calldata)
    (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMappedByte (I := I) hsz100 hhi hcanon
  have hret := bytesStoreX_setMappedByteShortSuccessReturn
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len) (acc := accEvm)
    hreachBody hcanon hlen hshort hbound hflag hvalid hperm haccEvm
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreSetMappedByteSlot I)
    (bytesStoreSetMappedByteShortStoredWord σ_evm I)
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedByteSlot I) =
        bytesStoreSetMappedByteHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetMappedByteHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  obtain ⟨accSolm, haccSolm⟩ :=
    accountMapEquiv_find?_some_exists hAccounts haccEvm
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetMappedByteLocals I) setMappedByteTransition.body
        (.returned
          (bytesStoreSetMappedByteFrame I)
          evmSolm1 (some (bytesStoreSetMappedByteValue I))) := by
    simpa [evmSolm0, evmSolm1, initState, bytesStoreSetMappedByteFrame] using
      bytesStoreSetMappedByteShortBodyReturns
        (evm := evmSolm0) (σ := σ_evm) (I := I) (len := len) (acc := accSolm)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadHeader
        (by simpa [evmSolm0, initState] using haccSolm)
        hcanon hlen hshort hbound hflag hvalid
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteSlot I)
          (bytesStoreSetMappedByteShortStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simpa [evmSolm1, evmSolm0] using
      bytesStoreAccountMapEquiv_storageStore_initState
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreSetMappedByteSlot I)
        (bytesStoreSetMappedByteShortStoredWord σ_evm I)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    hpostAccounts
    (returnEquiv_of_encode (uint8ReturnEncoding (bytesStoreSetMappedByteValueWord I) hcanon))

theorem bytesStoreSetMappedByteLongSuccessRuntime_of_post_readback
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠
      ⟨0⟩)
    (hheaderPost :
      bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I =
        bytesStoreSetMappedByteHeaderWord σ_evm I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            I.codeOwner
            (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I))
          I.codeOwner
          (bytesStoreSetMappedByteSlot I) =
        bytesStoreSetMappedByteHeaderWord σ_evm I) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetMappedByteSelector_size hsel
  have hreach := bytesStoreReachSetMappedByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨319⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetMappedByteEntryPc] using hreach
  have hreachBody := bytesStoreX_setMappedByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreDispatch_setMappedByte (cd := I.calldata)
    (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMappedByte (I := I) hsz100 hhi hcanon
  have hret := bytesStoreX_setMappedByteLongSuccessReturn_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len) (acc := accEvm)
    hreachBody hcanon hlen hbound hflag hvalid
    (by simpa [hheaderPost] using hlen)
    (by simpa [hheaderPost] using hflag)
    (by simpa [hheaderPost] using hvalid)
    hheaderPost hperm haccEvm
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreSetMappedByteLongDataSlot I)
    (bytesStoreSetMappedByteLongStoredWord σ_evm I)
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedByteSlot I) =
        bytesStoreSetMappedByteHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetMappedByteHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadData :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedByteLongDataSlot I) =
        bytesStoreSetMappedByteLongOldWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetMappedByteLongData_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  obtain ⟨accSolm, haccSolm⟩ :=
    accountMapEquiv_find?_some_exists hAccounts haccEvm
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetMappedByteLocals I) setMappedByteTransition.body
        (.returned
          (bytesStoreSetMappedByteFrame I)
          evmSolm1 (some (bytesStoreSetMappedByteValue I))) := by
    simpa [evmSolm0, evmSolm1, initState, bytesStoreSetMappedByteFrame] using
      bytesStoreSetMappedByteLongBodyReturns_of_post_readback
        (evm := evmSolm0) (σ := σ_evm) (I := I) (len := len) (acc := accSolm)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadHeader hloadData
        (by
          simpa [evmSolm0, evmSolm1, initState, storageStore_executionEnv] using
            hloadHeaderPost)
        (by simpa [evmSolm0, initState] using haccSolm)
        hcanon hlen hbound hflag hvalid
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
          (bytesStoreSetMappedByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simpa [evmSolm1, evmSolm0] using
      bytesStoreAccountMapEquiv_storageStore_initState
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreSetMappedByteLongDataSlot I)
        (bytesStoreSetMappedByteLongStoredWord σ_evm I)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    hpostAccounts
    (returnEquiv_of_encode (uint8ReturnEncoding (bytesStoreSetMappedByteValueWord I) hcanon))

theorem bytesStoreSetMappedByteLongReturnLongSuccessRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len lenPost : UInt256}
    {accEvm : Account}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hlenPost : lenPost = UInt256.div
      (bytesStoreSetMappedByteHeaderWord
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
          (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I) ⟨2⟩)
    (hflagPost : UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreSetMappedByteHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
              (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hboundPost : (bytesStoreSetMappedByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠
      ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetMappedByteSelector_size hsel
  have hreach := bytesStoreReachSetMappedByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨319⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetMappedByteEntryPc] using hreach
  have hreachBody := bytesStoreX_setMappedByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hdecLen := bytesStoreX_setMappedByteReachLengthDecoder
    (g := Sat256.ofUInt256 g) hreachBody
  have h805Raw := bytesStoreX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hdecLen hflag hvalid
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have h805 :
      ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨805⟩
        [len, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
          UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
          bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [hlen] using h805Raw
  have hret := bytesStoreX_setMappedByteLongLongSuccessReturn
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len) (lenPost := lenPost)
    (acc := accEvm)
    h805 hcanon hlenPost hflagPost hvalidPost hbound hboundPost hflag hperm haccEvm
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreSetMappedByteLongDataSlot I)
    (bytesStoreSetMappedByteLongStoredWord σ_evm I)
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedByteSlot I) =
        bytesStoreSetMappedByteHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetMappedByteHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadData :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedByteLongDataSlot I) =
        bytesStoreSetMappedByteLongOldWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetMappedByteLongData_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  obtain ⟨accSolm, haccSolm⟩ :=
    accountMapEquiv_find?_some_exists hAccounts haccEvm
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
          (bytesStoreSetMappedByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simpa [evmSolm1, evmSolm0] using
      bytesStoreAccountMapEquiv_storageStore_initState
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreSetMappedByteLongDataSlot I)
        (bytesStoreSetMappedByteLongStoredWord σ_evm I)
  have hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedByteSlot I) =
        bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I := by
    have howner : evmSolm1.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv]
    simpa [evmSolm1, storageStore_executionEnv] using
      bytesStoreStorageLoadSetMappedByteHeader_of_accountMapEquiv
        (evm := evmSolm1)
        (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
          (bytesStoreSetMappedByteLongStoredWord σ_evm I))
        (I := I) howner hpostAccounts
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetMappedByteLocals I) setMappedByteTransition.body
        (.returned
          (bytesStoreSetMappedByteFrame I)
          evmSolm1 (some (bytesStoreSetMappedByteValue I))) := by
    simpa [evmSolm0, evmSolm1, initState, bytesStoreSetMappedByteFrame] using
      bytesStoreSetMappedByteLongBodyReturnsOfPostLongReadback
        (evm := evmSolm0) (σ := σ_evm) (I := I)
        (len := len) (lenPost := lenPost)
        (postHeaderWord := bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I)
        (acc := accSolm)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadHeader hloadData hloadHeaderPost
        (by simpa [evmSolm0, initState] using haccSolm)
        hcanon hlen hlenPost hbound hboundPost hflag hvalid hflagPost hvalidPost
  have hd := bytesStoreDispatch_setMappedByte (cd := I.calldata)
    (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMappedByte (I := I) hsz100 hhi hcanon
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    hpostAccounts
    (returnEquiv_of_encode (uint8ReturnEncoding (bytesStoreSetMappedByteValueWord I) hcanon))

theorem bytesStoreSetMappedByteLongReturnShortSuccessRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len lenPost : UInt256}
    {accEvm : Account}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hlenPost : lenPost = UInt256.land (UInt256.div
      (bytesStoreSetMappedByteHeaderWord
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
          (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨127⟩)
    (hflagPost : UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I) ⟨1⟩ = ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStoreSetMappedByteHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
              (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hlen : len = UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hboundPost : (bytesStoreSetMappedByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠
      ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetMappedByteSelector_size hsel
  have hreach := bytesStoreReachSetMappedByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨319⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetMappedByteEntryPc] using hreach
  have hreachBody := bytesStoreX_setMappedByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hdecLen := bytesStoreX_setMappedByteReachLengthDecoder
    (g := Sat256.ofUInt256 g) hreachBody
  have h805Raw := bytesStoreX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hdecLen hflag hvalid
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have h805 :
      ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨805⟩
        [len, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
          UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
          bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [hlen] using h805Raw
  have hret := bytesStoreX_setMappedByteLongShortSuccessReturn
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len) (lenPost := lenPost)
    (acc := accEvm)
    h805 hcanon hlenPost hflagPost hvalidPost hbound hboundPost hflag hperm haccEvm
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreSetMappedByteLongDataSlot I)
    (bytesStoreSetMappedByteLongStoredWord σ_evm I)
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedByteSlot I) =
        bytesStoreSetMappedByteHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetMappedByteHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadData :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedByteLongDataSlot I) =
        bytesStoreSetMappedByteLongOldWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetMappedByteLongData_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
          (bytesStoreSetMappedByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simpa [evmSolm1, evmSolm0] using
      bytesStoreAccountMapEquiv_storageStore_initState
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreSetMappedByteLongDataSlot I)
        (bytesStoreSetMappedByteLongStoredWord σ_evm I)
  have hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedByteSlot I) =
        bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I := by
    have howner : evmSolm1.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv]
    simpa [evmSolm1, storageStore_executionEnv] using
      bytesStoreStorageLoadSetMappedByteHeader_of_accountMapEquiv
        (evm := evmSolm1)
        (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
          (bytesStoreSetMappedByteLongStoredWord σ_evm I))
        (I := I) howner hpostAccounts
  have hvalid0 :
      UInt256.sub ⟨0⟩ (UInt256.lt lenPost ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlenPost, hflagPost] using hvalidPost
  have hshortPost : lenPost.toNat < 32 :=
    solidityShortBytesValid_lt32 hvalid0
  have hidxLt32 : (bytesStoreSetMappedByteIndexWord I).toNat < 32 :=
    lt_trans hboundPost hshortPost
  have hbytePost :
      UInt256.byteAt (bytesStoreSetMappedByteIndexWord I)
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I) =
        bytesStoreSetMappedByteValueWord I := by
    by_cases hEq :
        bytesStoreSetMappedByteSlot I = bytesStoreSetMappedByteLongDataSlot I
    · have hheaderPostStored :
          bytesStoreSetMappedByteHeaderWord
              (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
                (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I =
            bytesStoreSetMappedByteLongStoredWord σ_evm I := by
        simpa [bytesStoreSetMappedByteHeaderWord, hEq] using
          sstoreAccountMap_storage_findD_self_of_find_some_any σ_evm I.codeOwner accEvm
            (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I) haccEvm
      rw [hheaderPostStored]
      exact bytesStoreSetMappedByteLongStoredWord_byteAt_index_of_lt32
        (σ := σ_evm) (I := I) hcanon hidxLt32
    · have hheaderOld :
          bytesStoreSetMappedByteHeaderWord
              (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
                (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I =
            bytesStoreSetMappedByteHeaderWord σ_evm I := by
        simpa [bytesStoreSetMappedByteHeaderWord,
          bytesStoreSetMappedByteLongDataSlot] using
          bytesStoreBytesHeaderWordAfterDataSstore_eq_of_before_of_ne
            (σ := σ_evm) (I := I) (baseSlot := bytesStoreSetMappedByteSlot I)
            (idx := bytesStoreSetMappedByteIndexWord I)
            (val := bytesStoreSetMappedByteLongStoredWord σ_evm I) hEq (by rfl)
      have hflagOldZero :
          UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ := by
        rw [← hheaderOld]
        exact hflagPost
      exact False.elim (hflag hflagOldZero)
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetMappedByteLocals I) setMappedByteTransition.body
        (.returned
          (bytesStoreSetMappedByteFrame I)
          evmSolm1 (some (bytesStoreSetMappedByteValue I))) := by
    simpa [evmSolm0, evmSolm1, initState, bytesStoreSetMappedByteFrame] using
      bytesStoreSetMappedByteLongBodyReturnsOfPostShortReadback
        (evm := evmSolm0) (σ := σ_evm) (I := I)
        (len := len) (lenPost := lenPost)
        (postHeaderWord := bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadHeader hloadData hloadHeaderPost
        hcanon hlen hlenPost hbound hboundPost hflag hvalid hflagPost hvalidPost
        hbytePost
  have hd := bytesStoreDispatch_setMappedByte (cd := I.calldata)
    (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMappedByte (I := I) hsz100 hhi hcanon
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    hpostAccounts
    (returnEquiv_of_encode (uint8ReturnEncoding (bytesStoreSetMappedByteValueWord I) hcanon))

theorem bytesStoreSetMappedByteLongReturnLongOobLengthRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len lenPost : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hlenPost : lenPost = UInt256.div
      (bytesStoreSetMappedByteHeaderWord
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
          (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I) ⟨2⟩)
    (hflagPost : UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreSetMappedByteHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
              (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hboundPost : ¬ (bytesStoreSetMappedByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠
      ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetMappedByteSelector_size hsel
  have hreach := bytesStoreReachSetMappedByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨319⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetMappedByteEntryPc] using hreach
  have hreachBody := bytesStoreX_setMappedByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hdecLen := bytesStoreX_setMappedByteReachLengthDecoder
    (g := Sat256.ofUInt256 g) hreachBody
  have h805Raw := bytesStoreX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hdecLen hflag hvalid
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have h805 :
      ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨805⟩
        [len, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
          UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
          bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [hlen] using h805Raw
  have hread := bytesStoreX_setMappedByteLongWriteReturnDecodedPostLongLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len) (lenPost := lenPost)
    h805 hbound hflag hlenPost hflagPost hvalidPost hperm
  have hrev := bytesStoreX_setMappedByteReturnOobLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ_evm)
    (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
      (bytesStoreSetMappedByteLongStoredWord σ_evm I))
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) (len := lenPost)
    hread hboundPost
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreSetMappedByteLongDataSlot I)
    (bytesStoreSetMappedByteLongStoredWord σ_evm I)
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedByteSlot I) =
        bytesStoreSetMappedByteHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetMappedByteHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadData :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedByteLongDataSlot I) =
        bytesStoreSetMappedByteLongOldWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetMappedByteLongData_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
          (bytesStoreSetMappedByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simpa [evmSolm1, evmSolm0] using
      bytesStoreAccountMapEquiv_storageStore_initState
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreSetMappedByteLongDataSlot I)
        (bytesStoreSetMappedByteLongStoredWord σ_evm I)
  have hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedByteSlot I) =
        bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I := by
    have howner : evmSolm1.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv]
    simpa [evmSolm1, storageStore_executionEnv] using
      bytesStoreStorageLoadSetMappedByteHeader_of_accountMapEquiv
        (evm := evmSolm1)
        (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
          (bytesStoreSetMappedByteLongStoredWord σ_evm I))
        (I := I) howner hpostAccounts
  have hd := bytesStoreDispatch_setMappedByte (cd := I.calldata)
    (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMappedByte (I := I) hsz100 hhi hcanon
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetMappedByteLocals I) setMappedByteTransition.body .reverted := by
    simpa [evmSolm0, initState] using
      bytesStoreSetMappedByteLongBodyReturnRevertsOfPostLongLength
        (evm := evmSolm0) (σ := σ_evm) (I := I)
        (len := len) (lenPost := lenPost)
        (postHeaderWord := bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadHeader hloadData hloadHeaderPost hcanon hlen hlenPost hbound hboundPost
        hflag hvalid hflagPost hvalidPost
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreSetMappedByteLongReturnShortOobLengthRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len lenPost : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hlenPost : lenPost = UInt256.land (UInt256.div
      (bytesStoreSetMappedByteHeaderWord
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
          (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨127⟩)
    (hflagPost : UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I) ⟨1⟩ = ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStoreSetMappedByteHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
              (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hlen : len = UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hboundPost : ¬ (bytesStoreSetMappedByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠
      ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetMappedByteSelector_size hsel
  have hreach := bytesStoreReachSetMappedByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨319⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetMappedByteEntryPc] using hreach
  have hreachBody := bytesStoreX_setMappedByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hdecLen := bytesStoreX_setMappedByteReachLengthDecoder
    (g := Sat256.ofUInt256 g) hreachBody
  have h805Raw := bytesStoreX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hdecLen hflag hvalid
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have h805 :
      ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨805⟩
        [len, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
          UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
          bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [hlen] using h805Raw
  have hread := bytesStoreX_setMappedByteLongWriteReturnDecodedShortLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len)
    h805 hbound hflag hflagPost hvalidPost hperm
  have hrev := bytesStoreX_setMappedByteReturnOobLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ_evm)
    (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
      (bytesStoreSetMappedByteLongStoredWord σ_evm I))
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) (len := lenPost)
    (by simpa [hlenPost] using hread) hboundPost
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreSetMappedByteLongDataSlot I)
    (bytesStoreSetMappedByteLongStoredWord σ_evm I)
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedByteSlot I) =
        bytesStoreSetMappedByteHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetMappedByteHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadData :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedByteLongDataSlot I) =
        bytesStoreSetMappedByteLongOldWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetMappedByteLongData_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
          (bytesStoreSetMappedByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simpa [evmSolm1, evmSolm0] using
      bytesStoreAccountMapEquiv_storageStore_initState
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreSetMappedByteLongDataSlot I)
        (bytesStoreSetMappedByteLongStoredWord σ_evm I)
  have hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedByteSlot I) =
        bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I := by
    have howner : evmSolm1.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv]
    simpa [evmSolm1, storageStore_executionEnv] using
      bytesStoreStorageLoadSetMappedByteHeader_of_accountMapEquiv
        (evm := evmSolm1)
        (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
          (bytesStoreSetMappedByteLongStoredWord σ_evm I))
        (I := I) howner hpostAccounts
  have hd := bytesStoreDispatch_setMappedByte (cd := I.calldata)
    (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMappedByte (I := I) hsz100 hhi hcanon
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetMappedByteLocals I) setMappedByteTransition.body .reverted := by
    simpa [evmSolm0, initState] using
      bytesStoreSetMappedByteLongBodyReturnRevertsOfPostShortLength
        (evm := evmSolm0) (σ := σ_evm) (I := I)
        (len := len) (lenPost := lenPost)
        (postHeaderWord := bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadHeader hloadData hloadHeaderPost hcanon hlen hlenPost hbound hboundPost
        hflag hvalid hflagPost hvalidPost
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreSetMappedByteLongReturnLongMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠
      ⟨0⟩)
    (hflagPost : UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hbadPost : UInt256.sub (UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreSetMappedByteHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
              (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetMappedByteSelector_size hsel
  have hreach := bytesStoreReachSetMappedByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨319⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetMappedByteEntryPc] using hreach
  have hreachBody := bytesStoreX_setMappedByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hdecLen := bytesStoreX_setMappedByteReachLengthDecoder
    (g := Sat256.ofUInt256 g) hreachBody
  have h805Raw := bytesStoreX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hdecLen hflag hvalid
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have h805 :
      ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨805⟩
        [len, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
          UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
          bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [hlen] using h805Raw
  have hrev := bytesStoreX_setMappedByteLongWriteReturnLongMalformed
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len)
    h805 hbound hflag hflagPost hbadPost hperm
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreSetMappedByteLongDataSlot I)
    (bytesStoreSetMappedByteLongStoredWord σ_evm I)
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedByteSlot I) =
        bytesStoreSetMappedByteHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetMappedByteHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadData :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedByteLongDataSlot I) =
        bytesStoreSetMappedByteLongOldWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetMappedByteLongData_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
          (bytesStoreSetMappedByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simpa [evmSolm1, evmSolm0] using
      bytesStoreAccountMapEquiv_storageStore_initState
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreSetMappedByteLongDataSlot I)
        (bytesStoreSetMappedByteLongStoredWord σ_evm I)
  have hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedByteSlot I) =
        bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I := by
    have howner : evmSolm1.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv]
    simpa [evmSolm1, storageStore_executionEnv] using
      bytesStoreStorageLoadSetMappedByteHeader_of_accountMapEquiv
        (evm := evmSolm1)
        (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
          (bytesStoreSetMappedByteLongStoredWord σ_evm I))
        (I := I) howner hpostAccounts
  have hd := bytesStoreDispatch_setMappedByte (cd := I.calldata)
    (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMappedByte (I := I) hsz100 hhi hcanon
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetMappedByteLocals I) setMappedByteTransition.body .reverted := by
    simpa [evmSolm0, initState] using
      bytesStoreSetMappedByteLongBodyReturnRevertsOfPostLongMalformed
        (evm := evmSolm0) (σ := σ_evm) (I := I) (len := len)
        (postHeaderWord := bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadHeader hloadData hloadHeaderPost hcanon hlen hbound hflag hvalid
        hflagPost hbadPost
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreSetMappedByteLongReturnShortMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
    (hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠
      ⟨0⟩)
    (hflagPost : UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I) ⟨1⟩ = ⟨0⟩)
    (hbadPost : UInt256.sub (UInt256.land
        (bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStoreSetMappedByteHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
              (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨127⟩) ⟨32⟩) =
          ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetMappedByteSelector_size hsel
  have hreach := bytesStoreReachSetMappedByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨319⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetMappedByteEntryPc] using hreach
  have hreachBody := bytesStoreX_setMappedByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hdecLen := bytesStoreX_setMappedByteReachLengthDecoder
    (g := Sat256.ofUInt256 g) hreachBody
  have h805Raw := bytesStoreX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hdecLen hflag hvalid
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have h805 :
      ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨805⟩
        [len, bytesStoreSetMappedByteIndexWord I, bytesStoreSetMappedByteSlot I,
          UInt256.shiftLeft (bytesStoreSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetMappedByteValueWord I, bytesStoreSetMappedByteIndexWord I,
          bytesStoreSetMappedByteKeyWord I, ⟨301⟩, bytesStoreSelWord I]
        (twoWordHashMem (bytesStoreSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [hlen] using h805Raw
  have hrev := bytesStoreX_setMappedByteLongWriteReturnShortMalformed
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len)
    h805 hbound hflag hflagPost hbadPost hperm
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreSetMappedByteLongDataSlot I)
    (bytesStoreSetMappedByteLongStoredWord σ_evm I)
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedByteSlot I) =
        bytesStoreSetMappedByteHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetMappedByteHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadData :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedByteLongDataSlot I) =
        bytesStoreSetMappedByteLongOldWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetMappedByteLongData_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
          (bytesStoreSetMappedByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simpa [evmSolm1, evmSolm0] using
      bytesStoreAccountMapEquiv_storageStore_initState
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreSetMappedByteLongDataSlot I)
        (bytesStoreSetMappedByteLongStoredWord σ_evm I)
  have hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedByteSlot I) =
        bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I := by
    have howner : evmSolm1.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv]
    simpa [evmSolm1, storageStore_executionEnv] using
      bytesStoreStorageLoadSetMappedByteHeader_of_accountMapEquiv
        (evm := evmSolm1)
        (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
          (bytesStoreSetMappedByteLongStoredWord σ_evm I))
        (I := I) howner hpostAccounts
  have hd := bytesStoreDispatch_setMappedByte (cd := I.calldata)
    (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMappedByte (I := I) hsz100 hhi hcanon
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetMappedByteLocals I) setMappedByteTransition.body .reverted := by
    simpa [evmSolm0, initState] using
      bytesStoreSetMappedByteLongBodyReturnRevertsOfPostShortMalformed
        (evm := evmSolm0) (σ := σ_evm) (I := I) (len := len)
        (postHeaderWord := bytesStoreSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedByteLongDataSlot I)
            (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadHeader hloadData hloadHeaderPost hcanon hlen hbound hflag hvalid
        hflagPost hbadPost
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreSetMappedByteRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hsz100 : 100 ≤ I.calldata.size
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (bytesStoreSetMappedByteValueWord I).toNat < EVM.twoPow 8
      · by_cases hflagLong :
          UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩
        · by_cases hvalidLong :
            UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩)
              (UInt256.lt (UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
                ⟨32⟩) ≠ ⟨0⟩
          · let len := UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩
            by_cases hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat
            · by_cases haccSome : ∃ accEvm, σ_evm.find? I.codeOwner = some accEvm
              · obtain ⟨accEvm, haccEq⟩ := haccSome
                let postHeader :=
                  bytesStoreSetMappedByteHeaderWord
                    (sstoreAccountMap I.codeOwner σ_evm
                      (bytesStoreSetMappedByteLongDataSlot I)
                      (bytesStoreSetMappedByteLongStoredWord σ_evm I)) I
                by_cases hflagPostLong : UInt256.land postHeader ⟨1⟩ ≠ ⟨0⟩
                · by_cases hvalidPostLong :
                    UInt256.sub (UInt256.land postHeader ⟨1⟩)
                      (UInt256.lt (UInt256.div postHeader ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩
                  · let lenPost := UInt256.div postHeader ⟨2⟩
                    by_cases hboundPost :
                        (bytesStoreSetMappedByteIndexWord I).toNat < lenPost.toNat
                    · exact bytesStoreSetMappedByteLongReturnLongSuccessRuntime
                        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                        (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                        (len := len) (lenPost := lenPost) (accEvm := accEvm)
                        hcode hsize hperm hwv hsel hAccounts haccEq hsz100 hhi hcanon
                        (by rfl) (by simpa [postHeader] using hflagPostLong)
                        (by simpa [postHeader] using hvalidPostLong)
                        (by rfl) hbound hboundPost hflagLong hvalidLong
                    · exact bytesStoreSetMappedByteLongReturnLongOobLengthRuntime
                        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                        (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                        (len := len) (lenPost := lenPost)
                        hcode hsize hperm hwv hsel hAccounts hsz100 hhi hcanon
                        (by rfl) (by simpa [postHeader] using hflagPostLong)
                        (by simpa [postHeader] using hvalidPostLong)
                        (by rfl) hbound hboundPost hflagLong hvalidLong
                  · have hbadPostLong :
                      UInt256.sub (UInt256.land postHeader ⟨1⟩)
                        (UInt256.lt (UInt256.div postHeader ⟨2⟩) ⟨32⟩) = ⟨0⟩ := by
                      by_contra hne
                      exact hvalidPostLong hne
                    exact bytesStoreSetMappedByteLongReturnLongMalformedRuntime
                      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                      (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                      (len := len)
                      hcode hsize hperm hwv hsel hAccounts hsz100 hhi hcanon
                      (by rfl) hbound hflagLong hvalidLong
                      (by simpa [postHeader] using hflagPostLong)
                      (by simpa [postHeader] using hbadPostLong)
                · have hflagPostShort : UInt256.land postHeader ⟨1⟩ = ⟨0⟩ := by
                    by_contra hne
                    exact hflagPostLong hne
                  by_cases hvalidPostShort :
                      UInt256.sub (UInt256.land postHeader ⟨1⟩)
                        (UInt256.lt (UInt256.land (UInt256.div postHeader ⟨2⟩) ⟨127⟩)
                          ⟨32⟩) ≠ ⟨0⟩
                  · let lenPost := UInt256.land (UInt256.div postHeader ⟨2⟩) ⟨127⟩
                    by_cases hboundPost :
                        (bytesStoreSetMappedByteIndexWord I).toNat < lenPost.toNat
                    · exact bytesStoreSetMappedByteLongReturnShortSuccessRuntime
                        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                        (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                        (len := len) (lenPost := lenPost) (accEvm := accEvm)
                        hcode hsize hperm hwv hsel hAccounts haccEq hsz100 hhi hcanon
                        (by rfl) (by simpa [postHeader] using hflagPostShort)
                        (by simpa [postHeader] using hvalidPostShort)
                        (by rfl) hbound hboundPost hflagLong hvalidLong
                    · exact bytesStoreSetMappedByteLongReturnShortOobLengthRuntime
                        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                        (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                        (len := len) (lenPost := lenPost)
                        hcode hsize hperm hwv hsel hAccounts hsz100 hhi hcanon
                        (by rfl) (by simpa [postHeader] using hflagPostShort)
                        (by simpa [postHeader] using hvalidPostShort)
                        (by rfl) hbound hboundPost hflagLong hvalidLong
                  · have hbadPostShort :
                      UInt256.sub (UInt256.land postHeader ⟨1⟩)
                        (UInt256.lt (UInt256.land (UInt256.div postHeader ⟨2⟩) ⟨127⟩)
                          ⟨32⟩) = ⟨0⟩ := by
                      by_contra hne
                      exact hvalidPostShort hne
                    exact bytesStoreSetMappedByteLongReturnShortMalformedRuntime
                      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                      (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                      (len := len)
                      hcode hsize hperm hwv hsel hAccounts hsz100 hhi hcanon
                      (by rfl) hbound hflagLong hvalidLong
                      (by simpa [postHeader] using hflagPostShort)
                      (by simpa [postHeader] using hbadPostShort)
              · have haccNone : σ_evm.find? I.codeOwner = none := by
                  cases haccEq : σ_evm.find? I.codeOwner with
                  | none => rfl
                  | some accEvm => exact False.elim (haccSome ⟨accEvm, haccEq⟩)
                have hhdr :
                    bytesStoreSetMappedByteHeaderWord σ_evm I = ⟨0⟩ := by
                  simp [bytesStoreSetMappedByteHeaderWord, haccNone, Option.option]
                have hflag0 :
                    UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩ =
                      ⟨0⟩ := by
                  rw [hhdr]
                  native_decide
                exact False.elim (hflagLong hflag0)
            · exact bytesStoreSetMappedByteOobLongRuntime
                (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hcode hsize hperm hwv hsel hAccounts hsz100 hhi hcanon
                hflagLong hvalidLong hbound
          · have hbad :
              UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩)
                (UInt256.lt (UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
                  ⟨32⟩) = ⟨0⟩ := by
              by_contra hne
              exact hvalidLong hne
            exact bytesStoreSetMappedByteLongMalformedRuntime
              (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
              (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hcode hsize hperm hwv hsel hAccounts hsz100 hhi hcanon
              hflagLong hbad
        · have hflagShort :
            UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ := by
            by_contra hne
            exact hflagLong hne
          by_cases hvalidShort :
              UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩)
                (UInt256.lt
                  (UInt256.land
                    (UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
                    ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
          · let len :=
              UInt256.land
                (UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
            have hltNe : UInt256.lt len ⟨32⟩ ≠ ⟨0⟩ := by
              intro hlt0
              have hzero : UInt256.sub ⟨0⟩ ⟨0⟩ = (⟨0⟩ : UInt256) := by
                native_decide
              exact hvalidShort (by simpa [len, hflagShort, hlt0] using hzero)
            have hshort : len.toNat < 32 := by
              have hlt := ult_ne_zero_toNat_lt hltNe
              simpa using hlt
            by_cases hbound : (bytesStoreSetMappedByteIndexWord I).toNat < len.toNat
            · by_cases haccSome : ∃ accEvm, σ_evm.find? I.codeOwner = some accEvm
              · obtain ⟨accEvm, haccEq⟩ := haccSome
                exact bytesStoreSetMappedByteShortSuccessRuntime
                  (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                  (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  (len := len) (accEvm := accEvm)
                  hcode hsize hperm hwv hsel hAccounts haccEq hsz100 hhi hcanon
                  (by rfl) hshort hbound hflagShort hvalidShort
              · have haccNone : σ_evm.find? I.codeOwner = none := by
                  cases haccEq : σ_evm.find? I.codeOwner with
                  | none => rfl
                  | some accEvm => exact False.elim (haccSome ⟨accEvm, haccEq⟩)
                have hhdr :
                    bytesStoreSetMappedByteHeaderWord σ_evm I = ⟨0⟩ := by
                  simp [bytesStoreSetMappedByteHeaderWord, haccNone, Option.option]
                have hlenZero : len = ⟨0⟩ := by
                  change
                    UInt256.land
                      (UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
                      ⟨127⟩ = ⟨0⟩
                  rw [hhdr]
                  native_decide
                have hlen0 : len.toNat = 0 := by
                  simp [hlenZero]
                have hbadBound : (bytesStoreSetMappedByteIndexWord I).toNat < 0 := by
                  simp [hlen0] at hbound
                exact False.elim (Nat.not_lt_zero _ hbadBound)
            · exact bytesStoreSetMappedByteOobShortRuntime
                (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hcode hsize hperm hwv hsel hAccounts hsz100 hhi hcanon
                hflagShort hvalidShort hbound
          · have hbad :
              UInt256.sub (UInt256.land (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨1⟩)
                (UInt256.lt
                  (UInt256.land
                    (UInt256.div (bytesStoreSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
                    ⟨127⟩) ⟨32⟩) = ⟨0⟩ := by
              by_contra hne
              exact hvalidShort hne
            exact bytesStoreSetMappedByteShortMalformedRuntime
              (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
              (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hcode hsize hperm hwv hsel hAccounts hsz100 hhi hcanon
              hflagShort hbad
      · exact bytesStoreSetMappedByteDecodeNoncanonValueRuntime
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hsize hperm hwv hsel hAccounts hsz100 hhi hcanon
    · exact bytesStoreSetMappedByteDecodeHugeRuntime
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts (by omega)
  · exact bytesStoreSetMappedByteDecodeShortRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts (by omega)

end BytesStore
