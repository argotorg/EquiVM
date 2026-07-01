import Examples.BytesStoreLite.FullSetMappedByte

/-!
# BytesStoreLite — `setMappedByte(uint256,uint256,uint8)` success paths

Successful writes are split from the decoder/revert layer so the mapped-byte proof can be
iterated independently from the already-stable malformed and bounds cases.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace BytesStoreLite

theorem bytesStoreLiteSetMappedByteLongBaseHashMem (I : ExecutionEnv) (mem : ByteArray) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((wordAt0Mem (bytesStoreLiteSetMappedByteSlot I) mem).readWithPadding 0 32))) =
      bytesLikeDataBase (bytesStoreLiteSetMappedByteSlot I) := by
  rw [wordAt0Mem_read0]
  simpa [bytesLikeDataBase] using
    keccakSlot_eq (UInt256.toByteArray (bytesStoreLiteSetMappedByteSlot I))

theorem bytesStoreLiteSetMappedByteSlotHashMem (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ mem
          ).readWithPadding 0 64))) =
      bytesStoreLiteSetMappedByteSlot I := by
  rw [twoWordHashMem_read0_64 (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ hmem]
  unfold bytesStoreLiteSetMappedByteSlot bytesStoreLiteSetMappedSlotOf mappedValueSlot
  rw [keyValueToWord_uint256]
  exact mappingSlot_single (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩

theorem bytesStoreLiteX_setMappedByteShortReachStoreCommon {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨805⟩
      [len, bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
        bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨848⟩
      [bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
        bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd805⟩ := hreach
  have hlt : UInt256.lt (bytesStoreLiteSetMappedByteIndexWord I) len = ⟨1⟩ :=
    ult_one hbound
  have rd819 := evm_run rd805 with [
    jumpdest, dup2, lt, push2 ⟨819⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd821 := evm_run rd819 with [jumpdest, dup2]
  obtain ⟨_, _, rd822₀⟩ := rd821.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd822⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨822⟩
        [bytesStoreLiteSetMappedByteHeaderWord σ I, bytesStoreLiteSetMappedByteIndexWord I,
          bytesStoreLiteSetMappedByteSlot I,
          UInt256.shiftLeft (bytesStoreLiteSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
          bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteSetMappedByteHeaderWord, initState] using rd822₀⟩
  have rd848 := evm_run rd822 with [
    push1 ⟨1⟩, and, iszero, push2 ⟨848⟩,
    jumpiT (by
      rw [u256_land_comm, hflag]
      decide)
      (by native_decide)]
  exact ⟨_, _, rd848⟩

theorem bytesStoreLiteX_setMappedByteLongReachStoreCommon {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨805⟩
      [len, bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
        bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨848⟩
      [bytesStoreLiteSetMappedByteLongWordIndex I, bytesStoreLiteSetMappedByteLongDataSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
        bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (bytesStoreLiteSetMappedByteSlot I)
        (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd805⟩ := hreach
  have hlt : UInt256.lt (bytesStoreLiteSetMappedByteIndexWord I) len = ⟨1⟩ :=
    ult_one hbound
  have hflagOne :
      UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨1⟩ = ⟨1⟩ :=
    u256_land_one_eq_one_of_ne_zero hflag
  have hslot := bytesStoreLiteSetMappedByteLongBaseHashMem I
    (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
  have rd819 := evm_run rd805 with [
    jumpdest, dup2, lt, push2 ⟨819⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd821 := evm_run rd819 with [jumpdest, dup2]
  obtain ⟨_, _, rd822₀⟩ := rd821.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd822⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨822⟩
        [bytesStoreLiteSetMappedByteHeaderWord σ I, bytesStoreLiteSetMappedByteIndexWord I,
          bytesStoreLiteSetMappedByteSlot I,
          UInt256.shiftLeft (bytesStoreLiteSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
          bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteSetMappedByteHeaderWord, initState] using rd822₀⟩
  have rd847 := evm_run rd822 with [
    push1 ⟨1⟩, and, iszero, push2 ⟨848⟩,
    jumpiNT (by
      rw [u256_land_comm, hflagOne]
      decide),
    swap1, push0,
    raw mstore 0 (wordAt0Mem (bytesStoreLiteSetMappedByteSlot I)
        (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem))
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256 0 (bytesLikeDataBase (bytesStoreLiteSetMappedByteSlot I))
      (UInt256.ofNat 3)
      (by native_decide) mem_cost hslot (by native_decide) (by evm_ov),
    swap1, push1 ⟨32⟩, swap2, dup3, dup3, div, add, swap2, swap1]
  have rd848raw := RD.mod rd847 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa [bytesStoreLiteSetMappedByteLongWordIndex,
      bytesStoreLiteSetMappedByteLongDataSlot,
      u256_add_comm (UInt256.div (bytesStoreLiteSetMappedByteIndexWord I) ⟨32⟩)
        (bytesLikeDataBase (bytesStoreLiteSetMappedByteSlot I))] using rd848raw⟩

theorem bytesStoreLiteX_setMappedByteShortStore {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨848⟩
      [bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
        bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨877⟩
      [⟨0⟩, bytesStoreLiteSetMappedByteValueWord I,
        bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteKeyWord I,
        ⟨301⟩, bytesStoreLiteSelWord I]
      (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedByteSlot I)
        (bytesStoreLiteSetMappedByteShortStoredWord σ I)) k C := by
  obtain ⟨_, _, rd848⟩ := hreach
  have rd857 := evm_run rd848 with [
    jumpdest, push1 ⟨31⟩, sub, push2 ⟨256⟩, exp, dup2]
  obtain ⟨_, _, rd858₀⟩ := rd857.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd858⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨858⟩
        [bytesStoreLiteSetMappedByteHeaderWord σ I,
          UInt256.exp ⟨256⟩ (UInt256.sub ⟨31⟩
            (bytesStoreLiteSetMappedByteIndexWord I)),
          bytesStoreLiteSetMappedByteSlot I,
          UInt256.shiftLeft (bytesStoreLiteSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
          bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteSetMappedByteHeaderWord, initState] using rd858₀⟩
  have rd875 := evm_run rd858 with [
    dup2, push1 ⟨255⟩, mul, not, and, swap1,
    push1 ⟨1⟩, push1 ⟨248⟩, shl, dup5, div, mul, lor, swap1]
  obtain ⟨_, _, rd875'⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨875⟩
        [bytesStoreLiteSetMappedByteSlot I,
          bytesStoreLiteSetMappedByteShortStoredWord σ I,
          UInt256.shiftLeft (bytesStoreLiteSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
          bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteSetMappedByteShortStoredWord,
        bytesStoreLiteSetMappedByteShortScale] using rd875⟩
  obtain ⟨_, _, rd876₀⟩ := rd875'.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd876⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨876⟩
        [UInt256.shiftLeft (bytesStoreLiteSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
          bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedByteSlot I)
          (bytesStoreLiteSetMappedByteShortStoredWord σ I)) k C := by
    exact ⟨_, _, by simpa [sstoreAccountMap, initState] using rd876₀⟩
  exact ⟨_, _, evm_run rd876 with [pop]⟩

theorem bytesStoreLiteX_setMappedByteLongStore {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨848⟩
      [bytesStoreLiteSetMappedByteLongWordIndex I, bytesStoreLiteSetMappedByteLongDataSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
        bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (bytesStoreLiteSetMappedByteSlot I)
        (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨877⟩
      [⟨0⟩, bytesStoreLiteSetMappedByteValueWord I,
        bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteKeyWord I,
        ⟨301⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (bytesStoreLiteSetMappedByteSlot I)
        (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedByteLongDataSlot I)
        (bytesStoreLiteSetMappedByteLongStoredWord σ I)) k C := by
  obtain ⟨_, _, rd848⟩ := hreach
  have rd857 := evm_run rd848 with [
    jumpdest, push1 ⟨31⟩, sub, push2 ⟨256⟩, exp, dup2]
  obtain ⟨_, _, rd858₀⟩ := rd857.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd858⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨858⟩
        [bytesStoreLiteSetMappedByteLongOldWord σ I,
          UInt256.exp ⟨256⟩ (UInt256.sub ⟨31⟩
            (bytesStoreLiteSetMappedByteLongWordIndex I)),
          bytesStoreLiteSetMappedByteLongDataSlot I,
          UInt256.shiftLeft (bytesStoreLiteSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
          bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (bytesStoreLiteSetMappedByteSlot I)
          (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem))
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteSetMappedByteLongOldWord, initState] using rd858₀⟩
  have rd875 := evm_run rd858 with [
    dup2, push1 ⟨255⟩, mul, not, and, swap1,
    push1 ⟨1⟩, push1 ⟨248⟩, shl, dup5, div, mul, lor, swap1]
  obtain ⟨_, _, rd875'⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨875⟩
        [bytesStoreLiteSetMappedByteLongDataSlot I,
          bytesStoreLiteSetMappedByteLongStoredWord σ I,
          UInt256.shiftLeft (bytesStoreLiteSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
          bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (bytesStoreLiteSetMappedByteSlot I)
          (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem))
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteSetMappedByteLongStoredWord,
        bytesStoreLiteSetMappedByteLongScale] using rd875⟩
  obtain ⟨_, _, rd876₀⟩ := rd875'.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd876⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨876⟩
        [UInt256.shiftLeft (bytesStoreLiteSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
          bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (bytesStoreLiteSetMappedByteSlot I)
          (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem))
        (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedByteLongDataSlot I)
          (bytesStoreLiteSetMappedByteLongStoredWord σ I)) k C := by
    exact ⟨_, _, by simpa [sstoreAccountMap, initState] using rd876₀⟩
  exact ⟨_, _, evm_run rd876 with [pop]⟩

theorem bytesStoreLiteX_setMappedByteReturnReachLengthDecoderMem
    {cA gh bl σinit σ σ₀ A I} {g : Sat256} {mem : ByteArray}
    (hmem : mem.size = 96)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨877⟩
      [⟨0⟩, bytesStoreLiteSetMappedByteValueWord I,
        bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteKeyWord I,
        ⟨301⟩, bytesStoreLiteSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      [bytesStoreLiteSetMappedByteHeaderWord σ I, ⟨905⟩,
        bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteSlot I, ⟨0⟩,
        bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
        bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd877⟩ := hreach
  have hslot := bytesStoreLiteSetMappedByteSlotHashMem (I := I) hmem
  have rd895 := evm_run rd877 with [
    push1 ⟨4⟩, push0, dup6, dup2,
    raw mstore 0 (wordAt0Mem (bytesStoreLiteSetMappedByteKeyWord I) mem)
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, add, swap1, dup2,
    raw mstore 0
      (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ mem)
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, add, push0,
    raw keccak256 0 (bytesStoreLiteSetMappedByteSlot I) (UInt256.ofNat 3)
      (by native_decide) mem_cost hslot (by native_decide) (by evm_ov),
    dup4, dup2]
  obtain ⟨_, _, rd897₀⟩ := rd895.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd897⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨897⟩
        [bytesStoreLiteSetMappedByteHeaderWord σ I,
          bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteSlot I, ⟨0⟩,
          bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
          bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ mem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteSetMappedByteHeaderWord, initState] using rd897₀⟩
  exact ⟨_, _, evm_run rd897 with [
    push2 ⟨905⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreLiteX_setMappedByteShortWriteReturnReachLengthDecoder
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨805⟩
      [len, bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
        bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [bytesStoreLiteSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedByteSlot I)
            (bytesStoreLiteSetMappedByteShortStoredWord σ I)) I,
        ⟨905⟩, bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteSlot I,
        ⟨0⟩, bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
        bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩
        (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedByteSlot I)
        (bytesStoreLiteSetMappedByteShortStoredWord σ I)) k C := by
  have h848 := bytesStoreLiteX_setMappedByteShortReachStoreCommon
    (g := g) hreach hbound hflag
  have h877 := bytesStoreLiteX_setMappedByteShortStore
    (g := g) h848 hperm
  exact bytesStoreLiteX_setMappedByteReturnReachLengthDecoderMem
    (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedByteSlot I)
      (bytesStoreLiteSetMappedByteShortStoredWord σ I))
    (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
    h877

theorem bytesStoreLiteX_setMappedByteLongWriteReturnReachLengthDecoder
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨805⟩
      [len, bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
        bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [bytesStoreLiteSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedByteLongDataSlot I)
            (bytesStoreLiteSetMappedByteLongStoredWord σ I)) I,
        ⟨905⟩, bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteSlot I,
        ⟨0⟩, bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
        bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩
        (wordAt0Mem (bytesStoreLiteSetMappedByteSlot I)
          (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedByteLongDataSlot I)
        (bytesStoreLiteSetMappedByteLongStoredWord σ I)) k C := by
  have h848 := bytesStoreLiteX_setMappedByteLongReachStoreCommon
    (g := g) hreach hbound hflag
  have h877 := bytesStoreLiteX_setMappedByteLongStore
    (g := g) h848 hperm
  exact bytesStoreLiteX_setMappedByteReturnReachLengthDecoderMem
    (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedByteLongDataSlot I)
      (bytesStoreLiteSetMappedByteLongStoredWord σ I))
    (wordAt0Mem_size_96 _ (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
    h877

theorem bytesStoreLiteX_setMappedByteShortWriteReturnDecodedLength
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨805⟩
      [len, bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
        bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hflagPost : UInt256.land
        (bytesStoreLiteSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedByteSlot I)
            (bytesStoreLiteSetMappedByteShortStoredWord σ I)) I) ⟨1⟩ = ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreLiteSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedByteSlot I)
            (bytesStoreLiteSetMappedByteShortStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStoreLiteSetMappedByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedByteSlot I)
              (bytesStoreLiteSetMappedByteShortStoredWord σ I)) I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨905⟩
      [UInt256.land (UInt256.div
          (bytesStoreLiteSetMappedByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedByteSlot I)
              (bytesStoreLiteSetMappedByteShortStoredWord σ I)) I) ⟨2⟩) ⟨127⟩,
        bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteSlot I, ⟨0⟩,
        bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
        bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩
        (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedByteSlot I)
        (bytesStoreLiteSetMappedByteShortStoredWord σ I)) k C := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedByteSlot I)
    (bytesStoreLiteSetMappedByteShortStoredWord σ I)
  have hdec := bytesStoreLiteX_setMappedByteShortWriteReturnReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag hperm
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := bytesStoreLiteSetMappedByteHeaderWord σ' I) (ret := ⟨905⟩)
    (rest := [bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteSlot I,
      ⟨0⟩, bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
      bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I])
    (mem := twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩
      (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [σ'] using hdec)
    (by simpa [σ'] using hflagPost)
    (by simpa [σ'] using hvalidPost)
    (by native_decide)
    (by simp)
  simpa [σ'] using hdecoded

theorem bytesStoreLiteX_setMappedByteLongWriteReturnDecodedLength
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨805⟩
      [len, bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
        bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hflagPost : UInt256.land
        (bytesStoreLiteSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedByteLongDataSlot I)
            (bytesStoreLiteSetMappedByteLongStoredWord σ I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreLiteSetMappedByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedByteLongDataSlot I)
            (bytesStoreLiteSetMappedByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreLiteSetMappedByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedByteLongDataSlot I)
              (bytesStoreLiteSetMappedByteLongStoredWord σ I)) I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨905⟩
      [UInt256.div
          (bytesStoreLiteSetMappedByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedByteLongDataSlot I)
              (bytesStoreLiteSetMappedByteLongStoredWord σ I)) I) ⟨2⟩,
        bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteSlot I, ⟨0⟩,
        bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
        bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩
        (wordAt0Mem (bytesStoreLiteSetMappedByteSlot I)
          (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedByteLongDataSlot I)
        (bytesStoreLiteSetMappedByteLongStoredWord σ I)) k C := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedByteLongDataSlot I)
    (bytesStoreLiteSetMappedByteLongStoredWord σ I)
  have hdec := bytesStoreLiteX_setMappedByteLongWriteReturnReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag hperm
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := bytesStoreLiteSetMappedByteHeaderWord σ' I) (ret := ⟨905⟩)
    (rest := [bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteSlot I,
      ⟨0⟩, bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
      bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I])
    (mem := twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩
      (wordAt0Mem (bytesStoreLiteSetMappedByteSlot I)
        (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [σ'] using hdec)
    (by simpa [σ'] using hflagPost)
    (by simpa [σ'] using hvalidPost)
    (by native_decide)
    (by simp)
  simpa [σ'] using hdecoded

theorem bytesStoreLiteX_setMappedByteShortReadReturnToWrapper
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len header : UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨905⟩
      [len, bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteSlot I, ⟨0⟩,
        bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
        bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat)
    (hheader :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetMappedByteSlot I) ⟨0⟩)) = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreLiteSetMappedByteIndexWord I) header)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreLiteSetMappedByteValueWord I) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨301⟩
      [bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
  obtain ⟨_, _, rd905⟩ := hreach
  have hlt : UInt256.lt (bytesStoreLiteSetMappedByteIndexWord I) len = ⟨1⟩ :=
    ult_one hbound
  have rd919 := evm_run rd905 with [
    jumpdest, dup2, lt, push2 ⟨919⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd921 := evm_run rd919 with [jumpdest, dup2]
  obtain ⟨_, _, rd922₀⟩ := rd921.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd922⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨922⟩
        [header, bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteSlot I,
          ⟨0⟩, bytesStoreLiteSetMappedByteValueWord I,
          bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteKeyWord I,
          ⟨301⟩, bytesStoreLiteSelWord I]
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
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨951⟩
        [header, bytesStoreLiteSetMappedByteIndexWord I, ⟨0⟩,
          bytesStoreLiteSetMappedByteValueWord I,
          bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteKeyWord I,
          ⟨301⟩, bytesStoreLiteSelWord I]
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

theorem bytesStoreLiteX_setMappedByteLongReadReturnToWrapper
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len header dataWord : UInt256}
    {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨905⟩
      [len, bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteSlot I, ⟨0⟩,
        bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
        bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat)
    (hheader :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetMappedByteSlot I) ⟨0⟩)) = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hdata :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetMappedByteLongDataSlot I) ⟨0⟩)) =
          dataWord)
    (hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreLiteSetMappedByteLongWordIndex I) dataWord)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreLiteSetMappedByteValueWord I) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨301⟩
      [bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSelWord I]
      (wordAt0Mem (bytesStoreLiteSetMappedByteSlot I) mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
  obtain ⟨_, _, rd905⟩ := hreach
  have hlt : UInt256.lt (bytesStoreLiteSetMappedByteIndexWord I) len = ⟨1⟩ :=
    ult_one hbound
  have hflagOne : UInt256.land header ⟨1⟩ = ⟨1⟩ :=
    u256_land_one_eq_one_of_ne_zero hflag
  have hslot := bytesStoreLiteSetMappedByteLongBaseHashMem I mem
  have rd919 := evm_run rd905 with [
    jumpdest, dup2, lt, push2 ⟨919⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd921 := evm_run rd919 with [jumpdest, dup2]
  obtain ⟨_, _, rd922₀⟩ := rd921.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd922⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨922⟩
        [header, bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteSlot I,
          ⟨0⟩, bytesStoreLiteSetMappedByteValueWord I,
          bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteKeyWord I,
          ⟨301⟩, bytesStoreLiteSelWord I]
        mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [initState, hheader] using rd922₀⟩
  have rd947 := evm_run rd922 with [
    push1 ⟨1⟩, and, iszero, push2 ⟨948⟩,
    jumpiNT (by
      rw [u256_land_comm, hflagOne]
      decide),
    swap1, push0,
    raw mstore 0 (wordAt0Mem (bytesStoreLiteSetMappedByteSlot I) mem)
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256 0 (bytesLikeDataBase (bytesStoreLiteSetMappedByteSlot I))
      (UInt256.ofNat 3)
      (by native_decide) mem_cost hslot (by native_decide) (by evm_ov),
    swap1, push1 ⟨32⟩, swap2, dup3, dup3, div, add, swap2, swap1]
  have rd948raw := RD.mod rd947 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd948⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨948⟩
        [bytesStoreLiteSetMappedByteLongWordIndex I,
          bytesStoreLiteSetMappedByteLongDataSlot I, ⟨0⟩,
          bytesStoreLiteSetMappedByteValueWord I,
          bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteKeyWord I,
          ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (bytesStoreLiteSetMappedByteSlot I) mem)
        (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteSetMappedByteLongWordIndex,
        bytesStoreLiteSetMappedByteLongDataSlot,
        u256_add_comm (UInt256.div (bytesStoreLiteSetMappedByteIndexWord I) ⟨32⟩)
          (bytesLikeDataBase (bytesStoreLiteSetMappedByteSlot I))] using rd948raw⟩
  have rd950 := evm_run rd948 with [jumpdest, swap1]
  obtain ⟨_, _, rd951₀⟩ := rd950.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd951⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨951⟩
        [dataWord, bytesStoreLiteSetMappedByteLongWordIndex I, ⟨0⟩,
          bytesStoreLiteSetMappedByteValueWord I,
          bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteKeyWord I,
          ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (bytesStoreLiteSetMappedByteSlot I) mem)
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

theorem bytesStoreLiteX_setMappedByteShortReadReturn
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len header : UInt256} {mem : ByteArray}
    (hsize : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨905⟩
      [len, bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteSlot I, ⟨0⟩,
        bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
        bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat)
    (hheader :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetMappedByteSlot I) ⟨0⟩)) = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreLiteSetMappedByteIndexWord I) header)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreLiteSetMappedByteValueWord I)
    (hcanon : UInt256.land (bytesStoreLiteSetMappedByteValueWord I) ⟨255⟩ =
      bytesStoreLiteSetMappedByteValueWord I) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σinit σ₀ g A I) (cA, τ)
      (UInt256.toByteArray (bytesStoreLiteSetMappedByteValueWord I)) := by
  have h301 := bytesStoreLiteX_setMappedByteShortReadReturnToWrapper
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (τ := τ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := len) (header := header) (mem := mem)
    hreach hbound hheader hflag hbyte
  have hret := bytesStoreLiteX_returnUInt8_301OfMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ := τ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := bytesStoreLiteSetMappedByteValueWord I)
    (mem := mem) hsize hread64 h301
  simpa [hcanon] using hret

theorem bytesStoreLiteX_setMappedByteLongReadReturn
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len header dataWord : UInt256}
    {mem : ByteArray}
    (hsize : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨905⟩
      [len, bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteSlot I, ⟨0⟩,
        bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
        bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat)
    (hheader :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetMappedByteSlot I) ⟨0⟩)) = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hdata :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetMappedByteLongDataSlot I) ⟨0⟩)) =
          dataWord)
    (hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreLiteSetMappedByteLongWordIndex I) dataWord)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreLiteSetMappedByteValueWord I)
    (hcanon : UInt256.land (bytesStoreLiteSetMappedByteValueWord I) ⟨255⟩ =
      bytesStoreLiteSetMappedByteValueWord I) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σinit σ₀ g A I) (cA, τ)
      (UInt256.toByteArray (bytesStoreLiteSetMappedByteValueWord I)) := by
  have h301 := bytesStoreLiteX_setMappedByteLongReadReturnToWrapper
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (τ := τ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := len) (header := header)
    (dataWord := dataWord) (mem := mem) hreach hbound hheader hflag hdata hbyte
  have hret := bytesStoreLiteX_returnUInt8_301OfMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ := τ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := bytesStoreLiteSetMappedByteValueWord I)
    (mem := wordAt0Mem (bytesStoreLiteSetMappedByteSlot I) mem)
    (wordAt0Mem_size_96 _ hsize)
    (bytesStoreLiteWordAt0Mem_read64 _ hsize hread64)
    h301
  simpa [hcanon] using hret

theorem bytesStoreLiteX_setMappedByteShortSuccessReturn
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256} {acc : Account}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨772⟩
      [bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
        bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcanon : (bytesStoreLiteSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len =
      UInt256.land (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hacc : σ.find? I.codeOwner = some acc) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedByteSlot I)
        (bytesStoreLiteSetMappedByteShortStoredWord σ I))
      (UInt256.toByteArray (bytesStoreLiteSetMappedByteValueWord I)) := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedByteSlot I)
    (bytesStoreLiteSetMappedByteShortStoredWord σ I)
  have hdec := bytesStoreLiteX_setMappedByteReachLengthDecoder (g := g) hreach
  have h805Raw := bytesStoreLiteX_bytesLengthDecoderShortValidMem
    (A := A) (I := I) (g := g) hdec hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h805 :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨805⟩
        [len, bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteSlot I,
          UInt256.shiftLeft (bytesStoreLiteSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
          bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    simpa [hlen] using h805Raw
  have hheaderPost :
      bytesStoreLiteSetMappedByteHeaderWord σ' I =
        bytesStoreLiteSetMappedByteShortStoredWord σ I := by
    dsimp [σ', bytesStoreLiteSetMappedByteHeaderWord]
    exact sstoreAccountMap_storage_findD_self_of_find_some_any σ I.codeOwner acc
      (bytesStoreLiteSetMappedByteSlot I)
      (bytesStoreLiteSetMappedByteShortStoredWord σ I) hacc
  have hflagPost :
      UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ' I) ⟨1⟩ = ⟨0⟩ := by
    rw [hheaderPost, bytesStoreLiteSetMappedByteShortStoredWord_flag_eq
      (σ := σ) (I := I) (len := len) hshort hbound, hflag]
  have hltLen : UInt256.lt len ⟨32⟩ = ⟨1⟩ := by
    exact ult_one (by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
  have hvalidLen : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hltLen]
    native_decide
  have hlenPost :
      UInt256.land (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ' I) ⟨2⟩) ⟨127⟩ =
        len := by
    rw [hheaderPost, bytesStoreLiteSetMappedByteShortStoredWord_shortLen_eq
      (σ := σ) (I := I) (len := len) hshort hbound]
    exact hlen.symm
  have hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreLiteSetMappedByteHeaderWord σ' I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStoreLiteSetMappedByteHeaderWord σ' I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflagPost, hlenPost] using hvalidLen
  have hreadRaw := bytesStoreLiteX_setMappedByteShortWriteReturnDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) h805 hbound hflag
    (by simpa [σ'] using hflagPost)
    (by simpa [σ'] using hvalidPost)
    hperm
  have hread :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨905⟩
        [len, bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteSlot I, ⟨0⟩,
          bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
          bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩
          (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem))
        (UInt256.ofNat 3) ByteArray.empty (cA, σ') k C := by
    simpa [σ', hlenPost] using hreadRaw
  have hheader :
      ((σ'.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetMappedByteSlot I) ⟨0⟩)) =
          bytesStoreLiteSetMappedByteShortStoredWord σ I := by
    simpa [σ'] using
      sstoreAccountMap_storage_findD_self_of_find_some_any σ I.codeOwner acc
        (bytesStoreLiteSetMappedByteSlot I)
        (bytesStoreLiteSetMappedByteShortStoredWord σ I) hacc
  have hbyteAt :
      UInt256.byteAt (bytesStoreLiteSetMappedByteIndexWord I)
          (bytesStoreLiteSetMappedByteShortStoredWord σ I) =
        bytesStoreLiteSetMappedByteValueWord I :=
    bytesStoreLiteSetMappedByteShortStoredWord_byteAt
      (σ := σ) (I := I) (len := len) hcanon hshort hbound
  have hbyte :
      UInt256.shiftRight
        (UInt256.mul
          (UInt256.byteAt (bytesStoreLiteSetMappedByteIndexWord I)
            (bytesStoreLiteSetMappedByteShortStoredWord σ I))
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreLiteSetMappedByteValueWord I := by
    rw [hbyteAt]
    exact bytesStoreLiteSetMappedByteValueHighMulShiftRight hcanon
  have hret := bytesStoreLiteX_setMappedByteShortReadReturn
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := len)
    (header := bytesStoreLiteSetMappedByteShortStoredWord σ I)
    (mem := twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩
      (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem))
    (twoWordHashMem_size_96 _ _
      (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
    (twoWordHashMem_read64 _ _
      (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
      (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64))
    hread hbound hheader
    (by simpa [hheaderPost] using hflagPost)
    hbyte
    (bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon)
  simpa [σ'] using hret

theorem bytesStoreLiteX_setMappedByteLongSuccessReturn
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256} {acc : Account}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨772⟩
      [bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
        bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcanon : (bytesStoreLiteSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
      ⟨0⟩)
    (hperm : I.perm = true)
    (hacc : σ.find? I.codeOwner = some acc) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedByteLongDataSlot I)
        (bytesStoreLiteSetMappedByteLongStoredWord σ I))
      (UInt256.toByteArray (bytesStoreLiteSetMappedByteValueWord I)) := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedByteLongDataSlot I)
    (bytesStoreLiteSetMappedByteLongStoredWord σ I)
  have hdec := bytesStoreLiteX_setMappedByteReachLengthDecoder (g := g) hreach
  have h805Raw := bytesStoreLiteX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := g) hdec hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h805 :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨805⟩
        [len, bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteSlot I,
          UInt256.shiftLeft (bytesStoreLiteSetMappedByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
          bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    simpa [hlen] using h805Raw
  have hheaderPost :
      bytesStoreLiteSetMappedByteHeaderWord σ' I =
        bytesStoreLiteSetMappedByteHeaderWord σ I := by
    simpa [σ', bytesStoreLiteSetMappedByteHeaderWord,
      bytesStoreLiteSetMappedByteLongDataSlot] using
        bytesStoreLiteBytesHeaderWordAfterDataSstore_eq_of_before
          (σ := σ) (I := I) (baseSlot := bytesStoreLiteSetMappedByteSlot I)
          (idx := bytesStoreLiteSetMappedByteIndexWord I)
          (val := bytesStoreLiteSetMappedByteLongStoredWord σ I) (by rfl)
  have hflagPost :
      UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ' I) ⟨1⟩ ≠ ⟨0⟩ := by
    simpa [hheaderPost] using hflag
  have hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreLiteSetMappedByteHeaderWord σ' I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreLiteSetMappedByteHeaderWord σ' I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hheaderPost] using hvalid
  have hreadRaw := bytesStoreLiteX_setMappedByteLongWriteReturnDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) h805 hbound hflag
    (by simpa [σ'] using hflagPost)
    (by simpa [σ'] using hvalidPost)
    hperm
  have hread :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨905⟩
        [len, bytesStoreLiteSetMappedByteIndexWord I, bytesStoreLiteSetMappedByteSlot I, ⟨0⟩,
          bytesStoreLiteSetMappedByteValueWord I, bytesStoreLiteSetMappedByteIndexWord I,
          bytesStoreLiteSetMappedByteKeyWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩
          (wordAt0Mem (bytesStoreLiteSetMappedByteSlot I)
            (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem)))
        (UInt256.ofNat 3) ByteArray.empty (cA, σ') k C := by
    simpa [σ', hheaderPost, hlen] using hreadRaw
  have hheader :
      ((σ'.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetMappedByteSlot I) ⟨0⟩)) =
          bytesStoreLiteSetMappedByteHeaderWord σ I := by
    simpa [σ', bytesStoreLiteSetMappedByteHeaderWord,
      bytesStoreLiteSetMappedByteLongDataSlot] using
        bytesStoreLiteBytesHeaderWordAfterDataSstore_eq_of_before
          (σ := σ) (I := I) (baseSlot := bytesStoreLiteSetMappedByteSlot I)
          (idx := bytesStoreLiteSetMappedByteIndexWord I)
          (val := bytesStoreLiteSetMappedByteLongStoredWord σ I) (by rfl)
  have hdata :
      ((σ'.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetMappedByteLongDataSlot I) ⟨0⟩)) =
          bytesStoreLiteSetMappedByteLongStoredWord σ I := by
    simpa [σ'] using
      sstoreAccountMap_storage_findD_self_of_find_some_any σ I.codeOwner acc
        (bytesStoreLiteSetMappedByteLongDataSlot I)
        (bytesStoreLiteSetMappedByteLongStoredWord σ I) hacc
  have hbyteAt :
      UInt256.byteAt (bytesStoreLiteSetMappedByteLongWordIndex I)
          (bytesStoreLiteSetMappedByteLongStoredWord σ I) =
        bytesStoreLiteSetMappedByteValueWord I :=
    bytesStoreLiteSetMappedByteLongStoredWord_byteAt (σ := σ) (I := I) hcanon
  have hbyte :
      UInt256.shiftRight
        (UInt256.mul
          (UInt256.byteAt (bytesStoreLiteSetMappedByteLongWordIndex I)
            (bytesStoreLiteSetMappedByteLongStoredWord σ I))
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreLiteSetMappedByteValueWord I := by
    rw [hbyteAt]
    exact bytesStoreLiteSetMappedByteValueHighMulShiftRight hcanon
  let readMem : ByteArray :=
    twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩
      (wordAt0Mem (bytesStoreLiteSetMappedByteSlot I)
        (twoWordHashMem (bytesStoreLiteSetMappedByteKeyWord I) ⟨4⟩ solcFreePtrMem))
  have hreadMemSize : readMem.size = 96 := by
    exact twoWordHashMem_size_96 _ _
      (wordAt0Mem_size_96 _
        (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
  have hreadMem64 :
      readMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    exact twoWordHashMem_read64 _ _
      (wordAt0Mem_size_96 _
        (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
      (bytesStoreLiteWordAt0Mem_read64 _
        (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
        (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64))
  have hret := bytesStoreLiteX_setMappedByteLongReadReturn
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := len)
    (header := bytesStoreLiteSetMappedByteHeaderWord σ I)
    (dataWord := bytesStoreLiteSetMappedByteLongStoredWord σ I)
    (mem := readMem)
    hreadMemSize hreadMem64
    (by simpa [readMem] using hread)
    hbound hheader hflag hdata hbyte
    (bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon)
  simpa [σ', readMem] using hret

theorem bytesStoreLiteSetMappedByteShortSuccessRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len =
      UInt256.land (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetMappedByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetMappedByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨319⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetMappedByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setMappedByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreLiteDispatch_setMappedByte (cd := I.calldata)
    (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setMappedByte (I := I) hsz100 hhi hcanon
  have hret := bytesStoreLiteX_setMappedByteShortSuccessReturn
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len) (acc := accEvm)
    hreachBody hcanon hlen hshort hbound hflag hvalid hperm haccEvm
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreLiteSetMappedByteSlot I)
    (bytesStoreLiteSetMappedByteShortStoredWord σ_evm I)
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetMappedByteSlot I) =
        bytesStoreLiteSetMappedByteHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetMappedByteHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  obtain ⟨accSolm, haccSolm⟩ :=
    accountMapEquiv_find?_some_exists hAccounts haccEvm
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetMappedByteLocals I) setMappedByteTransition.body
        (.returned
          (bytesStoreLiteSetMappedByteFrame I)
          evmSolm1 (some (bytesStoreLiteSetMappedByteValue I))) := by
    simpa [evmSolm0, evmSolm1, initState, bytesStoreLiteSetMappedByteFrame] using
      bytesStoreLiteSetMappedByteShortBodyReturns
        (evm := evmSolm0) (σ := σ_evm) (I := I) (len := len) (acc := accSolm)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadHeader
        (by simpa [evmSolm0, initState] using haccSolm)
        hcanon hlen hshort hbound hflag hvalid
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetMappedByteSlot I)
          (bytesStoreLiteSetMappedByteShortStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simp [evmSolm1, evmSolm0, initState, storageStore_accountMap]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner
      (bytesStoreLiteSetMappedByteSlot I)
      (bytesStoreLiteSetMappedByteShortStoredWord σ_evm I) hAccounts
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    hpostAccounts
    (returnEquiv_of_encode (uint8ReturnEncoding (bytesStoreLiteSetMappedByteValueWord I) hcanon))

theorem bytesStoreLiteSetMappedByteLongSuccessRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetMappedByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠
      ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetMappedByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetMappedByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨319⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetMappedByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setMappedByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreLiteDispatch_setMappedByte (cd := I.calldata)
    (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setMappedByte (I := I) hsz100 hhi hcanon
  have hret := bytesStoreLiteX_setMappedByteLongSuccessReturn
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len) (acc := accEvm)
    hreachBody hcanon hlen hbound hflag hvalid hperm haccEvm
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreLiteSetMappedByteLongDataSlot I)
    (bytesStoreLiteSetMappedByteLongStoredWord σ_evm I)
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetMappedByteSlot I) =
        bytesStoreLiteSetMappedByteHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetMappedByteHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadData :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetMappedByteLongDataSlot I) =
        bytesStoreLiteSetMappedByteLongOldWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetMappedByteLongData_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  obtain ⟨accSolm, haccSolm⟩ :=
    accountMapEquiv_find?_some_exists hAccounts haccEvm
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetMappedByteLocals I) setMappedByteTransition.body
        (.returned
          (bytesStoreLiteSetMappedByteFrame I)
          evmSolm1 (some (bytesStoreLiteSetMappedByteValue I))) := by
    simpa [evmSolm0, evmSolm1, initState, bytesStoreLiteSetMappedByteFrame] using
      bytesStoreLiteSetMappedByteLongBodyReturns
        (evm := evmSolm0) (σ := σ_evm) (I := I) (len := len) (acc := accSolm)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadHeader hloadData
        (by simpa [evmSolm0, initState] using haccSolm)
        hcanon hlen hbound hflag hvalid
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetMappedByteLongDataSlot I)
          (bytesStoreLiteSetMappedByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simp [evmSolm1, evmSolm0, initState, storageStore_accountMap]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner
      (bytesStoreLiteSetMappedByteLongDataSlot I)
      (bytesStoreLiteSetMappedByteLongStoredWord σ_evm I) hAccounts
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    hpostAccounts
    (returnEquiv_of_encode (uint8ReturnEncoding (bytesStoreLiteSetMappedByteValueWord I) hcanon))

theorem bytesStoreLiteSetMappedByteRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hsz100 : 100 ≤ I.calldata.size
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (bytesStoreLiteSetMappedByteValueWord I).toNat < EVM.twoPow 8
      · by_cases hflagLong :
          UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩
        · by_cases hvalidLong :
            UInt256.sub (UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨1⟩)
              (UInt256.lt (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
                ⟨32⟩) ≠ ⟨0⟩
          · let len := UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨2⟩
            by_cases hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat
            · by_cases haccSome : ∃ accEvm, σ_evm.find? I.codeOwner = some accEvm
              · obtain ⟨accEvm, haccEq⟩ := haccSome
                exact bytesStoreLiteSetMappedByteLongSuccessRuntime
                  (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                  (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  (len := len) (accEvm := accEvm)
                  hcode hsize hperm hwv hsel hAccounts haccEq hsz100 hhi hcanon
                  (by rfl) hbound hflagLong hvalidLong
              · have haccNone : σ_evm.find? I.codeOwner = none := by
                  cases haccEq : σ_evm.find? I.codeOwner with
                  | none => rfl
                  | some accEvm => exact False.elim (haccSome ⟨accEvm, haccEq⟩)
                have hhdr :
                    bytesStoreLiteSetMappedByteHeaderWord σ_evm I = ⟨0⟩ := by
                  simp [bytesStoreLiteSetMappedByteHeaderWord, haccNone, Option.option]
                have hflag0 :
                    UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨1⟩ =
                      ⟨0⟩ := by
                  rw [hhdr]
                  native_decide
                exact False.elim (hflagLong hflag0)
            · exact bytesStoreLiteSetMappedByteOobLongRuntime
                (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hcode hsize hperm hwv hsel hAccounts hsz100 hhi hcanon
                hflagLong hvalidLong hbound
          · have hbad :
              UInt256.sub (UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨1⟩)
                (UInt256.lt (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
                  ⟨32⟩) = ⟨0⟩ := by
              by_contra hne
              exact hvalidLong hne
            exact bytesStoreLiteSetMappedByteLongMalformedRuntime
              (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
              (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hcode hsize hperm hwv hsel hAccounts hsz100 hhi hcanon
              hflagLong hbad
        · have hflagShort :
            UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ := by
            by_contra hne
            exact hflagLong hne
          by_cases hvalidShort :
              UInt256.sub (UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨1⟩)
                (UInt256.lt
                  (UInt256.land
                    (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
                    ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
          · let len :=
              UInt256.land
                (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
            have hltNe : UInt256.lt len ⟨32⟩ ≠ ⟨0⟩ := by
              intro hlt0
              have hzero : UInt256.sub ⟨0⟩ ⟨0⟩ = (⟨0⟩ : UInt256) := by
                native_decide
              exact hvalidShort (by simpa [len, hflagShort, hlt0] using hzero)
            have hshort : len.toNat < 32 := by
              have hlt := ult_ne_zero_toNat_lt hltNe
              simpa using hlt
            by_cases hbound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < len.toNat
            · by_cases haccSome : ∃ accEvm, σ_evm.find? I.codeOwner = some accEvm
              · obtain ⟨accEvm, haccEq⟩ := haccSome
                exact bytesStoreLiteSetMappedByteShortSuccessRuntime
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
                    bytesStoreLiteSetMappedByteHeaderWord σ_evm I = ⟨0⟩ := by
                  simp [bytesStoreLiteSetMappedByteHeaderWord, haccNone, Option.option]
                have hlenZero : len = ⟨0⟩ := by
                  change
                    UInt256.land
                      (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
                      ⟨127⟩ = ⟨0⟩
                  rw [hhdr]
                  native_decide
                have hlen0 : len.toNat = 0 := by
                  simp [hlenZero]
                have hbadBound : (bytesStoreLiteSetMappedByteIndexWord I).toNat < 0 := by
                  simp [hlen0] at hbound
                exact False.elim (Nat.not_lt_zero _ hbadBound)
            · exact bytesStoreLiteSetMappedByteOobShortRuntime
                (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hcode hsize hperm hwv hsel hAccounts hsz100 hhi hcanon
                hflagShort hvalidShort hbound
          · have hbad :
              UInt256.sub (UInt256.land (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨1⟩)
                (UInt256.lt
                  (UInt256.land
                    (UInt256.div (bytesStoreLiteSetMappedByteHeaderWord σ_evm I) ⟨2⟩)
                    ⟨127⟩) ⟨32⟩) = ⟨0⟩ := by
              by_contra hne
              exact hvalidShort hne
            exact bytesStoreLiteSetMappedByteShortMalformedRuntime
              (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
              (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hcode hsize hperm hwv hsel hAccounts hsz100 hhi hcanon
              hflagShort hbad
      · exact bytesStoreLiteSetMappedByteDecodeNoncanonValueRuntime
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hsize hperm hwv hsel hAccounts hsz100 hhi hcanon
    · exact bytesStoreLiteSetMappedByteDecodeHugeRuntime
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts (by omega)
  · exact bytesStoreLiteSetMappedByteDecodeShortRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts (by omega)

end BytesStoreLite
