import Examples.BytesStore.FullSetChunkByte

/-!
# BytesStore — `setChunkByte(uint256,uint256,uint8)` bytecode decoder

This module keeps the optimized-bytecode ABI decoder proof separate from the larger Solm/storage
body proof in `FullSetChunkByte.lean`, so decoder iteration does not force that file to grow further.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace BytesStore

theorem bytesStoreSetChunkByteChunksBaseHash :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem).readWithPadding 0 32))) =
      chunksDataBase := by
  rw [wordAt0Mem_read0]
  simpa [chunksDataBase, bytesLikeDataBase] using
    keccakSlot_eq (UInt256.toByteArray (⟨1⟩ : UInt256))

theorem bytesStoreSetChunkByteChunksBaseHashMem (mem : ByteArray) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((wordAt0Mem (⟨1⟩ : UInt256) mem).readWithPadding 0 32))) =
      chunksDataBase := by
  rw [wordAt0Mem_read0]
  simpa [chunksDataBase, bytesLikeDataBase] using
    keccakSlot_eq (UInt256.toByteArray (⟨1⟩ : UInt256))

theorem bytesStoreSetChunkByteLongBaseHashMem (I : ExecutionEnv) (mem : ByteArray) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((wordAt0Mem (bytesStoreSetChunkByteSlot I) mem).readWithPadding 0 32))) =
      bytesLikeDataBase (bytesStoreSetChunkByteSlot I) := by
  rw [wordAt0Mem_read0]
  simpa [bytesLikeDataBase] using
    keccakSlot_eq (UInt256.toByteArray (bytesStoreSetChunkByteSlot I))

private theorem bytesStoreSetChunkByteDecodeLenCheckOk {sz : ℕ}
    (hlen : 100 ≤ sz) (hhi : sz < 2 ^ 255 + 4) (hsz : sz < UInt256.size) :
    UInt256.slt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) ⟨96⟩ = ⟨0⟩ := by
  exact solcCalldataStaticLenCheckOk (words := 3) (by simpa using hlen) hhi hsz

private theorem bytesStoreSetChunkByteDecodeLenCheckShort {sz : ℕ}
    (hhead : 4 ≤ sz) (hshort : sz < 100) (hsz : sz < UInt256.size) :
    UInt256.slt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
  exact solcCalldataStaticLenCheckShort (words := 3) hhead (by simpa using hshort) hsz
    (by norm_num)

private theorem bytesStoreSetChunkByteDecodeLenCheckHuge {sz : ℕ}
    (hbig : 2 ^ 255 + 4 ≤ sz) (hsz : sz < UInt256.size) :
    UInt256.slt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
  exact solcCalldataStaticLenCheckHuge (words := 3) hbig hsz (by norm_num)

theorem bytesStoreSetChunkByteSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem bytesStoreX_setChunkByteDecodeValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨414⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hcanon : UInt256.land (bytesStoreSetChunkByteValueWord I) ⟨255⟩ =
      bytesStoreSetChunkByteValueWord I) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1226⟩
      [bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd414⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ :=
    bytesStoreSetChunkByteDecodeLenCheckOk hsz100 hhi hsize
  have rd2009 := evm_run rd414 with [
    jumpdest, push2 ⟨301⟩, push2 ⟨428⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨2009⟩, jump (by native_decide)]
  have rd2027 := evm_run rd2009 with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2027⟩, jumpiT (by rw [hslt]; decide) (by native_decide)]
  have rd1946 := evm_run rd2027 with [
    jumpdest, dup4, calldataload, swap3, pop, push1 ⟨32⟩, dup5, add, calldataload,
    swap2, pop, push2 ⟨2050⟩, push1 ⟨64⟩, dup6, add, push2 ⟨1946⟩,
    jump (by native_decide)]
  rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide,
    show uInt256OfByteArray (I.calldata.readBytes 4 32) =
      bytesStoreSetChunkByteChunkIndexWord I from rfl,
    show (⟨4⟩ + ⟨32⟩ : UInt256) = ⟨36⟩ from by native_decide,
    show (⟨4⟩ + ⟨64⟩ : UInt256) = ⟨68⟩ from by native_decide] at rd1946
  have rd1950 := evm_run rd1946 with [
    jumpdest, dup1, calldataload]
  rw [show (⟨68⟩ : UInt256).toNat = 68 from by decide,
    show uInt256OfByteArray (I.calldata.readBytes 68 32) =
      bytesStoreSetChunkByteValueWord I from rfl] at rd1950
  have rd2050 := evm_run rd1950 with [
    push1 ⟨255⟩, dup2, and, dup2, eq,
    push2 ⟨1962⟩,
    jumpiT (by rw [bytesStoreSetPacketByteUint8CanonEqGuard hcanon]; decide)
      (by native_decide),
    jumpdest, swap2, swap1, pop, jump (by native_decide)]
  exact ⟨_, _, evm_run rd2050 with [
    jumpdest, swap1, pop, swap3, pop, swap3, pop, swap3, jump (by native_decide),
    jumpdest, push2 ⟨1226⟩, jump (by native_decide)]⟩

theorem bytesStoreX_setChunkByteDecodeShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨414⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100)
    (hsize : I.calldata.size < UInt256.size) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd414⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ :=
    bytesStoreSetChunkByteDecodeLenCheckShort hsz4 hshort hsize
  have rd2009 := evm_run rd414 with [
    jumpdest, push2 ⟨301⟩, push2 ⟨428⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨2009⟩, jump (by native_decide)]
  exact evm_run rd2009 with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2027⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreX_setChunkByteDecodeHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨414⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd414⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ :=
    bytesStoreSetChunkByteDecodeLenCheckHuge hbig hsize
  have rd2009 := evm_run rd414 with [
    jumpdest, push2 ⟨301⟩, push2 ⟨428⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨2009⟩, jump (by native_decide)]
  exact evm_run rd2009 with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2027⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreX_setChunkByteDecodeNoncanonValue {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨414⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hnc : UInt256.land (bytesStoreSetChunkByteValueWord I) ⟨255⟩ ≠
      bytesStoreSetChunkByteValueWord I) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd414⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ :=
    bytesStoreSetChunkByteDecodeLenCheckOk hsz100 hhi hsize
  have rd2009 := evm_run rd414 with [
    jumpdest, push2 ⟨301⟩, push2 ⟨428⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨2009⟩, jump (by native_decide)]
  have rd2027 := evm_run rd2009 with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2027⟩, jumpiT (by rw [hslt]; decide) (by native_decide)]
  have rd1946 := evm_run rd2027 with [
    jumpdest, dup4, calldataload, swap3, pop, push1 ⟨32⟩, dup5, add, calldataload,
    swap2, pop, push2 ⟨2050⟩, push1 ⟨64⟩, dup6, add, push2 ⟨1946⟩,
    jump (by native_decide)]
  rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide,
    show uInt256OfByteArray (I.calldata.readBytes 4 32) =
      bytesStoreSetChunkByteChunkIndexWord I from rfl,
    show (⟨4⟩ + ⟨32⟩ : UInt256) = ⟨36⟩ from by native_decide,
    show (⟨4⟩ + ⟨64⟩ : UInt256) = ⟨68⟩ from by native_decide] at rd1946
  have rd1950 := evm_run rd1946 with [
    jumpdest, dup1, calldataload]
  rw [show (⟨68⟩ : UInt256).toNat = 68 from by decide,
    show uInt256OfByteArray (I.calldata.readBytes 68 32) =
      bytesStoreSetChunkByteValueWord I from rfl] at rd1950
  exact evm_run rd1950 with [
    push1 ⟨255⟩, dup2, and, dup2, eq,
    push2 ⟨1962⟩,
    jumpiNT (by rw [bytesStoreSetPacketByteUint8NoncanonEqGuard hnc]),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreX_setChunkByteReachLengthDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1226⟩
      [bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ I).toNat) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [bytesStoreSetChunkByteHeaderWord σ I, ⟨1270⟩,
        bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I,
        UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1226⟩ := hreach
  have hlt :
      UInt256.lt (bytesStoreSetChunkByteChunkIndexWord I)
        (bytesStoreChunksLengthWord σ I) = ⟨1⟩ :=
    ult_one hbound
  have hslot := bytesStoreSetChunkByteChunksBaseHash
  have rd1236 := evm_run rd1226 with [
    jumpdest, push0, dup2, push1 ⟨248⟩, shl, push1 ⟨1⟩, dup6, dup2]
  obtain ⟨_, _, rd1237₀⟩ := rd1236.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1237⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1237⟩
        [bytesStoreChunksLengthWord σ I, bytesStoreSetChunkByteChunkIndexWord I,
          ⟨1⟩, UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
          bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreChunksLengthWord, initState] using rd1237₀⟩
  have rd1250 := evm_run rd1237 with [
    dup2, lt, push2 ⟨1250⟩, jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd1261 := evm_run rd1250 with [
    jumpdest, swap1, push0,
    raw mstore 0 (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256 0 chunksDataBase (UInt256.ofNat 3)
      (by native_decide) mem_cost hslot (by native_decide) (by evm_ov),
    add, dup5, dup2]
  obtain ⟨_, _, rd1262₀⟩ := rd1261.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1262⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1262⟩
        [bytesStoreSetChunkByteHeaderWord σ I, bytesStoreSetChunkByteIndexWord I,
          bytesStoreSetChunkByteSlot I,
          UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
          bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreSetChunkByteHeaderWord, bytesStoreSetChunkByteSlot,
        u256_add_comm chunksDataBase (bytesStoreSetChunkByteChunkIndexWord I),
        initState] using rd1262₀⟩
  exact ⟨_, _, evm_run rd1262 with [
    push2 ⟨1270⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreX_setChunkByteOobChunksLength {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1226⟩
      [bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound :
      ¬ (bytesStoreSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ I).toNat) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1226⟩ := hreach
  have hlt :
      UInt256.lt (bytesStoreSetChunkByteChunkIndexWord I)
        (bytesStoreChunksLengthWord σ I) = ⟨0⟩ :=
    ult_zero (by omega)
  have rd1236 := evm_run rd1226 with [
    jumpdest, push0, dup2, push1 ⟨248⟩, shl, push1 ⟨1⟩, dup6, dup2]
  obtain ⟨_, _, rd1237₀⟩ := rd1236.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1237⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1237⟩
        [bytesStoreChunksLengthWord σ I, bytesStoreSetChunkByteChunkIndexWord I,
          ⟨1⟩, UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
          bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreChunksLengthWord, initState] using rd1237₀⟩
  have rd2579 := evm_run rd1237 with [
    dup2, lt, push2 ⟨1250⟩, jumpiNT (by simpa using hlt),
    push2 ⟨1250⟩, push2 ⟨2579⟩, jump (by native_decide)]
  exact bytesStoreX_panic32Mem ⟨_, _, rd2579⟩
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setChunkByteOobAfterLength {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1270⟩
      [len, bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I,
        UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hbound : ¬ (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1270⟩ := hreach
  have hlt : UInt256.lt (bytesStoreSetChunkByteIndexWord I) len = ⟨0⟩ :=
    ult_zero (by omega)
  have rd2579 := evm_run rd1270 with [
    jumpdest, dup2, lt, push2 ⟨1284⟩,
    jumpiNT (by simpa using hlt),
    push2 ⟨1284⟩, push2 ⟨2579⟩, jump (by native_decide)]
  exact bytesStoreX_panic32Mem ⟨_, _, rd2579⟩
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setChunkByteOobLong {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1226⟩
      [bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hchunkBound :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ I).toNat)
    (hflag : UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hbound :
      ¬ (bytesStoreSetChunkByteIndexWord I).toNat <
        (UInt256.div (bytesStoreSetChunkByteHeaderWord σ I) ⟨2⟩).toNat) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdec := bytesStoreX_setChunkByteReachLengthDecoder hreach hchunkBound
  have hlen := bytesStoreX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := g) hdec hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreX_setChunkByteOobAfterLength (g := g) hlen hbound

theorem bytesStoreX_setChunkByteOobShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1226⟩
      [bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hchunkBound :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ I).toNat)
    (hflag : UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hbound :
      ¬ (bytesStoreSetChunkByteIndexWord I).toNat <
        (UInt256.land (UInt256.div (bytesStoreSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨127⟩).toNat) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdec := bytesStoreX_setChunkByteReachLengthDecoder hreach hchunkBound
  have hlen := bytesStoreX_bytesLengthDecoderShortValidMem
    (A := A) (I := I) (g := g) hdec hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreX_setChunkByteOobAfterLength (g := g) hlen hbound

theorem bytesStoreX_setChunkByteLongMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1226⟩
      [bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hchunkBound :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ I).toNat)
    (hflag : UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdec := bytesStoreX_setChunkByteReachLengthDecoder (g := g) hreach hchunkBound
  exact bytesStoreX_bytesLengthDecoderLongMalformedMem
    hdec hflag hbad (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setChunkByteShortMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1226⟩
      [bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hchunkBound :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ I).toNat)
    (hflag : UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdec := bytesStoreX_setChunkByteReachLengthDecoder (g := g) hreach hchunkBound
  exact bytesStoreX_bytesLengthDecoderShortMalformedMem
    hdec hflag hbad (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setChunkByteShortReachStoreCommon {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1270⟩
      [len, bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I,
        UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1313⟩
      [bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I,
        UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1270⟩ := hreach
  have hlt : UInt256.lt (bytesStoreSetChunkByteIndexWord I) len = ⟨1⟩ :=
    ult_one hbound
  have rd1284 := evm_run rd1270 with [
    jumpdest, dup2, lt, push2 ⟨1284⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd1286 := evm_run rd1284 with [jumpdest, dup2]
  obtain ⟨_, _, rd1287₀⟩ := rd1286.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1287⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1287⟩
        [bytesStoreSetChunkByteHeaderWord σ I, bytesStoreSetChunkByteIndexWord I,
          bytesStoreSetChunkByteSlot I,
          UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
          bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreSetChunkByteHeaderWord, initState] using rd1287₀⟩
  have rd1313 := evm_run rd1287 with [
    push1 ⟨1⟩, and, iszero, push2 ⟨1313⟩,
    jumpiT (by
      rw [u256_land_comm, hflag]
      decide)
      (by native_decide)]
  exact ⟨_, _, rd1313⟩

theorem bytesStoreX_setChunkByteLongReachStoreCommon {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1270⟩
      [len, bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I,
        UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1313⟩
      [bytesStoreSetChunkByteLongWordIndex I, bytesStoreSetChunkByteLongDataSlot I,
        UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      (wordAt0Mem (bytesStoreSetChunkByteSlot I)
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1270⟩ := hreach
  have hlt : UInt256.lt (bytesStoreSetChunkByteIndexWord I) len = ⟨1⟩ :=
    ult_one hbound
  have hflagOne :
      UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩ = ⟨1⟩ :=
    u256_land_one_eq_one_of_ne_zero hflag
  have hslot := bytesStoreSetChunkByteLongBaseHashMem I
    (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
  have rd1284 := evm_run rd1270 with [
    jumpdest, dup2, lt, push2 ⟨1284⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd1286 := evm_run rd1284 with [jumpdest, dup2]
  obtain ⟨_, _, rd1287₀⟩ := rd1286.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1287⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1287⟩
        [bytesStoreSetChunkByteHeaderWord σ I, bytesStoreSetChunkByteIndexWord I,
          bytesStoreSetChunkByteSlot I,
          UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
          bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreSetChunkByteHeaderWord, initState] using rd1287₀⟩
  have rd1312 := evm_run rd1287 with [
    push1 ⟨1⟩, and, iszero, push2 ⟨1313⟩,
    jumpiNT (by
      rw [u256_land_comm, hflagOne]
      decide),
    swap1, push0,
    raw mstore 0 (wordAt0Mem (bytesStoreSetChunkByteSlot I)
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256 0 (bytesLikeDataBase (bytesStoreSetChunkByteSlot I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost hslot (by native_decide) (by evm_ov),
    swap1, push1 ⟨32⟩, swap2, dup3, dup3, div, add, swap2, swap1]
  have rd1313raw := RD.mod rd1312 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa [bytesStoreSetChunkByteLongWordIndex,
      bytesStoreSetChunkByteLongDataSlot,
      u256_add_comm (UInt256.div (bytesStoreSetChunkByteIndexWord I) ⟨32⟩)
        (bytesLikeDataBase (bytesStoreSetChunkByteSlot I))] using rd1313raw⟩

theorem bytesStoreX_setChunkByteShortStore {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1313⟩
      [bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I,
        UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1342⟩
      [⟨0⟩, bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteSlot I)
        (bytesStoreSetChunkByteShortStoredWord σ I)) k C := by
  obtain ⟨_, _, rd1313⟩ := hreach
  have rd1322 := evm_run rd1313 with [
    jumpdest, push1 ⟨31⟩, sub, push2 ⟨256⟩, exp, dup2]
  obtain ⟨_, _, rd1323₀⟩ := rd1322.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1323⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
        [bytesStoreSetChunkByteHeaderWord σ I,
          UInt256.exp ⟨256⟩ (UInt256.sub ⟨31⟩
            (bytesStoreSetChunkByteIndexWord I)),
          bytesStoreSetChunkByteSlot I,
          UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
          bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreSetChunkByteHeaderWord, initState] using rd1323₀⟩
  have rd1340 := evm_run rd1323 with [
    dup2, push1 ⟨255⟩, mul, not, and, swap1,
    push1 ⟨1⟩, push1 ⟨248⟩, shl, dup5, div, mul, lor, swap1]
  obtain ⟨_, _, rd1340'⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1340⟩
        [bytesStoreSetChunkByteSlot I,
          bytesStoreSetChunkByteShortStoredWord σ I,
          UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
          bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreSetChunkByteShortStoredWord,
        bytesStoreSetChunkByteShortScale] using rd1340⟩
  obtain ⟨_, _, rd1341₀⟩ := rd1340'.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1341⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1341⟩
        [UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
          bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteSlot I)
          (bytesStoreSetChunkByteShortStoredWord σ I)) k C := by
    exact ⟨_, _, by simpa [sstoreAccountMap, initState] using rd1341₀⟩
  exact ⟨_, _, evm_run rd1341 with [pop]⟩

theorem bytesStoreX_setChunkByteLongStore {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1313⟩
      [bytesStoreSetChunkByteLongWordIndex I, bytesStoreSetChunkByteLongDataSlot I,
        UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      (wordAt0Mem (bytesStoreSetChunkByteSlot I)
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1342⟩
      [⟨0⟩, bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      (wordAt0Mem (bytesStoreSetChunkByteSlot I)
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)) (UInt256.ofNat 3)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
        (bytesStoreSetChunkByteLongStoredWord σ I)) k C := by
  obtain ⟨_, _, rd1313⟩ := hreach
  have rd1322 := evm_run rd1313 with [
    jumpdest, push1 ⟨31⟩, sub, push2 ⟨256⟩, exp, dup2]
  obtain ⟨_, _, rd1323₀⟩ := rd1322.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1323⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
        [bytesStoreSetChunkByteLongOldWord σ I,
          UInt256.exp ⟨256⟩ (UInt256.sub ⟨31⟩
            (bytesStoreSetChunkByteLongWordIndex I)),
          bytesStoreSetChunkByteLongDataSlot I,
          UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
          bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
        (wordAt0Mem (bytesStoreSetChunkByteSlot I)
          (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreSetChunkByteLongOldWord, initState] using rd1323₀⟩
  have rd1340 := evm_run rd1323 with [
    dup2, push1 ⟨255⟩, mul, not, and, swap1,
    push1 ⟨1⟩, push1 ⟨248⟩, shl, dup5, div, mul, lor, swap1]
  obtain ⟨_, _, rd1340'⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1340⟩
        [bytesStoreSetChunkByteLongDataSlot I,
          bytesStoreSetChunkByteLongStoredWord σ I,
          UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
          bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
        (wordAt0Mem (bytesStoreSetChunkByteSlot I)
          (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreSetChunkByteLongStoredWord,
        bytesStoreSetChunkByteLongScale] using rd1340⟩
  obtain ⟨_, _, rd1341₀⟩ := rd1340'.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1341⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1341⟩
        [UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
          bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
        (wordAt0Mem (bytesStoreSetChunkByteSlot I)
          (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)) (UInt256.ofNat 3)
        ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
          (bytesStoreSetChunkByteLongStoredWord σ I)) k C := by
    exact ⟨_, _, by simpa [sstoreAccountMap, initState] using rd1341₀⟩
  exact ⟨_, _, evm_run rd1341 with [pop]⟩

theorem bytesStoreX_setChunkByteReturnReachLengthDecoderMem
    {cA gh bl σinit σ σ₀ A I} {g : Sat256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1342⟩
      [⟨0⟩, bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ I).toNat) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      [bytesStoreSetChunkByteHeaderWord σ I, ⟨905⟩,
        bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I, ⟨0⟩,
        bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) mem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1342⟩ := hreach
  have hlt :
      UInt256.lt (bytesStoreSetChunkByteChunkIndexWord I)
        (bytesStoreChunksLengthWord σ I) = ⟨1⟩ :=
    ult_one hbound
  have hslot := bytesStoreSetChunkByteChunksBaseHashMem mem
  have rd1346 := evm_run rd1342 with [
    push1 ⟨1⟩, dup5, dup2]
  obtain ⟨_, _, rd1347₀⟩ := rd1346.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1347⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1347⟩
        [bytesStoreChunksLengthWord σ I, bytesStoreSetChunkByteChunkIndexWord I,
          ⟨1⟩, ⟨0⟩, bytesStoreSetChunkByteValueWord I,
          bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteChunkIndexWord I,
          ⟨301⟩, bytesStoreSelWord I]
        mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreChunksLengthWord, initState] using rd1347₀⟩
  have rd1360 := evm_run rd1347 with [
    dup2, lt, push2 ⟨1360⟩, jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd1371 := evm_run rd1360 with [
    jumpdest, swap1, push0,
    raw mstore 0 (wordAt0Mem (⟨1⟩ : UInt256) mem)
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256 0 chunksDataBase (UInt256.ofNat 3)
      (by native_decide) mem_cost hslot (by native_decide) (by evm_ov),
    add, dup4, dup2]
  obtain ⟨_, _, rd1372₀⟩ := rd1371.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1372⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1372⟩
        [bytesStoreSetChunkByteHeaderWord σ I, bytesStoreSetChunkByteIndexWord I,
          bytesStoreSetChunkByteSlot I, ⟨0⟩,
          bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
          bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) mem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreSetChunkByteHeaderWord, bytesStoreSetChunkByteSlot,
        u256_add_comm chunksDataBase (bytesStoreSetChunkByteChunkIndexWord I),
        initState] using rd1372₀⟩
  exact ⟨_, _, evm_run rd1372 with [
    push2 ⟨905⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreX_setChunkByteReturnOobChunksLengthMem
    {cA gh bl σinit σ σ₀ A I} {g : Sat256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1342⟩
      [⟨0⟩, bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound :
      ¬ (bytesStoreSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ I).toNat) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2579⟩
      [⟨1360⟩, bytesStoreSetChunkByteChunkIndexWord I, ⟨1⟩, ⟨0⟩,
        bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1342⟩ := hreach
  have hlt :
      UInt256.lt (bytesStoreSetChunkByteChunkIndexWord I)
        (bytesStoreChunksLengthWord σ I) = ⟨0⟩ :=
    ult_zero (by omega)
  have rd1346 := evm_run rd1342 with [
    push1 ⟨1⟩, dup5, dup2]
  obtain ⟨_, _, rd1347₀⟩ := rd1346.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1347⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1347⟩
        [bytesStoreChunksLengthWord σ I, bytesStoreSetChunkByteChunkIndexWord I,
          ⟨1⟩, ⟨0⟩, bytesStoreSetChunkByteValueWord I,
          bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteChunkIndexWord I,
          ⟨301⟩, bytesStoreSelWord I]
        mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreChunksLengthWord, initState] using rd1347₀⟩
  have rd2579 := evm_run rd1347 with [
    dup2, lt, push2 ⟨1360⟩, jumpiNT (by simpa using hlt),
    push2 ⟨1360⟩, push2 ⟨2579⟩, jump (by native_decide)]
  exact ⟨_, _, rd2579⟩

theorem bytesStoreX_panic32MemFromReach {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {stk : List UInt256} {mem : ByteArray}
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

theorem bytesStoreX_setChunkByteReturnOobChunksLength
    {cA gh bl σinit σ σ₀ A I} {g : Sat256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1342⟩
      [⟨0⟩, bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound :
      ¬ (bytesStoreSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ I).toNat) :
    RDrev bytesStoreBytecode g (initState cA gh bl σinit σ₀ g A I) := by
  exact bytesStoreX_panic32MemFromReach
    (bytesStoreX_setChunkByteReturnOobChunksLengthMem hreach hbound)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setChunkByteReturnOobLength
    {cA gh bl σinit σ σ₀ A I} {g : Sat256} {len : UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨905⟩
      [len, bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I, ⟨0⟩,
        bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : ¬ (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat) :
    RDrev bytesStoreBytecode g (initState cA gh bl σinit σ₀ g A I) := by
  obtain ⟨_, _, rd905⟩ := hreach
  have hlt : UInt256.lt (bytesStoreSetChunkByteIndexWord I) len = ⟨0⟩ :=
    ult_zero (by omega)
  have rd2579 := evm_run rd905 with [
    jumpdest, dup2, lt, push2 ⟨919⟩,
    jumpiNT (by simpa using hlt),
    push2 ⟨919⟩, push2 ⟨2579⟩, jump (by native_decide)]
  exact bytesStoreX_panic32MemFromReach ⟨_, _, rd2579⟩
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setChunkByteLongWriteReturnReachLengthDecoder
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1270⟩
      [len, bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I,
        UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hchunkBoundPost :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
            (bytesStoreSetChunkByteLongStoredWord σ I)) I).toNat)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [bytesStoreSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
            (bytesStoreSetChunkByteLongStoredWord σ I)) I,
        ⟨905⟩, bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I,
        ⟨0⟩, bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256)
        (wordAt0Mem (bytesStoreSetChunkByteSlot I)
          (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))) (UInt256.ofNat 3)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
        (bytesStoreSetChunkByteLongStoredWord σ I)) k C := by
  have h1313 := bytesStoreX_setChunkByteLongReachStoreCommon
    (g := g) hreach hbound hflag
  have h1342 := bytesStoreX_setChunkByteLongStore
    (g := g) h1313 hperm
  exact bytesStoreX_setChunkByteReturnReachLengthDecoderMem
    (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
      (bytesStoreSetChunkByteLongStoredWord σ I))
    h1342 hchunkBoundPost

theorem bytesStoreX_setChunkByteShortWriteReturnReachLengthDecoder
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1270⟩
      [len, bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I,
        UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hchunkBoundPost :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteSlot I)
            (bytesStoreSetChunkByteShortStoredWord σ I)) I).toNat)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [bytesStoreSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteSlot I)
            (bytesStoreSetChunkByteShortStoredWord σ I)) I,
        ⟨905⟩, bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I,
        ⟨0⟩, bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256)
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)) (UInt256.ofNat 3)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteSlot I)
        (bytesStoreSetChunkByteShortStoredWord σ I)) k C := by
  have h1313 := bytesStoreX_setChunkByteShortReachStoreCommon
    (g := g) hreach hbound hflag
  have h1342 := bytesStoreX_setChunkByteShortStore
    (g := g) h1313 hperm
  exact bytesStoreX_setChunkByteReturnReachLengthDecoderMem
    (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteSlot I)
      (bytesStoreSetChunkByteShortStoredWord σ I))
    h1342 hchunkBoundPost

theorem bytesStoreX_setChunkByteLongWriteReturnOobChunksLength
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1270⟩
      [len, bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I,
        UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hchunkBoundPost :
      ¬ (bytesStoreSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
            (bytesStoreSetChunkByteLongStoredWord σ I)) I).toNat)
    (hperm : I.perm = true) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h1313 := bytesStoreX_setChunkByteLongReachStoreCommon
    (g := g) hreach hbound hflag
  have h1342 := bytesStoreX_setChunkByteLongStore
    (g := g) h1313 hperm
  exact bytesStoreX_setChunkByteReturnOobChunksLength
    (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
      (bytesStoreSetChunkByteLongStoredWord σ I))
    h1342 hchunkBoundPost

theorem bytesStoreX_setChunkByteShortWriteReturnOobChunksLength
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1270⟩
      [len, bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I,
        UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hchunkBoundPost :
      ¬ (bytesStoreSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteSlot I)
            (bytesStoreSetChunkByteShortStoredWord σ I)) I).toNat)
    (hperm : I.perm = true) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h1313 := bytesStoreX_setChunkByteShortReachStoreCommon
    (g := g) hreach hbound hflag
  have h1342 := bytesStoreX_setChunkByteShortStore
    (g := g) h1313 hperm
  exact bytesStoreX_setChunkByteReturnOobChunksLength
    (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteSlot I)
      (bytesStoreSetChunkByteShortStoredWord σ I))
    h1342 hchunkBoundPost

theorem bytesStoreX_setChunkByteLongWriteReturnLongMalformed
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1270⟩
      [len, bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I,
        UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hchunkBoundPost :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
            (bytesStoreSetChunkByteLongStoredWord σ I)) I).toNat)
    (hflagPost : UInt256.land
        (bytesStoreSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
            (bytesStoreSetChunkByteLongStoredWord σ I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hbadPost : UInt256.sub (UInt256.land
        (bytesStoreSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
            (bytesStoreSetChunkByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreSetChunkByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
              (bytesStoreSetChunkByteLongStoredWord σ I)) I) ⟨2⟩) ⟨32⟩) = ⟨0⟩)
    (hperm : I.perm = true) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
    (bytesStoreSetChunkByteLongStoredWord σ I)
  have hdec := bytesStoreX_setChunkByteLongWriteReturnReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag hchunkBoundPost hperm
  exact bytesStoreX_bytesLengthDecoderLongMalformedMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := bytesStoreSetChunkByteHeaderWord σ' I) (ret := ⟨905⟩)
    (rest := [bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I,
      ⟨0⟩, bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
      bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem (bytesStoreSetChunkByteSlot I)
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
    (by simpa [σ'] using hdec)
    (by simpa [σ'] using hflagPost)
    (by simpa [σ'] using hbadPost)
    (by simp)

theorem bytesStoreX_setChunkByteLongWriteReturnShortMalformed
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1270⟩
      [len, bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I,
        UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hchunkBoundPost :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
            (bytesStoreSetChunkByteLongStoredWord σ I)) I).toNat)
    (hflagPost : UInt256.land
        (bytesStoreSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
            (bytesStoreSetChunkByteLongStoredWord σ I)) I) ⟨1⟩ = ⟨0⟩)
    (hbadPost : UInt256.sub (UInt256.land
        (bytesStoreSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
            (bytesStoreSetChunkByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStoreSetChunkByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
              (bytesStoreSetChunkByteLongStoredWord σ I)) I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩)
    (hperm : I.perm = true) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
    (bytesStoreSetChunkByteLongStoredWord σ I)
  have hdec := bytesStoreX_setChunkByteLongWriteReturnReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag hchunkBoundPost hperm
  exact bytesStoreX_bytesLengthDecoderShortMalformedMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := bytesStoreSetChunkByteHeaderWord σ' I) (ret := ⟨905⟩)
    (rest := [bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I,
      ⟨0⟩, bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
      bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem (bytesStoreSetChunkByteSlot I)
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
    (by simpa [σ'] using hdec)
    (by simpa [σ'] using hflagPost)
    (by simpa [σ'] using hbadPost)
    (by simp)

theorem bytesStoreX_setChunkByteLongWriteReturnDecodedLength
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1270⟩
      [len, bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I,
        UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hchunkBoundPost :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
            (bytesStoreSetChunkByteLongStoredWord σ I)) I).toNat)
    (hflagPost : UInt256.land
        (bytesStoreSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
            (bytesStoreSetChunkByteLongStoredWord σ I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
            (bytesStoreSetChunkByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreSetChunkByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
              (bytesStoreSetChunkByteLongStoredWord σ I)) I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨905⟩
      [UInt256.div
          (bytesStoreSetChunkByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
              (bytesStoreSetChunkByteLongStoredWord σ I)) I) ⟨2⟩,
        bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I, ⟨0⟩,
        bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256)
        (wordAt0Mem (bytesStoreSetChunkByteSlot I)
          (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))) (UInt256.ofNat 3)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
        (bytesStoreSetChunkByteLongStoredWord σ I)) k C := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
    (bytesStoreSetChunkByteLongStoredWord σ I)
  have hdec := bytesStoreX_setChunkByteLongWriteReturnReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag hchunkBoundPost hperm
  have hdecoded := bytesStoreX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := bytesStoreSetChunkByteHeaderWord σ' I) (ret := ⟨905⟩)
    (rest := [bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I,
      ⟨0⟩, bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
      bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem (bytesStoreSetChunkByteSlot I)
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [σ'] using hdec)
    (by simpa [σ'] using hflagPost)
    (by simpa [σ'] using hvalidPost)
    (by native_decide)
    (by simp)
  simpa [σ'] using hdecoded

theorem bytesStoreX_setChunkByteLongWriteReturnDecodedShortLength
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1270⟩
      [len, bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I,
        UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hchunkBoundPost :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
            (bytesStoreSetChunkByteLongStoredWord σ I)) I).toNat)
    (hflagPost : UInt256.land
        (bytesStoreSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
            (bytesStoreSetChunkByteLongStoredWord σ I)) I) ⟨1⟩ = ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
            (bytesStoreSetChunkByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStoreSetChunkByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
              (bytesStoreSetChunkByteLongStoredWord σ I)) I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨905⟩
      [UInt256.land (UInt256.div
          (bytesStoreSetChunkByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
              (bytesStoreSetChunkByteLongStoredWord σ I)) I) ⟨2⟩) ⟨127⟩,
        bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I, ⟨0⟩,
        bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256)
        (wordAt0Mem (bytesStoreSetChunkByteSlot I)
          (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))) (UInt256.ofNat 3)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
        (bytesStoreSetChunkByteLongStoredWord σ I)) k C := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteLongDataSlot I)
    (bytesStoreSetChunkByteLongStoredWord σ I)
  have hdec := bytesStoreX_setChunkByteLongWriteReturnReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag hchunkBoundPost hperm
  have hdecoded := bytesStoreX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := bytesStoreSetChunkByteHeaderWord σ' I) (ret := ⟨905⟩)
    (rest := [bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I,
      ⟨0⟩, bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
      bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem (bytesStoreSetChunkByteSlot I)
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [σ'] using hdec)
    (by simpa [σ'] using hflagPost)
    (by simpa [σ'] using hvalidPost)
    (by native_decide)
    (by simp)
  simpa [σ'] using hdecoded

theorem bytesStoreX_setChunkByteShortWriteReturnDecodedLength
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1270⟩
      [len, bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I,
        UInt256.shiftLeft (bytesStoreSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreSetChunkByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hchunkBoundPost :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteSlot I)
            (bytesStoreSetChunkByteShortStoredWord σ I)) I).toNat)
    (hflagPost : UInt256.land
        (bytesStoreSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteSlot I)
            (bytesStoreSetChunkByteShortStoredWord σ I)) I) ⟨1⟩ = ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteSlot I)
            (bytesStoreSetChunkByteShortStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStoreSetChunkByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteSlot I)
              (bytesStoreSetChunkByteShortStoredWord σ I)) I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨905⟩
      [UInt256.land (UInt256.div
          (bytesStoreSetChunkByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteSlot I)
              (bytesStoreSetChunkByteShortStoredWord σ I)) I) ⟨2⟩) ⟨127⟩,
        bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I, ⟨0⟩,
        bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256)
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)) (UInt256.ofNat 3)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteSlot I)
        (bytesStoreSetChunkByteShortStoredWord σ I)) k C := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreSetChunkByteSlot I)
    (bytesStoreSetChunkByteShortStoredWord σ I)
  have hdec := bytesStoreX_setChunkByteShortWriteReturnReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag hchunkBoundPost hperm
  have hdecoded := bytesStoreX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := bytesStoreSetChunkByteHeaderWord σ' I) (ret := ⟨905⟩)
    (rest := [bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I,
      ⟨0⟩, bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
      bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [σ'] using hdec)
    (by simpa [σ'] using hflagPost)
    (by simpa [σ'] using hvalidPost)
    (by native_decide)
    (by simp)
  simpa [σ'] using hdecoded

theorem bytesStoreX_setChunkByteShortReadReturnToWrapper
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len header : UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨905⟩
      [len, bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I, ⟨0⟩,
        bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat)
    (hheader :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreSetChunkByteSlot I) ⟨0⟩)) = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreSetChunkByteIndexWord I) header)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreSetChunkByteValueWord I) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨301⟩
      [bytesStoreSetChunkByteValueWord I, bytesStoreSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
  obtain ⟨_, _, rd905⟩ := hreach
  have hlt : UInt256.lt (bytesStoreSetChunkByteIndexWord I) len = ⟨1⟩ :=
    ult_one hbound
  have rd919 := evm_run rd905 with [
    jumpdest, dup2, lt, push2 ⟨919⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd921 := evm_run rd919 with [jumpdest, dup2]
  obtain ⟨_, _, rd922₀⟩ := rd921.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd922⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨922⟩
        [header, bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I,
          ⟨0⟩, bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
          bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
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
        [header, bytesStoreSetChunkByteIndexWord I, ⟨0⟩,
          bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
          bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
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

theorem bytesStoreX_setChunkByteLongReadReturnToWrapper
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len header dataWord : UInt256}
    {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨905⟩
      [len, bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I, ⟨0⟩,
        bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat)
    (hheader :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreSetChunkByteSlot I) ⟨0⟩)) = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hdata :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreSetChunkByteLongDataSlot I) ⟨0⟩)) =
          dataWord)
    (hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreSetChunkByteLongWordIndex I) dataWord)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreSetChunkByteValueWord I) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨301⟩
      [bytesStoreSetChunkByteValueWord I, bytesStoreSelWord I]
      (wordAt0Mem (bytesStoreSetChunkByteSlot I) mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
  obtain ⟨_, _, rd905⟩ := hreach
  have hlt : UInt256.lt (bytesStoreSetChunkByteIndexWord I) len = ⟨1⟩ :=
    ult_one hbound
  have hflagOne : UInt256.land header ⟨1⟩ = ⟨1⟩ :=
    u256_land_one_eq_one_of_ne_zero hflag
  have hslot := bytesStoreSetChunkByteLongBaseHashMem I mem
  have rd919 := evm_run rd905 with [
    jumpdest, dup2, lt, push2 ⟨919⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd921 := evm_run rd919 with [jumpdest, dup2]
  obtain ⟨_, _, rd922₀⟩ := rd921.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd922⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨922⟩
        [header, bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I,
          ⟨0⟩, bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
          bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
        mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [initState, hheader] using rd922₀⟩
  have rd947 := evm_run rd922 with [
    push1 ⟨1⟩, and, iszero, push2 ⟨948⟩,
    jumpiNT (by
      rw [u256_land_comm, hflagOne]
      decide),
    swap1, push0,
    raw mstore 0 (wordAt0Mem (bytesStoreSetChunkByteSlot I) mem)
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256 0 (bytesLikeDataBase (bytesStoreSetChunkByteSlot I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost hslot (by native_decide) (by evm_ov),
    swap1, push1 ⟨32⟩, swap2, dup3, dup3, div, add, swap2, swap1]
  have rd948raw := RD.mod rd947 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd948⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨948⟩
        [bytesStoreSetChunkByteLongWordIndex I,
          bytesStoreSetChunkByteLongDataSlot I, ⟨0⟩,
          bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
          bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
        (wordAt0Mem (bytesStoreSetChunkByteSlot I) mem)
        (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreSetChunkByteLongWordIndex,
        bytesStoreSetChunkByteLongDataSlot,
        u256_add_comm (UInt256.div (bytesStoreSetChunkByteIndexWord I) ⟨32⟩)
          (bytesLikeDataBase (bytesStoreSetChunkByteSlot I))] using rd948raw⟩
  have rd950 := evm_run rd948 with [jumpdest, swap1]
  obtain ⟨_, _, rd951₀⟩ := rd950.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd951⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨951⟩
        [dataWord, bytesStoreSetChunkByteLongWordIndex I, ⟨0⟩,
          bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
          bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
        (wordAt0Mem (bytesStoreSetChunkByteSlot I) mem)
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

theorem bytesStoreX_setChunkByteShortReadReturn
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len header : UInt256} {mem : ByteArray}
    (hsize : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨905⟩
      [len, bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I, ⟨0⟩,
        bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat)
    (hheader :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreSetChunkByteSlot I) ⟨0⟩)) = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreSetChunkByteIndexWord I) header)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreSetChunkByteValueWord I)
    (hcanon : UInt256.land (bytesStoreSetChunkByteValueWord I) ⟨255⟩ =
      bytesStoreSetChunkByteValueWord I) :
    RDret bytesStoreBytecode g (initState cA gh bl σinit σ₀ g A I) (cA, τ)
      (UInt256.toByteArray (bytesStoreSetChunkByteValueWord I)) := by
  have h301 := bytesStoreX_setChunkByteShortReadReturnToWrapper
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (τ := τ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := len) (header := header) (mem := mem)
    hreach hbound hheader hflag hbyte
  have hret := bytesStoreX_returnUInt8_301OfMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ := τ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := bytesStoreSetChunkByteValueWord I)
    (mem := mem) hsize hread64 h301
  simpa [hcanon] using hret

theorem bytesStoreX_setChunkByteLongReadReturn
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len header dataWord : UInt256}
    {mem : ByteArray}
    (hsize : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨905⟩
      [len, bytesStoreSetChunkByteIndexWord I, bytesStoreSetChunkByteSlot I, ⟨0⟩,
        bytesStoreSetChunkByteValueWord I, bytesStoreSetChunkByteIndexWord I,
        bytesStoreSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C)
    (hbound : (bytesStoreSetChunkByteIndexWord I).toNat < len.toNat)
    (hheader :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreSetChunkByteSlot I) ⟨0⟩)) = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hdata :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreSetChunkByteLongDataSlot I) ⟨0⟩)) =
          dataWord)
    (hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreSetChunkByteLongWordIndex I) dataWord)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreSetChunkByteValueWord I)
    (hcanon : UInt256.land (bytesStoreSetChunkByteValueWord I) ⟨255⟩ =
      bytesStoreSetChunkByteValueWord I) :
    RDret bytesStoreBytecode g (initState cA gh bl σinit σ₀ g A I) (cA, τ)
      (UInt256.toByteArray (bytesStoreSetChunkByteValueWord I)) := by
  have h301 := bytesStoreX_setChunkByteLongReadReturnToWrapper
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (τ := τ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := len) (header := header)
    (dataWord := dataWord) (mem := mem) hreach hbound hheader hflag hdata hbyte
  have hret := bytesStoreX_returnUInt8_301OfMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ := τ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := bytesStoreSetChunkByteValueWord I)
    (mem := wordAt0Mem (bytesStoreSetChunkByteSlot I) mem)
    (wordAt0Mem_size_96 _ hsize)
    (bytesStoreWordAt0Mem_read64 _ hsize hread64)
    h301
  simpa [hcanon] using hret

theorem bytesStoreSetChunkByteDecodeShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hshort : I.calldata.size < 100) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetChunkByteSelector_size hsel
  have hreach := bytesStoreReachSetChunkByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨414⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetChunkByteEntryPc] using hreach
  have hd := bytesStoreDispatch_setChunkByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setChunkByte_none_short (I := I) hshort
  exact (bytesStoreX_setChunkByteDecodeShort
      (g := Sat256.ofUInt256 g) hreachPc hsz hshort hsize)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreSetChunkByteDecodeHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetChunkByteSelector_size hsel
  have hreach := bytesStoreReachSetChunkByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨414⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetChunkByteEntryPc] using hreach
  have hd := bytesStoreDispatch_setChunkByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setChunkByte_none_huge (I := I) hbig
  exact (bytesStoreX_setChunkByteDecodeHuge
      (g := Sat256.ofUInt256 g) hreachPc hbig hsize)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreSetChunkByteDecodeNoncanonValueRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (bytesStoreSetChunkByteValueWord I).toNat < EVM.twoPow 8) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetChunkByteSelector_size hsel
  have hreach := bytesStoreReachSetChunkByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨414⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetChunkByteEntryPc] using hreach
  have hd := bytesStoreDispatch_setChunkByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setChunkByte_none_noncanon_value
    (I := I) hsz100 hhi hnc
  exact (bytesStoreX_setChunkByteDecodeNoncanonValue
      (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
      (bytesStoreSetPacketByteLand255_ne_self_of_not_uint8 hnc))
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreSetChunkByteOobChunksLengthRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hbound :
      ¬ (bytesStoreSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ_evm I).toNat) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetChunkByteSelector_size hsel
  have hreach := bytesStoreReachSetChunkByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨414⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetChunkByteEntryPc] using hreach
  have hreachBody := bytesStoreX_setChunkByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreDispatch_setChunkByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setChunkByte_locals (I := I) hsz100 hhi hcanon
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨1⟩ = bytesStoreChunksLengthWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
    exact bytesStoreSetChunkByteBodyBoundsRevertsOfChunksLength
      (by simp only [initState]; exact hwv) hload hbound
  exact (bytesStoreX_setChunkByteOobChunksLength
      (g := Sat256.ofUInt256 g) hreachBody hbound)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreSetChunkByteOobLongRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hchunkBound :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreSetChunkByteHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetChunkByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetChunkByteHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hbound :
      ¬ (bytesStoreSetChunkByteIndexWord I).toNat <
        (UInt256.div (bytesStoreSetChunkByteHeaderWord σ_evm I) ⟨2⟩).toNat) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetChunkByteSelector_size hsel
  have hreach := bytesStoreReachSetChunkByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨414⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetChunkByteEntryPc] using hreach
  have hreachBody := bytesStoreX_setChunkByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreDispatch_setChunkByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setChunkByte_locals (I := I) hsz100 hhi hcanon
  have hloadChunks :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨1⟩ = bytesStoreChunksLengthWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadHeader :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (bytesStoreSetChunkByteSlot I) =
          bytesStoreSetChunkByteHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadSetChunkByteHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadHeader' :
      Solm.EVM.storageLoad
        { (default : EVM.State) with
          accountMap := σ_solm
          σ₀ := σ₀
          executionEnv := I
          substate := A
          createdAccounts := cA
          machineState.gasAvailable := .ofUInt256 g
          blocks := bl
          genesisBlockHeader := gh }
        I.codeOwner (bytesStoreSetChunkByteSlot I) =
          bytesStoreSetChunkByteHeaderWord σ_evm I := by
    simpa [initState] using hloadHeader
  have hlen :
      readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreSetChunkByteHeaderRef I) =
          .ok (UInt256.div (bytesStoreSetChunkByteHeaderWord σ_evm I) ⟨2⟩).toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetChunkByteHeaderRef I)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (baseSlot := bytesStoreSetChunkByteSlot I)
      (header := bytesStoreSetChunkByteHeaderWord σ_evm I)
      (len := (UInt256.div (bytesStoreSetChunkByteHeaderWord σ_evm I) ⟨2⟩).toNat)
      (bytesStoreSetChunkByteHeaderRef_length_slot
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      (by simpa [initState] using hloadHeader)
      (solidityDecodeBytesLengthHeader_long_valid hflag rfl hvalid)
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
    exact bytesStoreSetChunkByteBodyBoundsRevertsOfLength
      (by simp only [initState]; exact hwv) hloadChunks hchunkBound hlen hbound
  exact (bytesStoreX_setChunkByteOobLong
      (g := Sat256.ofUInt256 g) hreachBody hchunkBound hflag hvalid hbound)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreSetChunkByteOobShortRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hchunkBound :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreSetChunkByteHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreSetChunkByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetChunkByteHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hbound :
      ¬ (bytesStoreSetChunkByteIndexWord I).toNat <
        (UInt256.land (UInt256.div (bytesStoreSetChunkByteHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetChunkByteSelector_size hsel
  have hreach := bytesStoreReachSetChunkByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨414⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetChunkByteEntryPc] using hreach
  have hreachBody := bytesStoreX_setChunkByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreDispatch_setChunkByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setChunkByte_locals (I := I) hsz100 hhi hcanon
  have hloadChunks :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨1⟩ = bytesStoreChunksLengthWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadHeader :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (bytesStoreSetChunkByteSlot I) =
          bytesStoreSetChunkByteHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadSetChunkByteHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadHeader' :
      Solm.EVM.storageLoad
        { (default : EVM.State) with
          accountMap := σ_solm
          σ₀ := σ₀
          executionEnv := I
          substate := A
          createdAccounts := cA
          machineState.gasAvailable := .ofUInt256 g
          blocks := bl
          genesisBlockHeader := gh }
        I.codeOwner (bytesStoreSetChunkByteSlot I) =
          bytesStoreSetChunkByteHeaderWord σ_evm I := by
    simpa [initState] using hloadHeader
  have hvalid0 :
      UInt256.sub ⟨0⟩
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetChunkByteHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  have hlen :
      readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreSetChunkByteHeaderRef I) =
          .ok (UInt256.land
            (UInt256.div (bytesStoreSetChunkByteHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat := by
    exact bytesStoreReadLengthOfHeaderLoad
      (er := bytesStoreSetChunkByteHeaderRef I)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (baseSlot := bytesStoreSetChunkByteSlot I)
      (header := bytesStoreSetChunkByteHeaderWord σ_evm I)
      (len := (UInt256.land
        (UInt256.div (bytesStoreSetChunkByteHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat)
      (bytesStoreSetChunkByteHeaderRef_length_slot
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      (by simpa [initState] using hloadHeader)
      (solidityDecodeBytesLengthHeader_short_valid hflag rfl hvalid)
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
    exact bytesStoreSetChunkByteBodyBoundsRevertsOfLength
      (by simp only [initState]; exact hwv) hloadChunks hchunkBound hlen hbound
  exact (bytesStoreX_setChunkByteOobShort
      (g := Sat256.ofUInt256 g) hreachBody hchunkBound hflag hvalid hbound)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreSetChunkByteLongMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hchunkBound :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreSetChunkByteHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreSetChunkByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetChunkByteHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetChunkByteSelector_size hsel
  have hreach := bytesStoreReachSetChunkByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨414⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetChunkByteEntryPc] using hreach
  have hreachBody := bytesStoreX_setChunkByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreDispatch_setChunkByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setChunkByte_locals (I := I) hsz100 hhi hcanon
  have hloadChunks :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨1⟩ = bytesStoreChunksLengthWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadHeader :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (bytesStoreSetChunkByteSlot I) =
          bytesStoreSetChunkByteHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadSetChunkByteHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadHeader' :
      Solm.EVM.storageLoad
        { (default : EVM.State) with
          accountMap := σ_solm
          σ₀ := σ₀
          executionEnv := I
          substate := A
          createdAccounts := cA
          machineState.gasAvailable := .ofUInt256 g
          blocks := bl
          genesisBlockHeader := gh }
        I.codeOwner (bytesStoreSetChunkByteSlot I) =
          bytesStoreSetChunkByteHeaderWord σ_evm I := by
    simpa [initState] using hloadHeader
  have hlen :
      readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreSetChunkByteHeaderRef I) = .revert := by
    exact bytesStoreReadLengthRevertOfHeaderLoad
      (er := bytesStoreSetChunkByteHeaderRef I)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (baseSlot := bytesStoreSetChunkByteSlot I)
      (header := bytesStoreSetChunkByteHeaderWord σ_evm I)
      (bytesStoreSetChunkByteHeaderRef_length_slot
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      (by simpa [initState] using hloadHeader)
      (by simp [solidityDecodeBytesLengthHeader, hflag, hbad])
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
    exact bytesStoreSetChunkByteBodyRevertsOfLengthRead
      (by simp only [initState]; exact hwv) hloadChunks hchunkBound hlen
  exact (bytesStoreX_setChunkByteLongMalformed
      (g := Sat256.ofUInt256 g) hreachBody hchunkBound hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreSetChunkByteShortMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hchunkBound :
      (bytesStoreSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreSetChunkByteHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreSetChunkByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetChunkByteHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetChunkByteSelector_size hsel
  have hreach := bytesStoreReachSetChunkByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨414⟩
      [bytesStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreSetChunkByteEntryPc] using hreach
  have hreachBody := bytesStoreX_setChunkByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreDispatch_setChunkByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setChunkByte_locals (I := I) hsz100 hhi hcanon
  have hloadChunks :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨1⟩ = bytesStoreChunksLengthWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadHeader :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (bytesStoreSetChunkByteSlot I) =
          bytesStoreSetChunkByteHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadSetChunkByteHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadHeader' :
      Solm.EVM.storageLoad
        { (default : EVM.State) with
          accountMap := σ_solm
          σ₀ := σ₀
          executionEnv := I
          substate := A
          createdAccounts := cA
          machineState.gasAvailable := .ofUInt256 g
          blocks := bl
          genesisBlockHeader := gh }
        I.codeOwner (bytesStoreSetChunkByteSlot I) =
          bytesStoreSetChunkByteHeaderWord σ_evm I := by
    simpa [initState] using hloadHeader
  have hbad0 :
      UInt256.sub ⟨0⟩
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetChunkByteHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) = ⟨0⟩ := by
    simpa [hflag] using hbad
  have hlen :
      readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreSetChunkByteHeaderRef I) = .revert := by
    exact bytesStoreReadLengthRevertOfHeaderLoad
      (er := bytesStoreSetChunkByteHeaderRef I)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (baseSlot := bytesStoreSetChunkByteSlot I)
      (header := bytesStoreSetChunkByteHeaderWord σ_evm I)
      (bytesStoreSetChunkByteHeaderRef_length_slot
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      (by simpa [initState] using hloadHeader)
      (by simp [solidityDecodeBytesLengthHeader, hflag, hbad0])
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
    exact bytesStoreSetChunkByteBodyRevertsOfLengthRead
      (by simp only [initState]; exact hwv) hloadChunks hchunkBound hlen
  exact (bytesStoreX_setChunkByteShortMalformed
      (g := Sat256.ofUInt256 g) hreachBody hchunkBound hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

end BytesStore
