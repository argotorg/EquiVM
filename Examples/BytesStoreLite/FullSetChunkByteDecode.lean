import Examples.BytesStoreLite.FullSetChunkByte

/-!
# BytesStoreLite — `setChunkByte(uint256,uint256,uint8)` bytecode decoder

This module keeps the optimized-bytecode ABI decoder proof separate from the larger Solm/storage
body proof in `FullSetChunkByte.lean`, so decoder iteration does not force that file to grow further.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace BytesStoreLite

theorem bytesStoreLiteSetChunkByteChunksBaseHash :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem).readWithPadding 0 32))) =
      chunksDataBase := by
  rw [wordAt0Mem_read0]
  simpa [chunksDataBase, bytesLikeDataBase] using
    keccakSlot_eq (UInt256.toByteArray (⟨1⟩ : UInt256))

theorem bytesStoreLiteSetChunkByteChunksBaseHashMem (mem : ByteArray) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((wordAt0Mem (⟨1⟩ : UInt256) mem).readWithPadding 0 32))) =
      chunksDataBase := by
  rw [wordAt0Mem_read0]
  simpa [chunksDataBase, bytesLikeDataBase] using
    keccakSlot_eq (UInt256.toByteArray (⟨1⟩ : UInt256))

theorem bytesStoreLiteSetChunkByteLongBaseHashMem (I : ExecutionEnv) (mem : ByteArray) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((wordAt0Mem (bytesStoreLiteSetChunkByteSlot I) mem).readWithPadding 0 32))) =
      bytesLikeDataBase (bytesStoreLiteSetChunkByteSlot I) := by
  rw [wordAt0Mem_read0]
  simpa [bytesLikeDataBase] using
    keccakSlot_eq (UInt256.toByteArray (bytesStoreLiteSetChunkByteSlot I))

private theorem bytesStoreLiteSetChunkByteDecodeLenCheckOk {sz : ℕ}
    (hlen : 100 ≤ sz) (hhi : sz < 2 ^ 255 + 4) (hsz : sz < UInt256.size) :
    UInt256.slt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) ⟨96⟩ = ⟨0⟩ := by
  exact solcCalldataStaticLenCheckOk (words := 3) (by simpa using hlen) hhi hsz

private theorem bytesStoreLiteSetChunkByteDecodeLenCheckShort {sz : ℕ}
    (hhead : 4 ≤ sz) (hshort : sz < 100) (hsz : sz < UInt256.size) :
    UInt256.slt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
  exact solcCalldataStaticLenCheckShort (words := 3) hhead (by simpa using hshort) hsz
    (by norm_num)

private theorem bytesStoreLiteSetChunkByteDecodeLenCheckHuge {sz : ℕ}
    (hbig : 2 ^ 255 + 4 ≤ sz) (hsz : sz < UInt256.size) :
    UInt256.slt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
  exact solcCalldataStaticLenCheckHuge (words := 3) hbig hsz (by norm_num)

theorem bytesStoreLiteSetChunkByteSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem bytesStoreLiteX_setChunkByteDecodeValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨414⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hcanon : UInt256.land (bytesStoreLiteSetChunkByteValueWord I) ⟨255⟩ =
      bytesStoreLiteSetChunkByteValueWord I) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1226⟩
      [bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd414⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ :=
    bytesStoreLiteSetChunkByteDecodeLenCheckOk hsz100 hhi hsize
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
      bytesStoreLiteSetChunkByteChunkIndexWord I from rfl,
    show (⟨4⟩ + ⟨32⟩ : UInt256) = ⟨36⟩ from by native_decide,
    show (⟨4⟩ + ⟨64⟩ : UInt256) = ⟨68⟩ from by native_decide] at rd1946
  have rd1950 := evm_run rd1946 with [
    jumpdest, dup1, calldataload]
  rw [show (⟨68⟩ : UInt256).toNat = 68 from by decide,
    show uInt256OfByteArray (I.calldata.readBytes 68 32) =
      bytesStoreLiteSetChunkByteValueWord I from rfl] at rd1950
  have rd2050 := evm_run rd1950 with [
    push1 ⟨255⟩, dup2, and, dup2, eq,
    push2 ⟨1962⟩,
    jumpiT (by rw [bytesStoreLiteSetPacketByteUint8CanonEqGuard hcanon]; decide)
      (by native_decide),
    jumpdest, swap2, swap1, pop, jump (by native_decide)]
  exact ⟨_, _, evm_run rd2050 with [
    jumpdest, swap1, pop, swap3, pop, swap3, pop, swap3, jump (by native_decide),
    jumpdest, push2 ⟨1226⟩, jump (by native_decide)]⟩

theorem bytesStoreLiteX_setChunkByteDecodeShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨414⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100)
    (hsize : I.calldata.size < UInt256.size) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd414⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ :=
    bytesStoreLiteSetChunkByteDecodeLenCheckShort hsz4 hshort hsize
  have rd2009 := evm_run rd414 with [
    jumpdest, push2 ⟨301⟩, push2 ⟨428⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨2009⟩, jump (by native_decide)]
  exact evm_run rd2009 with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2027⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_setChunkByteDecodeHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨414⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd414⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ :=
    bytesStoreLiteSetChunkByteDecodeLenCheckHuge hbig hsize
  have rd2009 := evm_run rd414 with [
    jumpdest, push2 ⟨301⟩, push2 ⟨428⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨2009⟩, jump (by native_decide)]
  exact evm_run rd2009 with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2027⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_setChunkByteDecodeNoncanonValue {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨414⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hnc : UInt256.land (bytesStoreLiteSetChunkByteValueWord I) ⟨255⟩ ≠
      bytesStoreLiteSetChunkByteValueWord I) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd414⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ :=
    bytesStoreLiteSetChunkByteDecodeLenCheckOk hsz100 hhi hsize
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
      bytesStoreLiteSetChunkByteChunkIndexWord I from rfl,
    show (⟨4⟩ + ⟨32⟩ : UInt256) = ⟨36⟩ from by native_decide,
    show (⟨4⟩ + ⟨64⟩ : UInt256) = ⟨68⟩ from by native_decide] at rd1946
  have rd1950 := evm_run rd1946 with [
    jumpdest, dup1, calldataload]
  rw [show (⟨68⟩ : UInt256).toNat = 68 from by decide,
    show uInt256OfByteArray (I.calldata.readBytes 68 32) =
      bytesStoreLiteSetChunkByteValueWord I from rfl] at rd1950
  exact evm_run rd1950 with [
    push1 ⟨255⟩, dup2, and, dup2, eq,
    push2 ⟨1962⟩,
    jumpiNT (by rw [bytesStoreLiteSetPacketByteUint8NoncanonEqGuard hnc]),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_setChunkByteReachLengthDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1226⟩
      [bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ I).toNat) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [bytesStoreLiteSetChunkByteHeaderWord σ I, ⟨1270⟩,
        bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1226⟩ := hreach
  have hlt :
      UInt256.lt (bytesStoreLiteSetChunkByteChunkIndexWord I)
        (bytesStoreLiteChunksLengthWord σ I) = ⟨1⟩ :=
    ult_one hbound
  have hslot := bytesStoreLiteSetChunkByteChunksBaseHash
  have rd1236 := evm_run rd1226 with [
    jumpdest, push0, dup2, push1 ⟨248⟩, shl, push1 ⟨1⟩, dup6, dup2]
  obtain ⟨_, _, rd1237₀⟩ := rd1236.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1237⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1237⟩
        [bytesStoreLiteChunksLengthWord σ I, bytesStoreLiteSetChunkByteChunkIndexWord I,
          ⟨1⟩, UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteChunksLengthWord, initState] using rd1237₀⟩
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
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1262⟩
        [bytesStoreLiteSetChunkByteHeaderWord σ I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteSlot I,
          UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteSetChunkByteHeaderWord, bytesStoreLiteSetChunkByteSlot,
        u256_add_comm chunksDataBase (bytesStoreLiteSetChunkByteChunkIndexWord I),
        initState] using rd1262₀⟩
  exact ⟨_, _, evm_run rd1262 with [
    push2 ⟨1270⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreLiteX_setChunkByteOobChunksLength {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1226⟩
      [bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound :
      ¬ (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ I).toNat) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1226⟩ := hreach
  have hlt :
      UInt256.lt (bytesStoreLiteSetChunkByteChunkIndexWord I)
        (bytesStoreLiteChunksLengthWord σ I) = ⟨0⟩ :=
    ult_zero (by omega)
  have rd1236 := evm_run rd1226 with [
    jumpdest, push0, dup2, push1 ⟨248⟩, shl, push1 ⟨1⟩, dup6, dup2]
  obtain ⟨_, _, rd1237₀⟩ := rd1236.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1237⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1237⟩
        [bytesStoreLiteChunksLengthWord σ I, bytesStoreLiteSetChunkByteChunkIndexWord I,
          ⟨1⟩, UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteChunksLengthWord, initState] using rd1237₀⟩
  have rd2579 := evm_run rd1237 with [
    dup2, lt, push2 ⟨1250⟩, jumpiNT (by simpa using hlt),
    push2 ⟨1250⟩, push2 ⟨2579⟩, jump (by native_decide)]
  exact bytesStoreLiteX_panic32Mem ⟨_, _, rd2579⟩
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setChunkByteOobAfterLength {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1270⟩
      [len, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hbound : ¬ (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1270⟩ := hreach
  have hlt : UInt256.lt (bytesStoreLiteSetChunkByteIndexWord I) len = ⟨0⟩ :=
    ult_zero (by omega)
  have rd2579 := evm_run rd1270 with [
    jumpdest, dup2, lt, push2 ⟨1284⟩,
    jumpiNT (by simpa using hlt),
    push2 ⟨1284⟩, push2 ⟨2579⟩, jump (by native_decide)]
  exact bytesStoreLiteX_panic32Mem ⟨_, _, rd2579⟩
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setChunkByteOobLong {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1226⟩
      [bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hbound :
      ¬ (bytesStoreLiteSetChunkByteIndexWord I).toNat <
        (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩).toNat) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdec := bytesStoreLiteX_setChunkByteReachLengthDecoder hreach hchunkBound
  have hlen := bytesStoreLiteX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := g) hdec hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreLiteX_setChunkByteOobAfterLength (g := g) hlen hbound

theorem bytesStoreLiteX_setChunkByteOobShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1226⟩
      [bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hbound :
      ¬ (bytesStoreLiteSetChunkByteIndexWord I).toNat <
        (UInt256.land (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨127⟩).toNat) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdec := bytesStoreLiteX_setChunkByteReachLengthDecoder hreach hchunkBound
  have hlen := bytesStoreLiteX_bytesLengthDecoderShortValidMem
    (A := A) (I := I) (g := g) hdec hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreLiteX_setChunkByteOobAfterLength (g := g) hlen hbound

theorem bytesStoreLiteX_setChunkByteLongMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1226⟩
      [bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdec := bytesStoreLiteX_setChunkByteReachLengthDecoder (g := g) hreach hchunkBound
  exact bytesStoreLiteX_bytesLengthDecoderLongMalformedMem
    hdec hflag hbad (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setChunkByteShortMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1226⟩
      [bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdec := bytesStoreLiteX_setChunkByteReachLengthDecoder (g := g) hreach hchunkBound
  exact bytesStoreLiteX_bytesLengthDecoderShortMalformedMem
    hdec hflag hbad (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setChunkByteShortReachStoreCommon {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1270⟩
      [len, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1313⟩
      [bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1270⟩ := hreach
  have hlt : UInt256.lt (bytesStoreLiteSetChunkByteIndexWord I) len = ⟨1⟩ :=
    ult_one hbound
  have rd1284 := evm_run rd1270 with [
    jumpdest, dup2, lt, push2 ⟨1284⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd1286 := evm_run rd1284 with [jumpdest, dup2]
  obtain ⟨_, _, rd1287₀⟩ := rd1286.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1287⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1287⟩
        [bytesStoreLiteSetChunkByteHeaderWord σ I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteSlot I,
          UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteSetChunkByteHeaderWord, initState] using rd1287₀⟩
  have rd1313 := evm_run rd1287 with [
    push1 ⟨1⟩, and, iszero, push2 ⟨1313⟩,
    jumpiT (by
      rw [u256_land_comm, hflag]
      decide)
      (by native_decide)]
  exact ⟨_, _, rd1313⟩

theorem bytesStoreLiteX_setChunkByteLongReachStoreCommon {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1270⟩
      [len, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1313⟩
      [bytesStoreLiteSetChunkByteLongWordIndex I, bytesStoreLiteSetChunkByteLongDataSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (bytesStoreLiteSetChunkByteSlot I)
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1270⟩ := hreach
  have hlt : UInt256.lt (bytesStoreLiteSetChunkByteIndexWord I) len = ⟨1⟩ :=
    ult_one hbound
  have hflagOne :
      UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ = ⟨1⟩ :=
    u256_land_one_eq_one_of_ne_zero hflag
  have hslot := bytesStoreLiteSetChunkByteLongBaseHashMem I
    (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
  have rd1284 := evm_run rd1270 with [
    jumpdest, dup2, lt, push2 ⟨1284⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd1286 := evm_run rd1284 with [jumpdest, dup2]
  obtain ⟨_, _, rd1287₀⟩ := rd1286.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1287⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1287⟩
        [bytesStoreLiteSetChunkByteHeaderWord σ I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteSlot I,
          UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteSetChunkByteHeaderWord, initState] using rd1287₀⟩
  have rd1312 := evm_run rd1287 with [
    push1 ⟨1⟩, and, iszero, push2 ⟨1313⟩,
    jumpiNT (by
      rw [u256_land_comm, hflagOne]
      decide),
    swap1, push0,
    raw mstore 0 (wordAt0Mem (bytesStoreLiteSetChunkByteSlot I)
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256 0 (bytesLikeDataBase (bytesStoreLiteSetChunkByteSlot I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost hslot (by native_decide) (by evm_ov),
    swap1, push1 ⟨32⟩, swap2, dup3, dup3, div, add, swap2, swap1]
  have rd1313raw := RD.mod rd1312 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa [bytesStoreLiteSetChunkByteLongWordIndex,
      bytesStoreLiteSetChunkByteLongDataSlot,
      u256_add_comm (UInt256.div (bytesStoreLiteSetChunkByteIndexWord I) ⟨32⟩)
        (bytesLikeDataBase (bytesStoreLiteSetChunkByteSlot I))] using rd1313raw⟩

theorem bytesStoreLiteX_setChunkByteShortStore {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1313⟩
      [bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1342⟩
      [⟨0⟩, bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteSlot I)
        (bytesStoreLiteSetChunkByteShortStoredWord σ I)) k C := by
  obtain ⟨_, _, rd1313⟩ := hreach
  have rd1322 := evm_run rd1313 with [
    jumpdest, push1 ⟨31⟩, sub, push2 ⟨256⟩, exp, dup2]
  obtain ⟨_, _, rd1323₀⟩ := rd1322.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1323⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
        [bytesStoreLiteSetChunkByteHeaderWord σ I,
          UInt256.exp ⟨256⟩ (UInt256.sub ⟨31⟩
            (bytesStoreLiteSetChunkByteIndexWord I)),
          bytesStoreLiteSetChunkByteSlot I,
          UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteSetChunkByteHeaderWord, initState] using rd1323₀⟩
  have rd1340 := evm_run rd1323 with [
    dup2, push1 ⟨255⟩, mul, not, and, swap1,
    push1 ⟨1⟩, push1 ⟨248⟩, shl, dup5, div, mul, lor, swap1]
  obtain ⟨_, _, rd1340'⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1340⟩
        [bytesStoreLiteSetChunkByteSlot I,
          bytesStoreLiteSetChunkByteShortStoredWord σ I,
          UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteSetChunkByteShortStoredWord,
        bytesStoreLiteSetChunkByteShortScale] using rd1340⟩
  obtain ⟨_, _, rd1341₀⟩ := rd1340'.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1341⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1341⟩
        [UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteSlot I)
          (bytesStoreLiteSetChunkByteShortStoredWord σ I)) k C := by
    exact ⟨_, _, by simpa [sstoreAccountMap, initState] using rd1341₀⟩
  exact ⟨_, _, evm_run rd1341 with [pop]⟩

theorem bytesStoreLiteX_setChunkByteLongStore {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1313⟩
      [bytesStoreLiteSetChunkByteLongWordIndex I, bytesStoreLiteSetChunkByteLongDataSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (bytesStoreLiteSetChunkByteSlot I)
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1342⟩
      [⟨0⟩, bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (bytesStoreLiteSetChunkByteSlot I)
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)) (UInt256.ofNat 3)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
        (bytesStoreLiteSetChunkByteLongStoredWord σ I)) k C := by
  obtain ⟨_, _, rd1313⟩ := hreach
  have rd1322 := evm_run rd1313 with [
    jumpdest, push1 ⟨31⟩, sub, push2 ⟨256⟩, exp, dup2]
  obtain ⟨_, _, rd1323₀⟩ := rd1322.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1323⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
        [bytesStoreLiteSetChunkByteLongOldWord σ I,
          UInt256.exp ⟨256⟩ (UInt256.sub ⟨31⟩
            (bytesStoreLiteSetChunkByteLongWordIndex I)),
          bytesStoreLiteSetChunkByteLongDataSlot I,
          UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (bytesStoreLiteSetChunkByteSlot I)
          (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteSetChunkByteLongOldWord, initState] using rd1323₀⟩
  have rd1340 := evm_run rd1323 with [
    dup2, push1 ⟨255⟩, mul, not, and, swap1,
    push1 ⟨1⟩, push1 ⟨248⟩, shl, dup5, div, mul, lor, swap1]
  obtain ⟨_, _, rd1340'⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1340⟩
        [bytesStoreLiteSetChunkByteLongDataSlot I,
          bytesStoreLiteSetChunkByteLongStoredWord σ I,
          UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (bytesStoreLiteSetChunkByteSlot I)
          (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteSetChunkByteLongStoredWord,
        bytesStoreLiteSetChunkByteLongScale] using rd1340⟩
  obtain ⟨_, _, rd1341₀⟩ := rd1340'.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1341⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1341⟩
        [UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (bytesStoreLiteSetChunkByteSlot I)
          (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)) (UInt256.ofNat 3)
        ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ I)) k C := by
    exact ⟨_, _, by simpa [sstoreAccountMap, initState] using rd1341₀⟩
  exact ⟨_, _, evm_run rd1341 with [pop]⟩

theorem bytesStoreLiteX_setChunkByteReturnReachLengthDecoderMem
    {cA gh bl σinit σ σ₀ A I} {g : Sat256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1342⟩
      [⟨0⟩, bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ I).toNat) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      [bytesStoreLiteSetChunkByteHeaderWord σ I, ⟨905⟩,
        bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I, ⟨0⟩,
        bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) mem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1342⟩ := hreach
  have hlt :
      UInt256.lt (bytesStoreLiteSetChunkByteChunkIndexWord I)
        (bytesStoreLiteChunksLengthWord σ I) = ⟨1⟩ :=
    ult_one hbound
  have hslot := bytesStoreLiteSetChunkByteChunksBaseHashMem mem
  have rd1346 := evm_run rd1342 with [
    push1 ⟨1⟩, dup5, dup2]
  obtain ⟨_, _, rd1347₀⟩ := rd1346.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1347⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1347⟩
        [bytesStoreLiteChunksLengthWord σ I, bytesStoreLiteSetChunkByteChunkIndexWord I,
          ⟨1⟩, ⟨0⟩, bytesStoreLiteSetChunkByteValueWord I,
          bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteChunkIndexWord I,
          ⟨301⟩, bytesStoreLiteSelWord I]
        mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteChunksLengthWord, initState] using rd1347₀⟩
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
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1372⟩
        [bytesStoreLiteSetChunkByteHeaderWord σ I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteSlot I, ⟨0⟩,
          bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) mem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteSetChunkByteHeaderWord, bytesStoreLiteSetChunkByteSlot,
        u256_add_comm chunksDataBase (bytesStoreLiteSetChunkByteChunkIndexWord I),
        initState] using rd1372₀⟩
  exact ⟨_, _, evm_run rd1372 with [
    push2 ⟨905⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreLiteX_setChunkByteLongWriteReturnReachLengthDecoder
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1270⟩
      [len, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hchunkBoundPost :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I).toNat)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I,
        ⟨905⟩, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
        ⟨0⟩, bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256)
        (wordAt0Mem (bytesStoreLiteSetChunkByteSlot I)
          (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))) (UInt256.ofNat 3)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
        (bytesStoreLiteSetChunkByteLongStoredWord σ I)) k C := by
  have h1313 := bytesStoreLiteX_setChunkByteLongReachStoreCommon
    (g := g) hreach hbound hflag
  have h1342 := bytesStoreLiteX_setChunkByteLongStore
    (g := g) h1313 hperm
  exact bytesStoreLiteX_setChunkByteReturnReachLengthDecoderMem
    (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
      (bytesStoreLiteSetChunkByteLongStoredWord σ I))
    h1342 hchunkBoundPost

theorem bytesStoreLiteX_setChunkByteShortWriteReturnReachLengthDecoder
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1270⟩
      [len, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hchunkBoundPost :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteSlot I)
            (bytesStoreLiteSetChunkByteShortStoredWord σ I)) I).toNat)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteSlot I)
            (bytesStoreLiteSetChunkByteShortStoredWord σ I)) I,
        ⟨905⟩, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
        ⟨0⟩, bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256)
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)) (UInt256.ofNat 3)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteSlot I)
        (bytesStoreLiteSetChunkByteShortStoredWord σ I)) k C := by
  have h1313 := bytesStoreLiteX_setChunkByteShortReachStoreCommon
    (g := g) hreach hbound hflag
  have h1342 := bytesStoreLiteX_setChunkByteShortStore
    (g := g) h1313 hperm
  exact bytesStoreLiteX_setChunkByteReturnReachLengthDecoderMem
    (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteSlot I)
      (bytesStoreLiteSetChunkByteShortStoredWord σ I))
    h1342 hchunkBoundPost

theorem bytesStoreLiteX_setChunkByteLongWriteReturnDecodedLength
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1270⟩
      [len, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hchunkBoundPost :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I).toNat)
    (hflagPost : UInt256.land
        (bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreLiteSetChunkByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
              (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨905⟩
      [UInt256.div
          (bytesStoreLiteSetChunkByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
              (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I) ⟨2⟩,
        bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I, ⟨0⟩,
        bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256)
        (wordAt0Mem (bytesStoreLiteSetChunkByteSlot I)
          (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))) (UInt256.ofNat 3)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
        (bytesStoreLiteSetChunkByteLongStoredWord σ I)) k C := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
    (bytesStoreLiteSetChunkByteLongStoredWord σ I)
  have hdec := bytesStoreLiteX_setChunkByteLongWriteReturnReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag hchunkBoundPost hperm
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := bytesStoreLiteSetChunkByteHeaderWord σ' I) (ret := ⟨905⟩)
    (rest := [bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
      ⟨0⟩, bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
      bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem (bytesStoreLiteSetChunkByteSlot I)
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [σ'] using hdec)
    (by simpa [σ'] using hflagPost)
    (by simpa [σ'] using hvalidPost)
    (by native_decide)
    (by simp)
  simpa [σ'] using hdecoded

theorem bytesStoreLiteX_setChunkByteShortWriteReturnDecodedLength
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1270⟩
      [len, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hchunkBoundPost :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteSlot I)
            (bytesStoreLiteSetChunkByteShortStoredWord σ I)) I).toNat)
    (hflagPost : UInt256.land
        (bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteSlot I)
            (bytesStoreLiteSetChunkByteShortStoredWord σ I)) I) ⟨1⟩ = ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteSlot I)
            (bytesStoreLiteSetChunkByteShortStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStoreLiteSetChunkByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteSlot I)
              (bytesStoreLiteSetChunkByteShortStoredWord σ I)) I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨905⟩
      [UInt256.land (UInt256.div
          (bytesStoreLiteSetChunkByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteSlot I)
              (bytesStoreLiteSetChunkByteShortStoredWord σ I)) I) ⟨2⟩) ⟨127⟩,
        bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I, ⟨0⟩,
        bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256)
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)) (UInt256.ofNat 3)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteSlot I)
        (bytesStoreLiteSetChunkByteShortStoredWord σ I)) k C := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteSlot I)
    (bytesStoreLiteSetChunkByteShortStoredWord σ I)
  have hdec := bytesStoreLiteX_setChunkByteShortWriteReturnReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag hchunkBoundPost hperm
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := bytesStoreLiteSetChunkByteHeaderWord σ' I) (ret := ⟨905⟩)
    (rest := [bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
      ⟨0⟩, bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
      bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [σ'] using hdec)
    (by simpa [σ'] using hflagPost)
    (by simpa [σ'] using hvalidPost)
    (by native_decide)
    (by simp)
  simpa [σ'] using hdecoded

theorem bytesStoreLiteX_setChunkByteShortReadReturnToWrapper
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len header : UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨905⟩
      [len, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I, ⟨0⟩,
        bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hheader :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetChunkByteSlot I) ⟨0⟩)) = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreLiteSetChunkByteIndexWord I) header)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreLiteSetChunkByteValueWord I) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨301⟩
      [bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
  obtain ⟨_, _, rd905⟩ := hreach
  have hlt : UInt256.lt (bytesStoreLiteSetChunkByteIndexWord I) len = ⟨1⟩ :=
    ult_one hbound
  have rd919 := evm_run rd905 with [
    jumpdest, dup2, lt, push2 ⟨919⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd921 := evm_run rd919 with [jumpdest, dup2]
  obtain ⟨_, _, rd922₀⟩ := rd921.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd922⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨922⟩
        [header, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
          ⟨0⟩, bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
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
        [header, bytesStoreLiteSetChunkByteIndexWord I, ⟨0⟩,
          bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
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

theorem bytesStoreLiteX_setChunkByteLongReadReturnToWrapper
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len header dataWord : UInt256}
    {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨905⟩
      [len, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I, ⟨0⟩,
        bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hheader :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetChunkByteSlot I) ⟨0⟩)) = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hdata :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetChunkByteLongDataSlot I) ⟨0⟩)) =
          dataWord)
    (hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreLiteSetChunkByteLongWordIndex I) dataWord)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreLiteSetChunkByteValueWord I) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨301⟩
      [bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSelWord I]
      (wordAt0Mem (bytesStoreLiteSetChunkByteSlot I) mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
  obtain ⟨_, _, rd905⟩ := hreach
  have hlt : UInt256.lt (bytesStoreLiteSetChunkByteIndexWord I) len = ⟨1⟩ :=
    ult_one hbound
  have hflagOne : UInt256.land header ⟨1⟩ = ⟨1⟩ :=
    u256_land_one_eq_one_of_ne_zero hflag
  have hslot := bytesStoreLiteSetChunkByteLongBaseHashMem I mem
  have rd919 := evm_run rd905 with [
    jumpdest, dup2, lt, push2 ⟨919⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd921 := evm_run rd919 with [jumpdest, dup2]
  obtain ⟨_, _, rd922₀⟩ := rd921.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd922⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨922⟩
        [header, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
          ⟨0⟩, bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [initState, hheader] using rd922₀⟩
  have rd947 := evm_run rd922 with [
    push1 ⟨1⟩, and, iszero, push2 ⟨948⟩,
    jumpiNT (by
      rw [u256_land_comm, hflagOne]
      decide),
    swap1, push0,
    raw mstore 0 (wordAt0Mem (bytesStoreLiteSetChunkByteSlot I) mem)
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256 0 (bytesLikeDataBase (bytesStoreLiteSetChunkByteSlot I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost hslot (by native_decide) (by evm_ov),
    swap1, push1 ⟨32⟩, swap2, dup3, dup3, div, add, swap2, swap1]
  have rd948raw := RD.mod rd947 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd948⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨948⟩
        [bytesStoreLiteSetChunkByteLongWordIndex I,
          bytesStoreLiteSetChunkByteLongDataSlot I, ⟨0⟩,
          bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (bytesStoreLiteSetChunkByteSlot I) mem)
        (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteSetChunkByteLongWordIndex,
        bytesStoreLiteSetChunkByteLongDataSlot,
        u256_add_comm (UInt256.div (bytesStoreLiteSetChunkByteIndexWord I) ⟨32⟩)
          (bytesLikeDataBase (bytesStoreLiteSetChunkByteSlot I))] using rd948raw⟩
  have rd950 := evm_run rd948 with [jumpdest, swap1]
  obtain ⟨_, _, rd951₀⟩ := rd950.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd951⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨951⟩
        [dataWord, bytesStoreLiteSetChunkByteLongWordIndex I, ⟨0⟩,
          bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (bytesStoreLiteSetChunkByteSlot I) mem)
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

theorem bytesStoreLiteX_setChunkByteShortReadReturn
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len header : UInt256} {mem : ByteArray}
    (hsize : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨905⟩
      [len, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I, ⟨0⟩,
        bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hheader :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetChunkByteSlot I) ⟨0⟩)) = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreLiteSetChunkByteIndexWord I) header)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreLiteSetChunkByteValueWord I)
    (hcanon : UInt256.land (bytesStoreLiteSetChunkByteValueWord I) ⟨255⟩ =
      bytesStoreLiteSetChunkByteValueWord I) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σinit σ₀ g A I) (cA, τ)
      (UInt256.toByteArray (bytesStoreLiteSetChunkByteValueWord I)) := by
  have h301 := bytesStoreLiteX_setChunkByteShortReadReturnToWrapper
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (τ := τ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := len) (header := header) (mem := mem)
    hreach hbound hheader hflag hbyte
  have hret := bytesStoreLiteX_returnUInt8_301OfMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ := τ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := bytesStoreLiteSetChunkByteValueWord I)
    (mem := mem) hsize hread64 h301
  simpa [hcanon] using hret

theorem bytesStoreLiteX_setChunkByteLongReadReturn
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len header dataWord : UInt256}
    {mem : ByteArray}
    (hsize : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨905⟩
      [len, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I, ⟨0⟩,
        bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hheader :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetChunkByteSlot I) ⟨0⟩)) = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hdata :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetChunkByteLongDataSlot I) ⟨0⟩)) =
          dataWord)
    (hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreLiteSetChunkByteLongWordIndex I) dataWord)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreLiteSetChunkByteValueWord I)
    (hcanon : UInt256.land (bytesStoreLiteSetChunkByteValueWord I) ⟨255⟩ =
      bytesStoreLiteSetChunkByteValueWord I) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σinit σ₀ g A I) (cA, τ)
      (UInt256.toByteArray (bytesStoreLiteSetChunkByteValueWord I)) := by
  have h301 := bytesStoreLiteX_setChunkByteLongReadReturnToWrapper
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (τ := τ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := len) (header := header)
    (dataWord := dataWord) (mem := mem) hreach hbound hheader hflag hdata hbyte
  have hret := bytesStoreLiteX_returnUInt8_301OfMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ := τ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := bytesStoreLiteSetChunkByteValueWord I)
    (mem := wordAt0Mem (bytesStoreLiteSetChunkByteSlot I) mem)
    (wordAt0Mem_size_96 _ hsize)
    (bytesStoreLiteWordAt0Mem_read64 _ hsize hread64)
    h301
  simpa [hcanon] using hret

/-
theorem bytesStoreLiteX_setChunkByteShortSuccessReturn
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256} {acc : Account}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1226⟩
      [bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hlen : len =
      UInt256.land (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hacc : σ.find? I.codeOwner = some acc) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteSlot I)
        (bytesStoreLiteSetChunkByteShortStoredWord σ I))
      (UInt256.toByteArray (bytesStoreLiteSetChunkByteValueWord I)) := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteSlot I)
    (bytesStoreLiteSetChunkByteShortStoredWord σ I)
  let header' : UInt256 :=
    Option.option ⟨0⟩
      (fun ac => Batteries.RBMap.findD ac.storage (bytesStoreLiteSetChunkByteSlot I) ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  have hdec := bytesStoreLiteX_setChunkByteReachLengthDecoder (g := g) hreach hchunkBound
  have h1270Raw := bytesStoreLiteX_bytesLengthDecoderShortValidMem
    (A := A) (I := I) (g := g) hdec hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h1270 :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1270⟩
        [len, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
          UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    simpa [hlen] using h1270Raw
  have hchunkBoundPost :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ' I).toNat := by
    simpa [hsigmaPost] using
      bytesStoreLiteChunkBoundAfterChunkHeaderSstore
        (σ := σ) (I := I) (chunkIndex := bytesStoreLiteSetChunkByteChunkIndexWord I)
        (val := bytesStoreLiteSetChunkByteShortStoredWord σ I) hchunkBound
  have hheader : header' = bytesStoreLiteSetChunkByteShortStoredWord σ I := by
    rw [hsigmaPost]
    simpa [header'] using
      sstoreAccountMap_storage_findD_self_of_find_some_any σ I.codeOwner acc
        (bytesStoreLiteSetChunkByteSlot I)
        (bytesStoreLiteSetChunkByteShortStoredWord σ I) hacc
  have hheaderPost :
      bytesStoreLiteSetChunkByteHeaderWord σ' I =
        bytesStoreLiteSetChunkByteShortStoredWord σ I := by
    simpa [header', bytesStoreLiteSetChunkByteHeaderWord] using hheader
  have hflagPost :
      UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ' I) ⟨1⟩ = ⟨0⟩ := by
    rw [hheaderPost, bytesStoreLiteSetChunkByteShortStoredWord_flag_eq
      (σ := σ) (I := I) (len := len) hshort hbound, hflag]
  have hltLen : UInt256.lt len ⟨32⟩ = ⟨1⟩ := by
    exact ult_one (by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
  have hvalidLen : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hltLen]
    native_decide
  have hlenPost :
      UInt256.land (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ' I) ⟨2⟩) ⟨127⟩ =
        len := by
    rw [hheaderPost, bytesStoreLiteSetChunkByteShortStoredWord_shortLen_eq
      (σ := σ) (I := I) (len := len) hshort hbound]
    exact hlen.symm
  have hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreLiteSetChunkByteHeaderWord σ' I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStoreLiteSetChunkByteHeaderWord σ' I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflagPost, hlenPost] using hvalidLen
  let headerPost := bytesStoreLiteSetChunkByteHeaderWord σ' I
  have hheaderLoad :
      ((σ'.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetChunkByteSlot I) ⟨0⟩)) =
          headerPost := by
    rfl
  have hflagHeader : UInt256.land headerPost ⟨1⟩ = ⟨0⟩ := by
    change UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ' I) ⟨1⟩ = ⟨0⟩
    exact hflagPost
  have hread := bytesStoreLiteX_setChunkByteShortWriteReturnDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) h1270
    hbound hflag
    (by
      rw [← hsigmaPost]
      exact hchunkBoundPost)
    (by
      rw [← hsigmaPost]
      exact hflagPost)
    (by
      rw [← hsigmaPost]
      exact hvalidPost)
    hperm
  have hbyteAt :
      UInt256.byteAt (bytesStoreLiteSetChunkByteIndexWord I) headerPost =
        bytesStoreLiteSetChunkByteValueWord I := by
    change UInt256.byteAt (bytesStoreLiteSetChunkByteIndexWord I)
        (bytesStoreLiteSetChunkByteHeaderWord σ' I) =
      bytesStoreLiteSetChunkByteValueWord I
    rw [hheaderPost]
    exact bytesStoreLiteSetChunkByteShortStoredWord_byteAt
      (σ := σ) (I := I) (len := len) hcanon hshort hbound
  have hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreLiteSetChunkByteIndexWord I) headerPost)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreLiteSetChunkByteValueWord I := by
    rw [hbyteAt]
    exact bytesStoreLiteSetByteValueHighMulShiftRight hcanon
  have h301 :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨301⟩
        [bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256)
          (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
        (UInt256.ofNat 3) ByteArray.empty (cA, σ') k C := by
    exact bytesStoreLiteX_setChunkByteShortReadReturnToWrapper
      (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (len := len)
      (header := headerPost)
      (mem := wordAt0Mem (⟨1⟩ : UInt256)
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      hread hbound hheaderLoad hflagHeader hbyte
  have hret := bytesStoreLiteX_returnUInt8_301OfMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := bytesStoreLiteSetChunkByteValueWord I)
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (wordAt0Mem_size_96 _ (wordAt0Mem_size_96 _ solcFreePtrMem_size))
    (bytesStoreLiteWordAt0Mem_read64 _
      (wordAt0Mem_size_96 _ solcFreePtrMem_size)
      (bytesStoreLiteWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64))
    h301
  rw [← hsigmaPost]
  simpa [bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon] using hret

theorem bytesStoreLiteX_setChunkByteLongSuccessReturn
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256} {acc : Account}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1226⟩
      [bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hlen : len = UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hacc : σ.find? I.codeOwner = some acc) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
        (bytesStoreLiteSetChunkByteLongStoredWord σ I))
      (UInt256.toByteArray (bytesStoreLiteSetChunkByteValueWord I)) := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
    (bytesStoreLiteSetChunkByteLongStoredWord σ I)
  let header' : UInt256 :=
    Option.option ⟨0⟩
      (fun ac => Batteries.RBMap.findD ac.storage (bytesStoreLiteSetChunkByteSlot I) ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  let dataWord' : UInt256 :=
    Option.option ⟨0⟩
      (fun ac => Batteries.RBMap.findD ac.storage (bytesStoreLiteSetChunkByteLongDataSlot I) ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  have hdec := bytesStoreLiteX_setChunkByteReachLengthDecoder (g := g) hreach hchunkBound
  have h1270Raw := bytesStoreLiteX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := g) hdec hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h1270 :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1270⟩
        [len, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
          UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    simpa [hlen] using h1270Raw
  have hchunkBoundPost :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ' I).toNat := by
    simpa [σ', bytesStoreLiteSetChunkByteLongDataSlot] using
      bytesStoreLiteChunkBoundAfterChunkDataSstore
        (σ := σ) (I := I) (chunkIndex := bytesStoreLiteSetChunkByteChunkIndexWord I)
        (idx := bytesStoreLiteSetChunkByteIndexWord I)
        (val := bytesStoreLiteSetChunkByteLongStoredWord σ I) hchunkBound
  have hheader : header' = bytesStoreLiteSetChunkByteHeaderWord σ I := by
    simpa [header', σ', bytesStoreLiteSetChunkByteHeaderWord,
      bytesStoreLiteSetChunkByteLongDataSlot] using
        bytesStoreLiteBytesHeaderWordAfterDataSstore_eq_of_before
          (σ := σ) (I := I) (baseSlot := bytesStoreLiteSetChunkByteSlot I)
          (idx := bytesStoreLiteSetChunkByteIndexWord I)
          (val := bytesStoreLiteSetChunkByteLongStoredWord σ I) (by rfl)
  have hheaderPost :
      bytesStoreLiteSetChunkByteHeaderWord σ' I =
        bytesStoreLiteSetChunkByteHeaderWord σ I := by
    simpa [header', bytesStoreLiteSetChunkByteHeaderWord] using hheader
  have hflagPost :
      UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ' I) ⟨1⟩ ≠ ⟨0⟩ := by
    simpa [hheaderPost] using hflag
  have hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreLiteSetChunkByteHeaderWord σ' I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreLiteSetChunkByteHeaderWord σ' I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hheaderPost] using hvalid
  have hread := bytesStoreLiteX_setChunkByteLongWriteReturnDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) h1270
    hbound hflag
    (by
      change (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ' I).toNat
      exact hchunkBoundPost)
    (by
      change UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ' I) ⟨1⟩ ≠ ⟨0⟩
      exact hflagPost)
    (by
      change UInt256.sub (UInt256.land
          (bytesStoreLiteSetChunkByteHeaderWord σ' I) ⟨1⟩)
          (UInt256.lt (UInt256.div
            (bytesStoreLiteSetChunkByteHeaderWord σ' I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩
      exact hvalidPost)
    hperm
  have hdata : dataWord' = bytesStoreLiteSetChunkByteLongStoredWord σ I := by
    simpa [dataWord', σ'] using
      sstoreAccountMap_storage_findD_self_of_find_some_any σ I.codeOwner acc
        (bytesStoreLiteSetChunkByteLongDataSlot I)
        (bytesStoreLiteSetChunkByteLongStoredWord σ I) hacc
  have hbyteAt :
      UInt256.byteAt (bytesStoreLiteSetChunkByteLongWordIndex I) dataWord' =
        bytesStoreLiteSetChunkByteValueWord I := by
    rw [hdata]
    exact bytesStoreLiteSetChunkByteLongStoredWord_byteAt
      (σ := σ) (I := I) hcanon
  have hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreLiteSetChunkByteLongWordIndex I) dataWord')
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreLiteSetChunkByteValueWord I := by
    rw [hbyteAt]
    exact bytesStoreLiteSetByteValueHighMulShiftRight hcanon
  have h301 := bytesStoreLiteX_setChunkByteLongReadReturnToWrapper
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := len) (header := header')
    (dataWord := dataWord')
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem (bytesStoreLiteSetChunkByteSlot I)
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
    hread hbound (by rfl) (by simpa [hheader] using hflag) (by rfl) hbyte
  have hret := bytesStoreLiteX_returnUInt8_301OfMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := bytesStoreLiteSetChunkByteValueWord I)
    (mem := wordAt0Mem (bytesStoreLiteSetChunkByteSlot I)
      (wordAt0Mem (⟨1⟩ : UInt256)
        (wordAt0Mem (bytesStoreLiteSetChunkByteSlot I)
          (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))))
    (wordAt0Mem_size_96 _
      (wordAt0Mem_size_96 _
        (wordAt0Mem_size_96 _
          (wordAt0Mem_size_96 _ solcFreePtrMem_size))))
    (bytesStoreLiteWordAt0Mem_read64 _
      (wordAt0Mem_size_96 _
        (wordAt0Mem_size_96 _
          (wordAt0Mem_size_96 _ solcFreePtrMem_size)))
      (bytesStoreLiteWordAt0Mem_read64 _
        (wordAt0Mem_size_96 _
          (wordAt0Mem_size_96 _ solcFreePtrMem_size))
        (bytesStoreLiteWordAt0Mem_read64 _
          (wordAt0Mem_size_96 _ solcFreePtrMem_size)
          (bytesStoreLiteWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64))))
    h301
  change RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
    (UInt256.toByteArray (bytesStoreLiteSetChunkByteValueWord I))
  simpa [bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon] using hret
-/

theorem bytesStoreLiteSetChunkByteDecodeShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hshort : I.calldata.size < 100) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetChunkByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetChunkByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨414⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetChunkByteEntryPc] using hreach
  have hd := bytesStoreLiteDispatch_setChunkByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunkByte_none_short (I := I) hshort
  exact (bytesStoreLiteX_setChunkByteDecodeShort
      (g := Sat256.ofUInt256 g) hreachPc hsz hshort hsize)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetChunkByteDecodeHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetChunkByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetChunkByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨414⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetChunkByteEntryPc] using hreach
  have hd := bytesStoreLiteDispatch_setChunkByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunkByte_none_huge (I := I) hbig
  exact (bytesStoreLiteX_setChunkByteDecodeHuge
      (g := Sat256.ofUInt256 g) hreachPc hbig hsize)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetChunkByteDecodeNoncanonValueRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetChunkByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetChunkByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨414⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetChunkByteEntryPc] using hreach
  have hd := bytesStoreLiteDispatch_setChunkByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunkByte_none_noncanon_value
    (I := I) hsz100 hhi hnc
  exact (bytesStoreLiteX_setChunkByteDecodeNoncanonValue
      (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
      (bytesStoreLiteSetPacketByteLand255_ne_self_of_not_uint8 hnc))
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetChunkByteOobChunksLengthRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hbound :
      ¬ (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetChunkByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetChunkByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨414⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetChunkByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setChunkByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreLiteDispatch_setChunkByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunkByte_locals (I := I) hsz100 hhi hcanon
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨1⟩ = bytesStoreLiteChunksLengthWord σ_evm I := by
    simpa [initState] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
    exact bytesStoreLiteSetChunkByteBodyBoundsRevertsOfChunksLength
      (by simp only [initState]; exact hwv) hload hbound
  exact (bytesStoreLiteX_setChunkByteOobChunksLength
      (g := Sat256.ofUInt256 g) hreachBody hbound)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetChunkByteOobLongRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hbound :
      ¬ (bytesStoreLiteSetChunkByteIndexWord I).toNat <
        (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩).toNat) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetChunkByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetChunkByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨414⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetChunkByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setChunkByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreLiteDispatch_setChunkByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunkByte_locals (I := I) hsz100 hhi hcanon
  have hloadChunks :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨1⟩ = bytesStoreLiteChunksLengthWord σ_evm I := by
    simpa [initState] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadHeader :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (bytesStoreLiteSetChunkByteSlot I) =
          bytesStoreLiteSetChunkByteHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreLiteStorageLoadSetChunkByteHeader_initState_of_accountMapEquiv
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
        I.codeOwner (bytesStoreLiteSetChunkByteSlot I) =
          bytesStoreLiteSetChunkByteHeaderWord σ_evm I := by
    simpa [initState] using hloadHeader
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteSetChunkByteHeaderRef I) =
          .ok (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩).toNat := by
    have hchunkNN :
        ¬ (((bytesStoreLiteSetChunkByteChunkIndexWord I).toNat : Int) < 0) := by omega
    have hloadHeaderSlot :
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
          I.codeOwner
            (chunksDataBase + bytesStoreLiteSetChunkByteChunkIndexWord I) =
          bytesStoreLiteSetChunkByteHeaderWord σ_evm I := by
      simpa [bytesStoreLiteSetChunkByteSlot] using hloadHeader'
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, initState,
      bytesStoreLiteSetChunkByteHeaderRef, chunksElemSlot?, nonnegativeIndexSlot?,
      hchunkNN, hloadHeaderSlot, hflag, hvalid, u256_ofNat_toNat]
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
    exact bytesStoreLiteSetChunkByteBodyBoundsRevertsOfLength
      (by simp only [initState]; exact hwv) hloadChunks hchunkBound hlen hbound
  exact (bytesStoreLiteX_setChunkByteOobLong
      (g := Sat256.ofUInt256 g) hreachBody hchunkBound hflag hvalid hbound)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetChunkByteOobShortRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hbound :
      ¬ (bytesStoreLiteSetChunkByteIndexWord I).toNat <
        (UInt256.land (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetChunkByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetChunkByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨414⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetChunkByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setChunkByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreLiteDispatch_setChunkByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunkByte_locals (I := I) hsz100 hhi hcanon
  have hloadChunks :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨1⟩ = bytesStoreLiteChunksLengthWord σ_evm I := by
    simpa [initState] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadHeader :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (bytesStoreLiteSetChunkByteSlot I) =
          bytesStoreLiteSetChunkByteHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreLiteStorageLoadSetChunkByteHeader_initState_of_accountMapEquiv
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
        I.codeOwner (bytesStoreLiteSetChunkByteSlot I) =
          bytesStoreLiteSetChunkByteHeaderWord σ_evm I := by
    simpa [initState] using hloadHeader
  have hvalid0 :
      UInt256.sub ⟨0⟩
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteSetChunkByteHeaderRef I) =
          .ok (UInt256.land
            (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat := by
    have hchunkNN :
        ¬ (((bytesStoreLiteSetChunkByteChunkIndexWord I).toNat : Int) < 0) := by omega
    have hloadHeaderSlot :
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
          I.codeOwner
            (chunksDataBase + bytesStoreLiteSetChunkByteChunkIndexWord I) =
          bytesStoreLiteSetChunkByteHeaderWord σ_evm I := by
      simpa [bytesStoreLiteSetChunkByteSlot] using hloadHeader'
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, initState,
      bytesStoreLiteSetChunkByteHeaderRef, chunksElemSlot?, nonnegativeIndexSlot?,
      hchunkNN, hloadHeaderSlot, hflag, hvalid0, u256_ofNat_toNat]
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
    exact bytesStoreLiteSetChunkByteBodyBoundsRevertsOfLength
      (by simp only [initState]; exact hwv) hloadChunks hchunkBound hlen hbound
  exact (bytesStoreLiteX_setChunkByteOobShort
      (g := Sat256.ofUInt256 g) hreachBody hchunkBound hflag hvalid hbound)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetChunkByteLongMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetChunkByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetChunkByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨414⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetChunkByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setChunkByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreLiteDispatch_setChunkByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunkByte_locals (I := I) hsz100 hhi hcanon
  have hloadChunks :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨1⟩ = bytesStoreLiteChunksLengthWord σ_evm I := by
    simpa [initState] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadHeader :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (bytesStoreLiteSetChunkByteSlot I) =
          bytesStoreLiteSetChunkByteHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreLiteStorageLoadSetChunkByteHeader_initState_of_accountMapEquiv
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
        I.codeOwner (bytesStoreLiteSetChunkByteSlot I) =
          bytesStoreLiteSetChunkByteHeaderWord σ_evm I := by
    simpa [initState] using hloadHeader
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteSetChunkByteHeaderRef I) = .revert := by
    have hchunkNN :
        ¬ (((bytesStoreLiteSetChunkByteChunkIndexWord I).toNat : Int) < 0) := by omega
    have hloadHeaderSlot :
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
          I.codeOwner
            (chunksDataBase + bytesStoreLiteSetChunkByteChunkIndexWord I) =
          bytesStoreLiteSetChunkByteHeaderWord σ_evm I := by
      simpa [bytesStoreLiteSetChunkByteSlot] using hloadHeader'
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, initState,
      bytesStoreLiteSetChunkByteHeaderRef, chunksElemSlot?, nonnegativeIndexSlot?,
      hchunkNN, hloadHeaderSlot, hflag, hbad, u256_ofNat_toNat]
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
    exact bytesStoreLiteSetChunkByteBodyRevertsOfLengthRead
      (by simp only [initState]; exact hwv) hloadChunks hchunkBound hlen
  exact (bytesStoreLiteX_setChunkByteLongMalformed
      (g := Sat256.ofUInt256 g) hreachBody hchunkBound hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetChunkByteShortMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetChunkByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetChunkByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨414⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetChunkByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setChunkByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreLiteDispatch_setChunkByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunkByte_locals (I := I) hsz100 hhi hcanon
  have hloadChunks :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨1⟩ = bytesStoreLiteChunksLengthWord σ_evm I := by
    simpa [initState] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadHeader :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (bytesStoreLiteSetChunkByteSlot I) =
          bytesStoreLiteSetChunkByteHeaderWord σ_evm I := by
    simpa [initState] using
      bytesStoreLiteStorageLoadSetChunkByteHeader_initState_of_accountMapEquiv
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
        I.codeOwner (bytesStoreLiteSetChunkByteSlot I) =
          bytesStoreLiteSetChunkByteHeaderWord σ_evm I := by
    simpa [initState] using hloadHeader
  have hbad0 :
      UInt256.sub ⟨0⟩
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) = ⟨0⟩ := by
    simpa [hflag] using hbad
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteSetChunkByteHeaderRef I) = .revert := by
    have hchunkNN :
        ¬ (((bytesStoreLiteSetChunkByteChunkIndexWord I).toNat : Int) < 0) := by omega
    have hloadHeaderSlot :
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
          I.codeOwner
            (chunksDataBase + bytesStoreLiteSetChunkByteChunkIndexWord I) =
          bytesStoreLiteSetChunkByteHeaderWord σ_evm I := by
      simpa [bytesStoreLiteSetChunkByteSlot] using hloadHeader'
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, initState,
      bytesStoreLiteSetChunkByteHeaderRef, chunksElemSlot?, nonnegativeIndexSlot?,
      hchunkNN, hloadHeaderSlot, hflag, hbad0, u256_ofNat_toNat]
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
    exact bytesStoreLiteSetChunkByteBodyRevertsOfLengthRead
      (by simp only [initState]; exact hwv) hloadChunks hchunkBound hlen
  exact (bytesStoreLiteX_setChunkByteShortMalformed
      (g := Sat256.ofUInt256 g) hreachBody hchunkBound hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

end BytesStoreLite
