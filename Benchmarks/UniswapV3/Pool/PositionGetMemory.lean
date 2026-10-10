import Benchmarks.UniswapV3.Pool.PositionGetSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def positionDataMem (mem : ByteArray) (p : UInt256) (owner : AccountAddress)
    (lower upper : UInt256) : ByteArray :=
  writeWord (writeWord (writeWord mem (p.toNat + 32)
    (UInt256.shiftLeft (EVM.word owner.val) ⟨96⟩)) (p.toNat + 52)
    (UInt256.shiftLeft (positionTickWord lower) ⟨232⟩)) (p.toNat + 55)
    (UInt256.shiftLeft (positionTickWord upper) ⟨232⟩)

def positionBuildMem (mem : ByteArray) (p : UInt256) (owner : AccountAddress)
    (lower upper : UInt256) : ByteArray :=
  writeWord (writeWord (positionDataMem mem p owner lower upper) p.toNat ⟨26⟩)
    64 (p + ⟨58⟩)

theorem positionDataMem_size (mem : ByteArray) (p : UInt256) (owner : AccountAddress)
    (lower upper : UInt256) :
    (positionDataMem mem p owner lower upper).size = max mem.size (p.toNat + 87) := by
  simp only [positionDataMem, writeWord_sparse_size]
  omega

theorem positionBuildMem_size (mem : ByteArray) (p : UInt256) (owner : AccountAddress)
    (lower upper : UInt256) (hp : 128 ≤ p.toNat) :
    (positionBuildMem mem p owner lower upper).size = max mem.size (p.toNat + 87) := by
  simp only [positionBuildMem, writeWord_sparse_size, positionDataMem_size]
  omega

theorem positionDataMem_load64 {mem : ByteArray} {aw p : UInt256} (hm : HeapMemory mem aw p)
    (owner : AccountAddress) (lower upper : UInt256) :
    memLoad (UInt256.ofNat 64) (positionDataMem mem p owner lower upper) = p := by
  have hp := hm.lower
  apply mloadWordValue_of_readWithPadding
  · change 64 < _
    rw [positionDataMem_size]; omega
  · change (positionDataMem mem p owner lower upper).readWithPadding 64 32 = _
    unfold positionDataMem
    rw [writeWord_sparse_read_preserved _ _ 64 _ (Or.inl ⟨by omega, by
        simp only [writeWord_sparse_size]; have hs := hm.size; omega⟩),
      writeWord_sparse_read_preserved _ _ 64 _ (Or.inl ⟨by omega, by
        simp only [writeWord_sparse_size]; have hs := hm.size; omega⟩),
      writeWord_sparse_read_preserved _ _ 64 _ (Or.inl ⟨by omega, hm.size⟩)]
    exact hm.free

theorem positionDataMem_bytes (mem : ByteArray) (p : UInt256) (owner : AccountAddress)
    (lower upper : UInt256) :
    (positionDataMem mem p owner lower upper).readWithPadding (p.toNat + 32) 26 =
      positionPackedBytes owner lower upper := by
  have hs := positionDataMem_size mem p owner lower upper
  rw [show 26 = 20 + 6 from rfl,
    byteArray_readWithPadding_split_unbounded _ _ 20 6 (by decide) (by decide) (by omega),
    byteArray_readWithPadding_split_unbounded _ _ 3 3 (by decide) (by decide) (by omega)]
  have h0 : (positionDataMem mem p owner lower upper).readWithPadding (p.toNat + 32) 20 =
      (EVM.word owner.val).toByteArray.extract 12 32 := by
    unfold positionDataMem
    rw [writeWord_read_preserved_len_of_disjoint
      (by simp only [writeWord_sparse_size]; have h := lt_usize 0 (by decide); omega)
      (Or.inl ⟨by omega, by simp only [writeWord_sparse_size]; omega⟩) (by decide) (by decide),
      writeWord_read_preserved_len_of_disjoint
      (by simp only [writeWord_sparse_size]; have h := lt_usize 0 (by decide); omega)
      (Or.inl ⟨by omega, by simp only [writeWord_sparse_size]; omega⟩) (by decide) (by decide)]
    have hw := writeWord_sparse_read_window mem (p.toNat + 32) 0 20
      (UInt256.shiftLeft (EVM.word owner.val) ⟨96⟩) (by decide) (by decide) (by decide)
    have hb : (UInt256.shiftLeft (EVM.word owner.val) ⟨96⟩).toByteArray.extract 0 20 =
        (EVM.word owner.val).toByteArray.extract 12 32 :=
      wordBytes_shift_prefix (EVM.word owner.val) 12 (by decide)
    simpa only [Nat.add_zero, Nat.zero_add, hb] using hw
  have h1 : (positionDataMem mem p owner lower upper).readWithPadding (p.toNat + 52) 3 =
      (positionTickWord lower).toByteArray.extract 29 32 := by
    unfold positionDataMem
    rw [writeWord_read_preserved_len_of_disjoint
      (by simp only [writeWord_sparse_size]; have h := lt_usize 0 (by decide); omega)
      (Or.inl ⟨by omega, by simp only [writeWord_sparse_size]; omega⟩) (by decide) (by decide)]
    have hw := writeWord_sparse_read_window
      (writeWord mem (p.toNat + 32) (UInt256.shiftLeft (EVM.word owner.val) ⟨96⟩))
      (p.toNat + 52) 0 3 (UInt256.shiftLeft (positionTickWord lower) ⟨232⟩)
      (by decide) (by decide) (by decide)
    have hb : (UInt256.shiftLeft (positionTickWord lower) ⟨232⟩).toByteArray.extract 0 3 =
        (positionTickWord lower).toByteArray.extract 29 32 :=
      wordBytes_shift_prefix (positionTickWord lower) 29 (by decide)
    simpa only [Nat.add_zero, Nat.zero_add, hb] using hw
  have h2 : (positionDataMem mem p owner lower upper).readWithPadding (p.toNat + 55) 3 =
      (positionTickWord upper).toByteArray.extract 29 32 := by
    unfold positionDataMem
    have hw := writeWord_sparse_read_window
      (writeWord (writeWord mem (p.toNat + 32) (UInt256.shiftLeft (EVM.word owner.val) ⟨96⟩))
        (p.toNat + 52) (UInt256.shiftLeft (positionTickWord lower) ⟨232⟩))
      (p.toNat + 55) 0 3
      (UInt256.shiftLeft (positionTickWord upper) ⟨232⟩) (by decide) (by decide) (by decide)
    have hb : (UInt256.shiftLeft (positionTickWord upper) ⟨232⟩).toByteArray.extract 0 3 =
        (positionTickWord upper).toByteArray.extract 29 32 :=
      wordBytes_shift_prefix (positionTickWord upper) 29 (by decide)
    simpa only [Nat.add_zero, Nat.zero_add, hb] using hw
  simp only [show p.toNat + 32 + 20 = p.toNat + 52 from by omega,
    show p.toNat + 32 + 20 + 3 = p.toNat + 55 from by omega,
    h0, h1, h2, ByteArray.append_assoc, positionPackedBytes]

theorem positionBuildMem_bytes (mem : ByteArray) (p : UInt256) (owner : AccountAddress)
    (lower upper : UInt256) (hp : 128 ≤ p.toNat) :
    (positionBuildMem mem p owner lower upper).readWithPadding (p.toNat + 32) 26 =
      positionPackedBytes owner lower upper := by
  unfold positionBuildMem
  rw [writeWord_read_preserved_len_of_disjoint
      (by simp only [writeWord_sparse_size, positionDataMem_size]; have h := lt_usize 0 (by decide); omega)
      (Or.inr ⟨by omega, by simp only [writeWord_sparse_size, positionDataMem_size]; omega⟩)
      (by decide) (by decide),
    writeWord_read_preserved_len_of_disjoint
      (by rw [positionDataMem_size]; have h := lt_usize 0 (by decide); omega)
      (Or.inr ⟨by omega, by rw [positionDataMem_size]; omega⟩) (by decide) (by decide)]
  exact positionDataMem_bytes mem p owner lower upper

theorem positionBuildMem_length (mem : ByteArray) (p : UInt256) (owner : AccountAddress)
    (lower upper : UInt256) (hp : 128 ≤ p.toNat) :
    memLoad p (positionBuildMem mem p owner lower upper) = ⟨26⟩ := by
  apply mloadWordValue_of_readWithPadding
  · rw [positionBuildMem_size _ _ _ _ _ hp]; omega
  · unfold positionBuildMem
    rw [writeWord_sparse_read_preserved _ _ _ _ (Or.inr ⟨by omega, by
      rw [writeWord_sparse_size]; omega⟩)]
    exact writeWord_sparse_read_back _ _ _

theorem positionBuildMem_free (mem : ByteArray) (p : UInt256) (owner : AccountAddress)
    (lower upper : UInt256) :
    (positionBuildMem mem p owner lower upper).readWithPadding 64 32 =
      (p + ⟨58⟩).toByteArray := writeWord_sparse_read_back _ _ _

theorem positionBuildMem_prefix (mem : ByteArray) (p : UInt256) (owner : AccountAddress)
    (lower upper : UInt256) :
    MemoryPrefix mem (positionBuildMem mem p owner lower upper) p.toNat := by
  unfold positionBuildMem positionDataMem
  refine (memoryPrefix_sparse_writeWord mem (p.toNat + 32) p.toNat
    (UInt256.shiftLeft (EVM.word owner.val) ⟨96⟩)
    (Or.inl (by omega))).trans ?_
  refine (memoryPrefix_sparse_writeWord _ (p.toNat + 52) p.toNat
    (UInt256.shiftLeft (positionTickWord lower) ⟨232⟩)
    (Or.inl (by omega))).trans ?_
  refine (memoryPrefix_sparse_writeWord _ (p.toNat + 55) p.toNat
    (UInt256.shiftLeft (positionTickWord upper) ⟨232⟩)
    (Or.inl (by omega))).trans ?_
  refine (memoryPrefix_sparse_writeWord _ p.toNat p.toNat ⟨26⟩
    (Or.inl (le_refl _))).trans ?_
  exact memoryPrefix_sparse_writeWord _ 64 p.toNat _ (Or.inr (by decide))

theorem positionBuildMem_hash (mem : ByteArray) (p : UInt256) (owner : AccountAddress)
    (lower upper : UInt256) (hp : 128 ≤ p.toNat) (hb : p.toNat + 32 < UInt256.size) :
    keccakWord (⟨32⟩ + p) ⟨26⟩ (positionBuildMem mem p owner lower upper) =
      positionKey owner lower upper := by
  have hoff : (⟨32⟩ + p : UInt256).toNat = p.toNat + 32 := by
    rw [u256_add_comm]
    exact uadd_word_ofNat_toNat p 32 hb
  unfold keccakWord
  rw [hoff, show (⟨26⟩ : UInt256).toNat = 26 from rfl, positionBuildMem_bytes _ _ _ _ _ hp]
  exact keccakSlot_eq _

def positionGetMem (mem : ByteArray) (p : UInt256) (owner : AccountAddress)
    (lower upper slot : UInt256) : ByteArray :=
  twoWordHashMem (positionKey owner lower upper) slot (positionBuildMem mem p owner lower upper)

theorem positionGetMem_size (mem : ByteArray) (p : UInt256) (owner : AccountAddress)
    (lower upper slot : UInt256) (hp : 128 ≤ p.toNat) :
    (positionGetMem mem p owner lower upper slot).size = max mem.size (p.toNat + 87) := by
  unfold positionGetMem twoWordHashMem wordAt32Mem wordAt0Mem
  change (writeWord (writeWord _ 0 _) 32 _).size = _
  rw [writeWord_sparse_size, writeWord_sparse_size, positionBuildMem_size _ _ _ _ _ hp]
  omega

theorem positionGetMem_free (mem : ByteArray) (p : UInt256) (owner : AccountAddress)
    (lower upper slot : UInt256) (hp : 128 ≤ p.toNat) :
    (positionGetMem mem p owner lower upper slot).readWithPadding 64 32 =
      (p + ⟨58⟩).toByteArray := by
  rw [positionGetMem, twoWordHashMem_read_above64 _ _ _ (by decide)
    (by rw [positionBuildMem_size _ _ _ _ _ hp]; omega)]
  exact positionBuildMem_free _ _ _ _ _

theorem positionGetMem_prefix (mem : ByteArray) (p : UInt256) (owner : AccountAddress)
    (lower upper slot : UInt256) :
    MemoryPrefix mem (positionGetMem mem p owner lower upper slot) p.toNat := by
  apply (positionBuildMem_prefix mem p owner lower upper).trans
  unfold positionGetMem twoWordHashMem wordAt32Mem wordAt0Mem
  change MemoryPrefix _ (writeWord (writeWord _ 0 _) 32 _) p.toNat
  exact (memoryPrefix_sparse_writeWord _ 0 _ _ (Or.inr (by decide))).trans
    (memoryPrefix_sparse_writeWord _ 32 _ _ (Or.inr (by decide)))

theorem positionGetMem_hash (mem : ByteArray) (p : UInt256) (owner : AccountAddress)
    (lower upper slot : UInt256) :
    keccakWord ⟨0⟩ ⟨64⟩ (positionGetMem mem p owner lower upper slot) =
      solcMappingSlot slot (positionKey owner lower upper) := by
  unfold keccakWord
  rw [positionGetMem]
  exact twoWordHashMem_solcMappingSlot_any _ _ _

theorem positionGetMem_zero_initial (owner : AccountAddress) (lower upper slot : UInt256) :
    memLoad (UInt256.ofNat 96) (positionGetMem solcFreePtrMem ⟨128⟩ owner lower upper slot) = ⟨0⟩ := by
  apply mloadWordValue_of_readWithPadding
  · change 96 < _
    rw [positionGetMem_size _ _ _ _ _ _ (by decide), solcFreePtrMem_size]
    decide
  · change (positionGetMem solcFreePtrMem ⟨128⟩ owner lower upper slot).readWithPadding 96 32 = _
    unfold positionGetMem twoWordHashMem wordAt32Mem wordAt0Mem positionBuildMem positionDataMem
    change (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord
      (writeWord solcFreePtrMem 160 (UInt256.shiftLeft (EVM.word owner.val) ⟨96⟩))
      180 (UInt256.shiftLeft (positionTickWord lower) ⟨232⟩))
      183 (UInt256.shiftLeft (positionTickWord upper) ⟨232⟩))
      128 ⟨26⟩) 64 ⟨186⟩) 0 (positionKey owner lower upper)) 32 slot).readWithPadding 96 32 = _
    rw [writeWord_sparse_read_preserved _ _ _ _ (Or.inr ⟨by decide, by
      simp only [writeWord_sparse_size, solcFreePtrMem_size]; decide⟩)]
    rw [writeWord_sparse_read_preserved _ _ _ _ (Or.inr ⟨by decide, by
      simp only [writeWord_sparse_size, solcFreePtrMem_size]; decide⟩)]
    rw [writeWord_sparse_read_preserved _ _ _ _ (Or.inr ⟨by decide, by
      simp only [writeWord_sparse_size, solcFreePtrMem_size]; decide⟩)]
    rw [writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨by decide, by
      simp only [writeWord_sparse_size, solcFreePtrMem_size]; decide⟩)]
    rw [writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨by decide, by
      simp only [writeWord_sparse_size, solcFreePtrMem_size]; decide⟩)]
    rw [writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨by decide, by
      simp only [writeWord_sparse_size, solcFreePtrMem_size]; decide⟩)]
    rw [writeWord_sparse_eq _ _ _ (by rw [solcFreePtrMem_size]; decide)]
    rw [readWithPadding_eq_extract _ _ (by
      simp only [ByteArray.size_append, solcFreePtrMem_size, ByteArray_zeroes_size, toByteArray_size]
      decide)]
    rw [extract_append_left _ _ _ _ (by
      simp only [ByteArray.size_append, solcFreePtrMem_size, ByteArray_zeroes_size]; decide)]
    rw [solcFreePtrMem_size]
    change (solcFreePtrMem ++ ByteArray.zeroes 64).extract 96 128 = (⟨0⟩ : UInt256).toByteArray
    decide +kernel

end Benchmarks.UniswapV3.Pool
