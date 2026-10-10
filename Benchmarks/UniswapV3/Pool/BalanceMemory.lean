import Benchmarks.UniswapV3.Pool.SafeTransferMemory
import Benchmarks.UniswapV3.Pool.BalanceSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: replacing a selector preserves the ABI payload after it.
theorem selectorPatch_read_payload (mem : ByteArray) (off first : UInt256) (len : Nat)
    (hlen : 28 < len) (hsmall : 4 + len < 2 ^ 64)
    (hin : off.toNat + 4 + len ≤ mem.size) :
    (writeWord mem off.toNat (spliceWord4 first (memLoad off mem))).readWithPadding
        off.toNat (4 + len) =
      first.toByteArray.extract 0 4 ++ mem.readWithPadding (off.toNat + 4) len := by
  have hsize := writeWord_sparse_size mem off.toNat (spliceWord4 first (memLoad off mem))
  rw [show 4 + len = 32 + (len - 28) by omega,
    byteArray_readWithPadding_split _ _ 32 (len - 28)
      (by decide) (by omega) (by decide) (by omega) (by omega) (by omega),
    writeWord_sparse_read_back, spliceWord4_toByteArray,
    memLoad_toByteArray_window mem off 4 28 (by omega) (by decide) (by decide),
    writeWord_sparse_read_preserved_len _ _ _ (len - 28) _
      (Or.inr ⟨by omega, by omega⟩) (by omega) (by omega), ByteArray.append_assoc]
  rw [show off.toNat + 32 = (off.toNat + 4) + 28 by omega,
    ← byteArray_readWithPadding_split mem (off.toNat + 4) 28 (len - 28)
      (by decide) (by omega) (by decide) (by omega) (by omega) (by omega),
    show 28 + (len - 28) = len by omega]

def balanceSelectorWord : UInt256 := UInt256.shiftLeft (UInt256.ofNat 1889567281) ⟨224⟩

def balanceSelectorPatchedWord (old : UInt256) : UInt256 :=
  UInt256.lor balanceSelectorWord (UInt256.land (UInt256.ofNat (2 ^ 224 - 1)) old)

theorem balanceSelectorPatchedWord_eq (old : UInt256) :
    balanceSelectorPatchedWord old = spliceWord4 balanceSelectorWord old := by
  unfold balanceSelectorPatchedWord spliceWord4
  rw [show UInt256.land balanceSelectorWord (UInt256.lnot (UInt256.ofNat (2 ^ 224 - 1))) =
    balanceSelectorWord from by decide +kernel, u256_land_comm old]

def balanceArgsMem (mem : ByteArray) (p who : UInt256) : ByteArray :=
  writeWord mem (p.toNat + 36) who

def balanceHeadMem (mem : ByteArray) (p who : UInt256) : ByteArray :=
  writeWord (writeWord (balanceArgsMem mem p who) p.toNat ⟨36⟩) 64 (p + ⟨68⟩)

def balanceBuildMem (mem : ByteArray) (p who : UInt256) : ByteArray :=
  writeWord (balanceHeadMem mem p who) (p.toNat + 32)
    (balanceSelectorPatchedWord (memLoad (p + ⟨32⟩) (balanceHeadMem mem p who)))

theorem balanceArgsMem_size (mem : ByteArray) (p who : UInt256) :
    (balanceArgsMem mem p who).size = max mem.size (p.toNat + 68) := by
  simp only [balanceArgsMem, writeWord_sparse_size]

theorem balanceHeadMem_size (mem : ByteArray) (p who : UInt256) (hp : 128 ≤ p.toNat) :
    (balanceHeadMem mem p who).size = max mem.size (p.toNat + 68) := by
  simp only [balanceHeadMem, writeWord_sparse_size, balanceArgsMem_size]; omega

theorem balanceBuildMem_size (mem : ByteArray) (p who : UInt256) (hp : 128 ≤ p.toNat) :
    (balanceBuildMem mem p who).size = max mem.size (p.toNat + 68) := by
  simp only [balanceBuildMem, writeWord_sparse_size, balanceHeadMem_size _ _ _ hp]; omega

theorem balanceArgsMem_load64 {mem : ByteArray} {aw p : UInt256}
    (hm : HeapMemory mem aw p) (who : UInt256) :
    memLoad (UInt256.ofNat 64) (balanceArgsMem mem p who) = p := by
  have hp := hm.lower
  apply mloadWordValue_of_readWithPadding
  · change 64 < _; rw [balanceArgsMem_size]; omega
  · change (balanceArgsMem mem p who).readWithPadding 64 32 = _
    unfold balanceArgsMem
    rw [writeWord_sparse_read_preserved _ _ 64 _ (Or.inl ⟨by omega, hm.size⟩)]
    exact hm.free

theorem balanceHeadMem_read64 (mem : ByteArray) (p who : UInt256) :
    (balanceHeadMem mem p who).readWithPadding 64 32 = (p + ⟨68⟩).toByteArray :=
  writeWord_sparse_read_back _ _ _

theorem balanceHeadMem_read_length (mem : ByteArray) (p who : UInt256)
    (hp : 128 ≤ p.toNat) :
    (balanceHeadMem mem p who).readWithPadding p.toNat 32 = (⟨36⟩ : UInt256).toByteArray := by
  unfold balanceHeadMem
  rw [writeWord_sparse_read_preserved _ _ _ _ (Or.inr ⟨by omega, by
    rw [writeWord_sparse_size]; omega⟩)]
  exact writeWord_sparse_read_back _ _ _

theorem balanceHeadMem_read_arg {mem : ByteArray} {aw p : UInt256}
    (hm : HeapMemory mem aw p) (who : UInt256) :
    (balanceHeadMem mem p who).readWithPadding (p.toNat + 36) 32 = who.toByteArray := by
  have hp := hm.lower
  have hg := hm.gap
  have hu := lt_usize 68 (by decide)
  change (writeCascade mem [(p.toNat + 36, who), (p.toNat, ⟨36⟩),
    (64, p + ⟨68⟩)]).readWithPadding (p.toNat + 36) 32 = _
  apply writeCascade_read_word_of_head
  · omega
  · simp [WindowDisjointFromWrites, Nat.add_assoc]; omega

theorem balanceBuildMem_read64 (mem : ByteArray) (p who : UInt256) (hp : 128 ≤ p.toNat) :
    (balanceBuildMem mem p who).readWithPadding 64 32 = (p + ⟨68⟩).toByteArray := by
  unfold balanceBuildMem
  rw [writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨by omega, by
    rw [balanceHeadMem_size _ _ _ hp]; omega⟩), balanceHeadMem_read64]

theorem balanceBuildMem_load_length (mem : ByteArray) (p who : UInt256)
    (hp : 128 ≤ p.toNat) : memLoad p (balanceBuildMem mem p who) = ⟨36⟩ := by
  apply mloadWordValue_of_readWithPadding
  · rw [balanceBuildMem_size _ _ _ hp]; omega
  · unfold balanceBuildMem
    rw [writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨by omega, by
      rw [balanceHeadMem_size _ _ _ hp]; omega⟩), balanceHeadMem_read_length _ _ _ hp]

theorem balanceBuildMem_load64 (mem : ByteArray) (p who : UInt256) (hp : 128 ≤ p.toNat) :
    memLoad (UInt256.ofNat 64) (balanceBuildMem mem p who) = p + ⟨68⟩ := by
  apply mloadWordValue_of_readWithPadding
  · change 64 < _; rw [balanceBuildMem_size _ _ _ hp]; omega
  · exact balanceBuildMem_read64 _ _ _ hp

theorem balanceBuildMem_prefix (mem : ByteArray) (p who : UInt256) :
    MemoryPrefix mem (balanceBuildMem mem p who) p.toNat := by
  unfold balanceBuildMem balanceHeadMem balanceArgsMem
  refine (memoryPrefix_sparse_writeWord mem (p.toNat + 36) p.toNat who
    (Or.inl (by omega))).trans ?_
  refine (memoryPrefix_sparse_writeWord _ p.toNat p.toNat ⟨36⟩
    (Or.inl (le_refl _))).trans ?_
  refine (memoryPrefix_sparse_writeWord _ 64 p.toNat (p + ⟨68⟩)
    (Or.inr (by decide))).trans ?_
  exact memoryPrefix_sparse_writeWord _ (p.toNat + 32) p.toNat _ (Or.inl (by omega))

theorem balanceBuildMem_calldata {mem : ByteArray} {aw p : UInt256}
    (hm : HeapMemory mem aw p) (who : AccountAddress) (hb : p.toNat + 68 < UInt256.size) :
    (balanceBuildMem mem p (EVM.word who.val)).readWithPadding (p.toNat + 32) 36 =
      balanceCalldata who := by
  have h32 : (p + (⟨32⟩ : UInt256)).toNat = p.toNat + 32 := uadd_word_ofNat_toNat p 32 (by omega)
  unfold balanceBuildMem
  rw [balanceSelectorPatchedWord_eq, ← h32]
  rw [show 36 = 4 + 32 from rfl, selectorPatch_read_payload _ _ _ 32
    (by decide) (by decide) (by rw [h32, balanceHeadMem_size _ _ _ hm.lower]; omega), h32]
  rw [show p.toNat + 32 + 4 = p.toNat + 36 by omega, balanceHeadMem_read_arg hm]
  exact congrArg (fun x : ByteArray ↦ x ++ (EVM.word who.val).toByteArray) (by decide +kernel)

end Benchmarks.UniswapV3.Pool
