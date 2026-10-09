import Benchmarks.Safe.ModulesEncoding
import Benchmarks.Safe.AddressArrayMemory
import Benchmarks.Safe.AddressArrayCopy
import Benchmarks.Safe.Blocks.Runtime_010
import Benchmarks.Safe.Blocks.Runtime_047
import Benchmarks.Safe.Blocks.Runtime_007

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

theorem safeModulesReturn {I g s0 σ k C aw mem rdata capacity words next} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨1301⟩ (next :: ⟨128⟩ :: R)
      (writeWord mem 128 (UInt256.ofNat words.length)) aw rdata σ k C)
    (hov : R.length + 18 ≤ 1024)
    (hm : AddressArrayMemory mem capacity (words ++ List.replicate (capacity - words.length) ⟨0⟩))
    (hn : capacity ≤ 2 ^ 64 - 1) (hlen : words.length ≤ capacity)
    (hc : ∀ w ∈ words, w.toNat < EVM.addressModulus)
    (hnext : next.toNat < EVM.addressModulus) :
    RDret safeBytecode g s0 σ (modulesReturnBytes words next) := by
  let baseMem := writeWord mem 128 (UInt256.ofNat words.length)
  let fp := 160 + 32 * capacity
  have hbsize : baseMem.size = mem.size := by
    rw [writeWord_sparse_size, Nat.max_eq_left hm.lower]
  have hbupper : baseMem.size ≤ fp := by rw [hbsize]; exact hm.upper
  have hbfree : baseMem.readWithPadding 64 32 = (addressArrayFreePtr capacity).toByteArray := by
    rw [writeWord_sparse_read_preserved _ _ _ _
      (.inl ⟨by decide, by have := hm.lower; omega⟩)]
    exact hm.freePtr
  have hbwords : WordArrayMemory baseMem 160 words :=
    hm.words.appendLeft.writeDisjoint mem 160 words hm.aligned (by decide) 128
      (UInt256.ofNat words.length) (.inl (by decide))
  have hfp : (addressArrayFreePtr capacity).toNat = fp :=
    ulit_toNat' _ (by change 160 + 32 * capacity < 2 ^ 256; omega)
  have hfpadd (j : Nat) (hj : j ≤ 96) :
      addressArrayFreePtr capacity + UInt256.ofNat j = UInt256.ofNat (fp + j) := by
    apply u256_inj
    rw [uadd_toNat, hfp, ulit_toNat' j (by change j < 2 ^ 256; omega)]
    rfl
  have hfree : memLoad (UInt256.ofNat 64) baseMem = addressArrayFreePtr capacity :=
    memLoad_of_wordRead _ _ _ hbfree
  obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeRuntime_block_1301_packed (by omega) (by jump_dest) h
  change RD safeBytecode I g s0 ⟨10638⟩
    (memLoad (UInt256.ofNat 64) baseMem :: next :: ⟨128⟩ :: ⟨771⟩ :: R)
    baseMem aw₁ rdata σ k₁ C₁ at h₁
  rw [hfree] at h₁
  obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeRuntime_block_10638_packed (by simp; omega)
    (by jump_dest) h₁
  simp only [safeRuntime_block_10638_stack, safeRuntime_block_10638_memory,
    hfp, hfpadd 64 (by decide)] at h₂
  have hcount : memLoad ⟨128⟩ (writeWord baseMem fp ⟨64⟩) = UInt256.ofNat words.length := by
    apply memLoad_of_wordRead
    change (writeWord baseMem fp ⟨64⟩).readWithPadding 128 32 = _
    rw [writeWord_sparse_read_preserved _ _ _ _
      (.inl ⟨by dsimp [fp]; omega, by rw [hbsize]; exact hm.lower⟩)]
    exact writeWord_sparse_read_back _ _ _
  obtain ⟨aw₃, k₃, C₃, h₃⟩ := safeRuntime_block_10238_packed (by simp; omega) h₂
  change RD safeBytecode I g s0 ⟨10256⟩
    (⟨0⟩ :: (⟨128⟩ + UInt256.ofNat 32) :: memLoad ⟨128⟩ (writeWord baseMem fp ⟨64⟩) ::
      ⟨0⟩ :: ⟨128⟩ :: (UInt256.ofNat (fp + 64) + UInt256.ofNat 32) ::
      ⟨10656⟩ :: ⟨0⟩ :: addressArrayFreePtr capacity :: next :: ⟨128⟩ :: ⟨771⟩ :: R)
    (writeWord (writeWord baseMem fp ⟨64⟩) (UInt256.ofNat (fp + 64)).toNat
      (memLoad ⟨128⟩ (writeWord baseMem fp ⟨64⟩))) aw₃ rdata σ k₃ C₃ at h₃
  have ha : UInt256.ofNat (fp + 64) + UInt256.ofNat 32 = UInt256.ofNat (fp + 96) := by
    rw [u256_add_comm]
    simpa only [Nat.add_assoc] using u256_32_add_ofNat (fp + 64)
  rw [hcount, ha, ulit_toNat' _ (by change fp + 64 < 2 ^ 256; dsimp [fp]; omega)] at h₃
  have hwords := modulesHeaderWords baseMem fp words hbwords (by rw [hbsize]; exact hm.aligned)
    (by dsimp [fp]; omega) (by dsimp [fp]; omega)
  have hmsize := modulesHeaderSize baseMem fp words.length hbupper
  obtain ⟨aw₄, k₄, C₄, h₄⟩ := safeAddressArrayCopyLoop words (i := 0) (src := 160) h₃
    (by simp; omega) hwords hmsize (by dsimp [fp]; omega) (by simp)
    (by change words.length < 2 ^ 256; omega)
    (by change fp + 96 + 32 * words.length < 2 ^ 256; dsimp [fp]; omega) hc (by jump_dest)
  obtain ⟨aw₅, k₅, C₅, h₅⟩ := safeRuntime_block_10656_packed (by simp; omega)
    (by jump_dest) h₄
  have hfp32 : (addressArrayFreePtr capacity + UInt256.ofNat 32).toNat = fp + 32 := by
    rw [hfpadd 32 (by decide), ulit_toNat' _ (by change fp + 32 < 2 ^ 256; dsimp [fp]; omega)]
  simp only [safeRuntime_block_10656_stack, safeRuntime_block_10656_memory,
    safeAddressMask, solcAddrMask_clean hnext, hfp32] at h₅
  have hret := safeRuntime_block_771 (by omega) h₅
  let encoded := modulesEncodedMemory baseMem fp words next
  have hefree : memLoad (UInt256.ofNat 64) encoded = addressArrayFreePtr capacity := by
    apply memLoad_of_wordRead
    change (modulesEncodedMemory baseMem fp words next).readWithPadding 64 32 = _
    rw [modulesEncodedRead64 baseMem fp words next hbupper (by
      rw [hbsize]
      have := hm.lower
      omega)]
    exact hbfree
  change RDret safeBytecode g s0 σ (encoded.readWithPadding
    (memLoad (UInt256.ofNat 64) encoded).toNat
    (UInt256.sub (UInt256.ofNat (fp + 96 + 32 * words.length))
      (memLoad (UInt256.ofNat 64) encoded)).toNat) at hret
  have hend : (UInt256.ofNat (fp + 96 + 32 * words.length)).toNat =
      fp + 96 + 32 * words.length :=
    ulit_toNat' _ (by change fp + 96 + 32 * words.length < 2 ^ 256; dsimp [fp]; omega)
  rw [hefree, usub_toNat (by rw [hfp, hend]; omega), hfp, hend] at hret
  have hlen' : fp + 96 + 32 * words.length - fp = 96 + 32 * words.length := by omega
  rw [hlen', modulesEncodedRead baseMem fp words next hbupper] at hret
  exact hret

end Benchmarks.Safe
