import Benchmarks.Safe.ViaIR.AddressArrayMemory
import Benchmarks.Safe.ViaIR.AddressArrayCopy
import Benchmarks.Safe.ViaIR.AddressArrayEncoding
import Benchmarks.Safe.ViaIR.Blocks.Runtime_020
import Benchmarks.Safe.ViaIR.Blocks.Runtime_005

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

set_option maxHeartbeats 800000 in
theorem safeGetOwnersReturnTrace {I g s0 σ k C aw mem rdata n words i} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4171⟩
      (⟨1⟩ :: ⟨0⟩ :: UInt256.ofNat i :: ⟨128⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 18 ≤ 1024) (hm : AddressArrayMemory mem n words)
    (hn : n ≤ 2 ^ 64 - 1) (hc : ∀ w ∈ words, w.toNat < EVM.addressModulus) :
    RDret fork safeBytecode g s0 σ (addressArrayReturnBytes words) := by
  let fp := 160 + 32 * n
  have hfp : (addressArrayFreePtr n).toNat = fp :=
    ulit_toNat' _ (by change 160 + 32 * n < 2 ^ 256; omega)
  have hfpadd : addressArrayFreePtr n + UInt256.ofNat 32 = UInt256.ofNat (fp + 32) := by
    rw [u256_add_comm]
    exact u256_32_add_ofNat fp
  have hfree : memLoad (UInt256.ofNat 64) mem = addressArrayFreePtr n :=
    memLoad_of_wordRead _ _ _ hm.freePtr
  obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeRuntime_block_4171_packed (by omega) (by jump_dest) h
  simp only [safeRuntime_block_4171_stack, safeRuntime_block_4171_memory,
    hfree, hfp, hfpadd] at h₁
  have hcount : memLoad ⟨128⟩ (writeWord mem fp (UInt256.ofNat 32)) = UInt256.ofNat n := by
    apply memLoad_of_wordRead
    change (writeWord mem fp (UInt256.ofNat 32)).readWithPadding 128 32 = _
    rw [writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨by dsimp [fp]; omega, hm.lower⟩)]
    exact hm.count
  obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeRuntime_block_7437_packed (by simp; omega) h₁
  change RD fork safeBytecode I g s0 ⟨7453⟩
    (⟨0⟩ :: memLoad ⟨128⟩ (writeWord mem fp (UInt256.ofNat 32)) ::
      (⟨128⟩ + UInt256.ofNat 32) :: (UInt256.ofNat (fp + 32) + UInt256.ofNat 32) ::
      ⟨585⟩ :: addressArrayFreePtr n :: addressArrayFreePtr n ::
      ⟨1⟩ :: ⟨0⟩ :: UInt256.ofNat i :: ⟨128⟩ :: R)
    (writeWord (writeWord mem fp (UInt256.ofNat 32)) (UInt256.ofNat (fp + 32)).toNat
      (memLoad ⟨128⟩ (writeWord mem fp (UInt256.ofNat 32)))) aw₂ rdata σ k₂ C₂ at h₂
  have ha : UInt256.ofNat (fp + 32) + UInt256.ofNat 32 = UInt256.ofNat (fp + 64) := by
    rw [u256_add_comm]
    simpa only [Nat.add_assoc] using u256_32_add_ofNat (fp + 32)
  rw [hcount, ha, ulit_toNat' _ (by change fp + 32 < 2 ^ 256; dsimp [fp]; omega)] at h₂
  have hwords := addressArrayHeaderWords mem fp words 160 hm.words hm.aligned
    (by decide) (by dsimp [fp]; omega) (by rw [hm.length])
  rw [hm.length] at hwords
  have hmsize := addressArrayHeaderSize mem fp n hm.upper
  obtain ⟨_, _, _, h585⟩ := safeAddressArrayCopyLoop words (i := 0) (src := 160) h₂
    (by simp; omega) hwords hmsize (by rw [hm.length]; dsimp [fp]; omega)
    (by simpa using hm.length) (by change n < 2 ^ 256; omega)
    (by rw [hm.length]; change fp + 64 + 32 * n < 2 ^ 256; dsimp [fp]; omega)
    hc (by jump_dest)
  have hret := safeRuntime_block_585 (by simp; omega) h585
  let encoded := addressArrayHeaderMemory mem fp n ++ wordBytes words
  change RDret fork safeBytecode g s0 σ (encoded.readWithPadding
    (addressArrayFreePtr n).toNat
    (UInt256.sub (UInt256.ofNat (fp + 64 + 32 * words.length))
      (addressArrayFreePtr n)).toNat) at hret
  have hend : (UInt256.ofNat (fp + 64 + 32 * words.length)).toNat =
      fp + 64 + 32 * words.length :=
    ulit_toNat' _ (by rw [hm.length]; change fp + 64 + 32 * n < 2 ^ 256; dsimp [fp]; omega)
  rw [usub_toNat (by rw [hfp, hend]; omega), hfp, hend] at hret
  have hlen : fp + 64 + 32 * words.length - fp = 64 + 32 * words.length := by omega
  rw [hlen] at hret
  have hread := addressArrayEncodedRead mem fp words hm.upper
  rw [hm.length] at hread
  rw [hm.length] at hret
  rw [hread] at hret
  exact hret

end Benchmarks.Safe.ViaIR
