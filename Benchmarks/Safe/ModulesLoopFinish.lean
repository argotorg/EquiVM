import Benchmarks.Safe.ModulesLoop
import Benchmarks.Safe.ModulesSource
import Benchmarks.Safe.CheckedSubtract
import Benchmarks.Safe.Memory
import Benchmarks.Safe.Blocks.Runtime_026

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeModulesLastWord {mem capacity words}
    (hm : AddressArrayMemory mem capacity (words ++ List.replicate (capacity - words.length) ⟨0⟩))
    (hi : 0 < words.length) (hn : capacity ≤ 2 ^ 64 - 1) (hlen : words.length ≤ capacity) :
    memLoad ((UInt256.ofNat 32 + UInt256.mul (UInt256.ofNat 32)
      (UInt256.ofNat (words.length - 1))) + ⟨128⟩) mem = words.getLastD ⟨0⟩ := by
  have hp := safeAddressArrayIndexAddress (words.length - 1) (by omega)
  rw [← uadd_assoc] at hp
  apply memLoad_of_wordRead
  change ((UInt256.ofNat 32 + UInt256.mul (UInt256.ofNat 32)
    (UInt256.ofNat (words.length - 1))) + (⟨128⟩ : UInt256)).toNat = _ at hp
  rw [hp]
  have hb : words.length - 1 < words.length := by omega
  have hr := hm.words (words.length - 1) (by simp; omega)
  rw [List.getElem_append_left hb] at hr
  have hw : words ≠ [] := by intro he; simp [he] at hi
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hw,
    Option.getD_some, List.getLast_eq_getElem]
  exact hr

theorem safeModulesFinish {I g s0 σ k C aw mem rdata capacity words next start ret}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨5128⟩
      (UInt256.ofNat words.length :: next :: ⟨128⟩ :: UInt256.ofNat capacity :: start :: ret :: R)
      mem aw rdata σ k C)
    (hov : R.length + 13 ≤ 1024)
    (hm : AddressArrayMemory mem capacity (words ++ List.replicate (capacity - words.length) ⟨0⟩))
    (hn : capacity ≤ 2 ^ 64 - 1) (hlen : words.length ≤ capacity)
    (hc : next.toNat < EVM.addressModulus) (hg : next = ⟨1⟩ ∨ 0 < words.length)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD safeBytecode I g s0 ret (modulesPageNext words next :: ⟨128⟩ :: R)
      (writeWord mem 128 (UInt256.ofNat words.length)) aw' rdata σ k' C' := by
  have h5184 : ∃ aw' k' C', RD safeBytecode I g s0 ⟨5184⟩
      (UInt256.ofNat words.length :: modulesPageNext words next :: ⟨128⟩ ::
        UInt256.ofNat capacity :: start :: ret :: R) mem aw' rdata σ k' C' := by
    by_cases hs : next = ⟨1⟩
    · have h₁ := safeRuntime_block_5128_taken (by simp; omega)
        (by rw [safeAddressMask, solcAddrMask_clean hc, hs]; decide) (by jump_dest) h
      exact ⟨_, _, _, by simpa [modulesPageNext, hs] using h₁⟩
    · have hi : 0 < words.length := hg.resolve_left hs
      have h₁ := safeRuntime_block_5128_fallthrough (by simp; omega)
        (by rw [safeAddressMask, solcAddrMask_clean hc]; exact u256_eq_of_ne (Ne.symm hs)) h
      have h₂ := safeRuntime_block_5146 (by simp; omega) (by jump_dest) h₁
      have hlword := ulit_toNat' words.length (by change words.length < 2 ^ 256; omega)
      have hnword := ulit_toNat' capacity (by change capacity < 2 ^ 256; omega)
      obtain ⟨k₃, C₃, h₃⟩ := safeSubtractTrace h₂
        (by simp only [safeRuntime_block_5146_stack, List.length_cons]; omega)
        (by rw [hlword]; exact hi) (by jump_dest)
      have hsub : UInt256.sub (UInt256.ofNat words.length) (UInt256.ofNat 1) =
          UInt256.ofNat (words.length - 1) := by
        apply u256_inj
        rw [usub_toNat (by rw [hlword]; exact hi), hlword]
        exact (ulit_toNat' _ (by change words.length - 1 < 2 ^ 256; omega)).symm
      rw [hsub] at h₃
      have hcount : memLoad ⟨128⟩ mem = UInt256.ofNat capacity :=
        memLoad_of_wordRead mem _ _ hm.count
      have hlt := ult_one (a := UInt256.ofNat (words.length - 1)) (b := UInt256.ofNat capacity)
        (by rw [hnword, ulit_toNat' _ (by change words.length - 1 < 2 ^ 256; omega)]; omega)
      have h₄ := safeRuntime_block_5157_taken (by simp; omega)
        (by rw [hcount, hlt]; decide) (by jump_dest) h₃
      have h₅ := safeRuntime_block_5173 (by simp; omega) h₄
      simp only [safeRuntime_block_5173_stack, safeModulesLastWord hm hi hn hlen] at h₅
      exact ⟨_, _, _, by simpa only [modulesPageNext, hs, if_false] using h₅⟩
  obtain ⟨aw₁, k₁, C₁, h₁⟩ := h5184
  exact safeRuntime_block_5184_packed (by simp; omega) hret h₁

theorem safeModulesFinishEmpty {I g s0 σ k C aw mem rdata capacity next start ret}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨5128⟩
      (⟨0⟩ :: next :: ⟨128⟩ :: capacity :: start :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 14 ≤ 1024) (hc : next.toNat < EVM.addressModulus)
    (hs : next ≠ ⟨1⟩) : RDrev safeBytecode g s0 := by
  have h₁ := safeRuntime_block_5128_fallthrough (by simp; omega)
    (by rw [safeAddressMask, solcAddrMask_clean hc]; exact u256_eq_of_ne (Ne.symm hs)) h
  have h₂ := safeRuntime_block_5146 (by simp; omega) (by jump_dest) h₁
  exact safeSubtractZeroOne h₂
    (by simp only [safeRuntime_block_5146_stack, List.length_cons]; omega)

end Benchmarks.Safe
