import Benchmarks.Safe.ViaIR.ModulesLoop
import Benchmarks.Safe.ViaIR.ModulesSource
import Benchmarks.Safe.ViaIR.Memory
import Benchmarks.Safe.ViaIR.Blocks.Runtime_014

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem safeModulesLastWord {mem capacity words}
    (hm : AddressArrayMemory mem capacity (words ++ List.replicate (capacity - words.length) ⟨0⟩))
    (hi : 0 < words.length) (hn : capacity ≤ 2 ^ 64 - 1) (hlen : words.length ≤ capacity) :
    memLoad ((UInt256.shiftLeft (UInt256.ofNat (words.length - 1)) (UInt256.ofNat 5) +
      ⟨128⟩) + UInt256.ofNat 32) mem = words.getLastD ⟨0⟩ := by
  have hp : ((UInt256.shiftLeft (UInt256.ofNat (words.length - 1)) (UInt256.ofNat 5) +
      (⟨128⟩ : UInt256)) + UInt256.ofNat 32).toNat = 160 + 32 * (words.length - 1) := by
    have hshift : UInt256.shiftLeft (UInt256.ofNat (words.length - 1)) (UInt256.ofNat 5) =
        UInt256.ofNat (32 * (words.length - 1)) :=
      shiftLeft5_ofNat_eq (by change 32 * (words.length - 1) < 2 ^ 256; omega)
    change ((UInt256.shiftLeft (UInt256.ofNat (words.length - 1)) (UInt256.ofNat 5) +
      UInt256.ofNat 128) + UInt256.ofNat 32).toNat = _
    rw [hshift, uadd3_ofNat_toNat (by change 32 * (words.length - 1) < 2 ^ 256; omega)
      (by decide) (by decide) (by change 32 * (words.length - 1) + 128 < 2 ^ 256; omega)
      (by change 32 * (words.length - 1) + 128 + 32 < 2 ^ 256; omega)]
    omega
  apply memLoad_of_wordRead
  rw [hp]
  have hb : words.length - 1 < words.length := by omega
  have hr := hm.words (words.length - 1) (by simp; omega)
  rw [List.getElem_append_left hb] at hr
  have hw : words ≠ [] := by intro he; simp [he] at hi
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hw,
    Option.getD_some, List.getLast_eq_getElem]
  exact hr

theorem safeModulesFinish {I g s0 σ k C aw mem rdata capacity words next}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2710⟩
      (next :: next :: ⟨128⟩ :: UInt256.ofNat capacity :: UInt256.ofNat words.length :: ⟨0⟩ :: R)
      mem aw rdata σ k C)
    (hov : R.length + 13 ≤ 1024)
    (hm : AddressArrayMemory mem capacity (words ++ List.replicate (capacity - words.length) ⟨0⟩))
    (hn : capacity ≤ 2 ^ 64 - 1) (hlen : words.length ≤ capacity)
    (hc : next.toNat < EVM.addressModulus)
    (hcwords : ∀ w ∈ words, w.toNat < EVM.addressModulus)
    (hg : next = ⟨1⟩ ∨ 0 < words.length) :
    ∃ aw' k' C' scratch, RD fork safeBytecode I g s0 ⟨2734⟩
      (UInt256.ofNat words.length :: modulesPageNext words next :: ⟨128⟩ :: scratch :: R)
      mem aw' rdata σ k' C' := by
  by_cases hs : next = ⟨1⟩
  · have h2734 := safeRuntime_block_2710_fallthrough (by simp; omega)
      (by rw [safeAddressMask, solcAddrMask_clean hc, hs]; decide) h
    refine ⟨aw, k + 19, C + 59, ⟨0⟩, ?_⟩
    simpa [safeRuntime_block_2710_fallthrough_stack, modulesPageNext, hs] using h2734
  · have hi : 0 < words.length := hg.resolve_left hs
    have h2781 := safeRuntime_block_2710_taken (by simp; omega)
      (by rw [safeAddressMask, solcAddrMask_clean hc, u256_add_lnot_zero_eq_sub_one]
          exact u256_sub_ne_zero_of_ne hs) (by jump_dest) h
    simp only [safeRuntime_block_2710_taken_stack] at h2781
    have hlword := ulit_toNat' words.length (by change words.length < 2 ^ 256; omega)
    have hnword := ulit_toNat' capacity (by change capacity < 2 ^ 256; omega)
    have hpred := ulit_toNat' (words.length - 1)
      (by change words.length - 1 < 2 ^ 256; omega)
    have hsub : UInt256.ofNat words.length + UInt256.lnot ⟨0⟩ =
        UInt256.ofNat (words.length - 1) := by
      rw [u256_add_lnot_zero_eq_pred_of_pos _ (by rw [hlword]; exact hi), hlword]
    have h2795 := safeRuntime_block_2781_fallthrough (by simp; omega)
      (by rw [hsub]; exact ugt_zero (by rw [hlword, hpred]; omega)) h2781
    simp only [safeRuntime_block_2781_fallthrough_stack, hsub] at h2795
    have h9000 := safeRuntime_block_2795 (by simp; omega) (by jump_dest) h2795
    simp only [safeRuntime_block_2795_stack, safeAddressMask] at h9000
    have hcount : memLoad ⟨128⟩ mem = UInt256.ofNat capacity :=
      memLoad_of_wordRead mem _ _ hm.count
    have hlt := ult_one (a := UInt256.ofNat (words.length - 1)) (b := UInt256.ofNat capacity)
      (by rw [hnword, hpred]; omega)
    obtain ⟨_, _, _, h9010⟩ := safeRuntime_block_9000_fallthrough_packed (by simp; omega)
      (by rw [hcount, hlt]; decide) h9000
    have h2818 := safeRuntime_block_9010 (by simp; omega) (by jump_dest) h9010
    simp only [safeRuntime_block_9010_stack] at h2818
    obtain ⟨aw', k', C', h2734⟩ := safeRuntime_block_2818_packed (by simp; omega)
      (by jump_dest) h2818
    have hlast : (words.getLastD ⟨0⟩).toNat < EVM.addressModulus := by
      have hw := List.getLastD_mem_cons (l := words) (a := (⟨0⟩ : UInt256))
      rcases List.mem_cons.mp hw with hw | hw
      · rw [hw]; decide
      · exact hcwords _ hw
    simp only [safeRuntime_block_2818_stack, safeModulesLastWord hm hi hn hlen,
      solcAddrMask_clean hlast] at h2734
    exact ⟨aw', k', C', ⟨2761⟩, by simpa only [modulesPageNext, hs, if_false] using h2734⟩

theorem safeModulesFinishEmpty {I g s0 σ k C aw mem rdata capacity next}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2710⟩
      (next :: next :: ⟨128⟩ :: capacity :: ⟨0⟩ :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 14 ≤ 1024) (hc : next.toNat < EVM.addressModulus)
    (hs : next ≠ ⟨1⟩) : RDrev fork safeBytecode g s0 := by
  have h2781 := safeRuntime_block_2710_taken (by simp; omega)
    (by rw [safeAddressMask, solcAddrMask_clean hc, u256_add_lnot_zero_eq_sub_one]
        exact u256_sub_ne_zero_of_ne hs) (by jump_dest) h
  simp only [safeRuntime_block_2710_taken_stack] at h2781
  have h2826 := safeRuntime_block_2781_taken (by simp; omega) (by decide) (by jump_dest) h2781
  exact safeRuntime_block_2826 (by simp; omega) h2826

end Benchmarks.Safe.ViaIR
