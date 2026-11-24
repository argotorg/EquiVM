import Benchmarks.Safe.ViaIR.AddressCalldataCopyStep
import Benchmarks.Safe.ViaIR.WordWrites

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000 in
theorem safeAddressCalldataCopyLoop (count : Nat)
    {I g s0 σ k C aw mem rdata i n src dst}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3187⟩
      (UInt256.ofNat i :: UInt256.ofNat n :: UInt256.ofNat src :: UInt256.ofNat dst :: R)
      mem aw rdata σ k C)
    (hi : i + count = n) (hn : n < UInt256.size)
    (hsrc : src + 32 * count < UInt256.size) (hdst : dst + 32 * count < UInt256.size)
    (hm : mem.size = dst)
    (hc : ∀ w ∈ calldataWords I.calldata src count, w.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨3195⟩
      (UInt256.ofNat n :: UInt256.ofNat n :: UInt256.ofNat (src + 32 * count) ::
        UInt256.ofNat (dst + 32 * count) :: R)
      (mem ++ wordBytes (calldataWords I.calldata src count)) aw' rdata σ k' C' := by
  induction count generalizing i src dst mem aw k C with
  | zero =>
      have he : i = n := by omega
      subst i
      have h₁ := safeRuntime_block_3187_fallthrough (by simp; omega)
        (ult_zero (Nat.le_refl _)) h
      simpa only [Nat.mul_zero, Nat.add_zero, calldataWords, wordBytes, ByteArray.append_empty]
        using (show ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨3195⟩
          (UInt256.ofNat n :: UInt256.ofNat n :: UInt256.ofNat src :: UInt256.ofNat dst :: R)
          mem aw' rdata σ k' C' from ⟨_, _, _, h₁⟩)
  | succ count ih =>
      have hh : (calldataWord I.calldata src).toNat < EVM.addressModulus :=
        hc _ (by simp [calldataWords])
      obtain ⟨aw', k', C', h₁⟩ := safeAddressCalldataCopyStep h (by omega) hn
        (by omega) (by omega) hh hov
      have hm' : (writeWord mem dst (calldataWord I.calldata src)).size = dst + 32 := by
        rw [writeWord_sparse_size, hm, Nat.max_eq_right (by omega)]
      obtain ⟨aw'', k'', C'', h₂⟩ := ih h₁ (by omega) (by omega) (by omega) hm'
        (fun w hw ↦ hc w (by simp [calldataWords, hw]))
      have hd : dst + 32 + 32 * count = dst + 32 * (count + 1) := by omega
      have hs : src + 32 + 32 * count = src + 32 * (count + 1) := by omega
      rw [hd, hs] at h₂
      have hw : writeWord mem dst (calldataWord I.calldata src) =
          mem ++ (calldataWord I.calldata src).toByteArray := writeWordAtEnd mem _ hm
      rw [hw, ByteArray.append_assoc] at h₂
      exact ⟨aw'', k'', C'', h₂⟩

set_option maxRecDepth 2000 in
theorem safeAddressCalldataCopyLoopRevert (count : Nat)
    {I g s0 σ k C aw mem rdata i n src dst}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3187⟩
      (UInt256.ofNat i :: UInt256.ofNat n :: UInt256.ofNat src :: UInt256.ofNat dst :: R)
      mem aw rdata σ k C)
    (hi : i + count = n) (hn : n < UInt256.size)
    (hsrc : src + 32 * count < UInt256.size) (hdst : dst + 32 * count < UInt256.size)
    (hc : ¬∀ w ∈ calldataWords I.calldata src count, w.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  induction count generalizing i src dst mem aw k C with
  | zero => exact (hc (by simp [calldataWords])).elim
  | succ count ih =>
      by_cases hh : (calldataWord I.calldata src).toNat < EVM.addressModulus
      · obtain ⟨aw', k', C', h₁⟩ := safeAddressCalldataCopyStep h (by omega) hn
          (by omega) (by omega) hh hov
        exact ih h₁ (by omega) (by omega) (by omega)
          (fun ht ↦ hc (by simpa [calldataWords, hh] using ht))
      · exact safeAddressCalldataCopyStepRevert h (by omega) hn (by omega) hh hov

set_option maxRecDepth 2000 in
theorem safeSetupOwnersCopyLoop (count : Nat)
    {I g s0 σ k C aw mem rdata src dst finish} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3294⟩
      (UInt256.ofNat dst :: UInt256.ofNat src :: UInt256.ofNat finish :: R)
      mem aw rdata σ k C)
    (hi : src + 32 * count = finish) (hs : finish < UInt256.size)
    (hd : dst + 32 * count < UInt256.size)
    (hc : ∀ w ∈ calldataWords I.calldata src count, w.toNat < EVM.addressModulus)
    (hov : R.length + 14 ≤ 1024) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨3302⟩
      (UInt256.ofNat (dst + 32 * count) :: UInt256.ofNat finish ::
        UInt256.ofNat finish :: R)
      (writeWords mem dst (calldataWords I.calldata src count)) aw' rdata σ k' C' := by
  induction count generalizing src dst mem aw k C with
  | zero =>
      have he : src = finish := by omega
      subst src
      have h₁ := safeRuntime_block_3294_fallthrough (by omega) (ult_zero (Nat.le_refl _)) h
      simpa only [Nat.mul_zero, Nat.add_zero, calldataWords, writeWords] using
        (show ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨3302⟩
          (UInt256.ofNat dst :: UInt256.ofNat finish :: UInt256.ofNat finish :: R)
          mem aw' rdata σ k' C' from ⟨_, _, _, h₁⟩)
  | succ count ih =>
      have h₁ := safeRuntime_block_3294_taken (by omega) (by
        rw [ult_one (by rw [ulit_toNat' _ (by omega), ulit_toNat' _ hs]; omega)]
        decide) (by jump_dest) h
      have h₂ := safeRuntime_block_3835 (by simp; omega) (by jump_dest) h₁
      have hsrc : (UInt256.ofNat src).toNat = src := ulit_toNat' _ (by omega)
      obtain ⟨_, _, h₃⟩ := safeReadCalldataAddress h₂ (by
        rw [hsrc]; exact hc _ (by simp [calldataWords])) (by simp; omega) (by jump_dest)
      obtain ⟨_, _, _, h₄⟩ := safeRuntime_block_3848_packed
        (by simp; omega) (by jump_dest) h₃
      simp only [safeRuntime_block_3848_stack, safeRuntime_block_3848_memory, hsrc,
        wordOfNatAdd dst 32 (by omega), wordOfNatAdd src 32 (by omega),
        ulit_toNat' dst (by omega)] at h₄
      obtain ⟨aw', k', C', h₅⟩ := ih h₄ (by omega) (by omega)
        (fun w hw ↦ hc w (by simp [calldataWords, hw]))
      have hd' : dst + 32 + 32 * count = dst + 32 * (count + 1) := by omega
      rw [hd'] at h₅
      exact ⟨aw', k', C', h₅⟩

end Benchmarks.Safe.ViaIR
