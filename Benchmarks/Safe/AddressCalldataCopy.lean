import Benchmarks.Safe.AddressCalldataCopyStep

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safeAddressCalldataCopyLoop (count : Nat)
    {I g s0 σ k C aw mem rdata i n src dst}
    {scratch base fallbackHandler target threshold : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨11543⟩
      (UInt256.ofNat i :: UInt256.ofNat dst :: UInt256.ofNat src :: scratch :: base ::
        fallbackHandler :: target :: threshold :: UInt256.ofNat n :: R) mem aw rdata σ k C)
    (hi : i + count = n) (hn : n < UInt256.size)
    (hsrc : src + 32 * count < UInt256.size) (hdst : dst + 32 * count < UInt256.size)
    (hm : mem.size = dst)
    (hc : ∀ w ∈ calldataWords I.calldata src count, w.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ aw' k' C', RD safeBytecode I g s0 ⟨11591⟩
      (UInt256.ofNat n :: UInt256.ofNat (dst + 32 * count) ::
        UInt256.ofNat (src + 32 * count) :: scratch :: base :: fallbackHandler :: target ::
        threshold :: UInt256.ofNat n :: R)
      (mem ++ wordBytes (calldataWords I.calldata src count)) aw' rdata σ k' C' := by
  induction count generalizing i src dst mem aw k C with
  | zero =>
      have he : i = n := by omega
      subst i
      have h₁ := safeRuntime_block_11543_taken (by omega)
        (by rw [ult_zero (Nat.le_refl _)]; decide) (by jump_dest) h
      simpa only [Nat.mul_zero, Nat.add_zero, calldataWords, wordBytes, ByteArray.append_empty]
        using (show ∃ aw' k' C', RD safeBytecode I g s0 ⟨11591⟩
          (UInt256.ofNat n :: UInt256.ofNat dst :: UInt256.ofNat src :: scratch :: base ::
            fallbackHandler :: target :: threshold :: UInt256.ofNat n :: R)
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

set_option maxRecDepth 100000 in
theorem safeAddressCalldataCopyLoopRevert (count : Nat)
    {I g s0 σ k C aw mem rdata i n src dst}
    {scratch base fallbackHandler target threshold : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨11543⟩
      (UInt256.ofNat i :: UInt256.ofNat dst :: UInt256.ofNat src :: scratch :: base ::
        fallbackHandler :: target :: threshold :: UInt256.ofNat n :: R) mem aw rdata σ k C)
    (hi : i + count = n) (hn : n < UInt256.size)
    (hsrc : src + 32 * count < UInt256.size) (hdst : dst + 32 * count < UInt256.size)
    (hc : ¬∀ w ∈ calldataWords I.calldata src count, w.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) : RDrev safeBytecode g s0 := by
  induction count generalizing i src dst mem aw k C with
  | zero => exact (hc (by simp [calldataWords])).elim
  | succ count ih =>
      by_cases hh : (calldataWord I.calldata src).toNat < EVM.addressModulus
      · obtain ⟨aw', k', C', h₁⟩ := safeAddressCalldataCopyStep h (by omega) hn
          (by omega) (by omega) hh hov
        exact ih h₁ (by omega) (by omega) (by omega)
          (fun ht ↦ hc (by simpa [calldataWords, hh] using ht))
      · exact safeAddressCalldataCopyStepRevert h (by omega) hn (by omega) hh hov

end Benchmarks.Safe
