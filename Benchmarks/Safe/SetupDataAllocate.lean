import Benchmarks.Safe.CalldataLengthRounding
import Benchmarks.Safe.CalldataBufferMemory
import Benchmarks.Safe.SetupDecodeScalars
import Benchmarks.Safe.Blocks.Runtime_023

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safeSetupModulesAllocate {I g s0 σ k C aw mem rdata n len ptr} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨4719⟩ (setupDecodedStack I.calldata n len R)
      mem aw rdata σ k C)
    (hb : SetupCalldataBounds I.calldata n len)
    (hf : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr)
    (hp : ptr + 64 + len < UInt256.size) (hov : R.length + 24 ≤ 1024) :
    ∃ aw' k' C', RD safeBytecode I g s0 ⟨8319⟩
      (UInt256.ofNat ptr :: calldataWord I.calldata 68 :: ⟨4782⟩ ::
        setupDecodedStack I.calldata n len R)
      (calldataBufferMemory I.calldata mem (setupDataStart I.calldata) ptr len len
        (ptr + 32 + ABI.paddedSize len)) aw' rdata σ k' C' := by
  have hpad : ABI.paddedSize len ≤ len + 31 := by unfold ABI.paddedSize; omega
  have hsrc : setupDataStart I.calldata < UInt256.size := by
    have hh := lt_of_le_of_lt hb.dataEnd (lt_size_of_lt_sign hb.small)
    omega
  have hend : UInt256.ofNat ptr + (UInt256.ofNat 32 + UInt256.ofNat (ABI.paddedSize len)) =
      UInt256.ofNat (ptr + 32 + ABI.paddedSize len) := by
    rw [wordOfNatAdd _ _ (by omega), wordOfNatAdd _ _ (by omega)]
    rw [Nat.add_assoc]
  have hstart : (UInt256.ofNat 32 + UInt256.ofNat ptr).toNat = ptr + 32 := by
    rw [wordOfNatAdd _ _ (by omega), ulit_toNat' _ (by omega)]
    omega
  have htail : ((UInt256.ofNat 32 + UInt256.ofNat ptr) + UInt256.ofNat len).toNat =
      ptr + 32 + len := by
    rw [uadd_toNat, hstart, ulit_toNat' len (by omega), Nat.mod_eq_of_lt (by omega)]
  obtain ⟨aw', k', C', h₁⟩ := safeRuntime_block_4719_packed (by simp; omega) (by jump_dest) h
  simp only [safeRuntime_block_4719_stack, safeRuntime_block_4719_memory, hf,
    roundedCalldataLength len (by omega), hend, hstart, htail,
    ulit_toNat' ptr (by omega), ulit_toNat' len (by omega),
    ulit_toNat' (setupDataStart I.calldata) hsrc] at h₁
  exact ⟨aw', k', C', h₁⟩

end Benchmarks.Safe
