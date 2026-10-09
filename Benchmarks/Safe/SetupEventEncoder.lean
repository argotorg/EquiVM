import Benchmarks.Safe.SetupEventMemory
import Benchmarks.Safe.AddressCalldataCopy

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safeSetupEventEncodeStart {I g s0 σ k C aw mem rdata ptr n src}
    {fallbackHandler target threshold ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨11525⟩
      (UInt256.ofNat ptr :: fallbackHandler :: target :: threshold :: UInt256.ofNat n ::
        UInt256.ofNat src :: ret :: R) mem aw rdata σ k C)
    (hp : ptr + 160 < UInt256.size) (hov : R.length + 18 ≤ 1024) :
    ∃ aw' k' C', RD safeBytecode I g s0 ⟨11543⟩
      (⟨0⟩ :: UInt256.ofNat (ptr + 160) :: UInt256.ofNat src :: ⟨0⟩ :: UInt256.ofNat ptr ::
        fallbackHandler :: target :: threshold :: UInt256.ofNat n :: UInt256.ofNat src ::
        ret :: R) (setupEventHeader mem ptr n) aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', h₁⟩ := safeRuntime_block_11525_packed (by simp; omega) h
  have h128 : (UInt256.ofNat ptr + UInt256.ofNat 128).toNat = ptr + 128 :=
    uadd_ofNat_toNat (by omega) (by decide) (by omega)
  simp only [safeRuntime_block_11525_stack, safeRuntime_block_11525_memory,
    wordOfNatAdd ptr 160 hp, ulit_toNat' ptr (by omega), h128] at h₁
  exact ⟨aw', k', C', h₁⟩

set_option maxRecDepth 100000 in
theorem safeSetupEventEncode {I g s0 σ k C aw mem rdata ptr n src}
    {fallbackHandler target threshold ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨11525⟩
      (UInt256.ofNat ptr :: fallbackHandler :: target :: threshold :: UInt256.ofNat n ::
        UInt256.ofNat src :: ret :: R) mem aw rdata σ k C)
    (hm : mem.size ≤ ptr) (hn : n < UInt256.size)
    (hp : ptr + 160 + 32 * n < UInt256.size) (hs : src + 32 * n < UInt256.size)
    (hc : ∀ w ∈ calldataWords I.calldata src n, w.toNat < EVM.addressModulus)
    (ht : target.toNat < EVM.addressModulus) (hf : fallbackHandler.toNat < EVM.addressModulus)
    (hov : R.length + 18 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD safeBytecode I g s0 ret
      (UInt256.ofNat (ptr + 160 + 32 * n) :: R)
      (setupEventMemory mem ptr (calldataWords I.calldata src n) threshold target fallbackHandler)
      aw' rdata σ k' C' := by
  obtain ⟨_, _, _, h₁⟩ := safeSetupEventEncodeStart h (by omega) hov
  obtain ⟨_, _, _, h₂⟩ := safeAddressCalldataCopyLoop (i := 0) n h₁ (Nat.zero_add _) hn hs hp
    (setupEventHeader_size mem ptr n hm) hc (by simp; omega)
  obtain ⟨aw', k', C', h₃⟩ := safeRuntime_block_11591_packed (by omega) hret h₂
  have h32 : (UInt256.ofNat ptr + UInt256.ofNat 32).toNat = ptr + 32 :=
    uadd_ofNat_toNat (by omega) (by decide) (by omega)
  have h64 : (UInt256.ofNat ptr + UInt256.ofNat 64).toNat = ptr + 64 :=
    uadd_ofNat_toNat (by omega) (by decide) (by omega)
  have h96 : (UInt256.ofNat ptr + UInt256.ofNat 96).toNat = ptr + 96 :=
    uadd_ofNat_toNat (by omega) (by decide) (by omega)
  simp only [safeRuntime_block_11591_stack, safeRuntime_block_11591_memory,
    safeAddressMask, solcAddrMask_clean_left ht, solcAddrMask_clean_left hf, h32, h64, h96] at h₃
  simpa only [setupEventMemory, calldataWords_length] using
    (show ∃ aw' k' C', RD safeBytecode I g s0 ret
      (UInt256.ofNat (ptr + 160 + 32 * n) :: R)
      (writeWord (writeWord (writeWord
        (setupEventHeader mem ptr n ++ wordBytes (calldataWords I.calldata src n))
        (ptr + 32) threshold) (ptr + 64) target) (ptr + 96) fallbackHandler)
      aw' rdata σ k' C' from ⟨aw', k', C', h₃⟩)

set_option maxRecDepth 100000 in
theorem safeSetupEventEncodeRevert {I g s0 σ k C aw mem rdata ptr n src}
    {fallbackHandler target threshold ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨11525⟩
      (UInt256.ofNat ptr :: fallbackHandler :: target :: threshold :: UInt256.ofNat n ::
        UInt256.ofNat src :: ret :: R) mem aw rdata σ k C)
    (hn : n < UInt256.size) (hp : ptr + 160 + 32 * n < UInt256.size)
    (hs : src + 32 * n < UInt256.size)
    (hc : ¬∀ w ∈ calldataWords I.calldata src n, w.toNat < EVM.addressModulus)
    (hov : R.length + 18 ≤ 1024) : RDrev safeBytecode g s0 := by
  obtain ⟨_, _, _, h₁⟩ := safeSetupEventEncodeStart h (by omega) hov
  exact safeAddressCalldataCopyLoopRevert (i := 0) n h₁ (Nat.zero_add _) hn hs hp hc
    (by simp; omega)

end Benchmarks.Safe
