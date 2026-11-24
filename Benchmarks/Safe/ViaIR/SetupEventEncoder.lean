import Benchmarks.Safe.ViaIR.SetupEventMemory
import Benchmarks.Safe.ViaIR.AddressCalldataCopy
import Benchmarks.Safe.ViaIR.SetupDecodeScalars

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

def setupEventSaved (I : ExecutionEnv) (n len ptr : Nat) (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat (setupOwnersStart I.calldata),
    UInt256.ofNat (setupOwnersStart I.calldata + 32 * n), calldataWord I.calldata 36,
    calldataWord I.calldata 132, calldataWord I.calldata 132, UInt256.ofNat len,
    UInt256.ofNat (setupDataStart I.calldata), calldataWord I.calldata 68,
    UInt256.ofNat ptr, calldataWord I.calldata 164, calldataWord I.calldata 228,
    calldataWord I.calldata 196, UInt256.ofNat n, ⟨0⟩] ++ R

set_option maxRecDepth 2000
set_option maxHeartbeats 800000

theorem safeSetupEventEncodeStart {I g s0 σ k C aw mem rdata ptr n len}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3163⟩ (setupDecodedStack I.calldata n len R)
      mem aw rdata σ k C)
    (hf : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr)
    (hp : ptr + 160 < UInt256.size) (hov : R.length + 32 ≤ 1024) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨3187⟩
      (⟨0⟩ :: UInt256.ofNat n :: UInt256.ofNat (setupOwnersStart I.calldata) ::
        UInt256.ofNat (ptr + 160) :: setupEventSaved I n len ptr R)
      (setupEventHeader mem ptr n) aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', h₁⟩ := safeRuntime_block_3163_packed (by simp; omega) h
  have h128 : (UInt256.ofNat ptr + UInt256.ofNat 128).toNat = ptr + 128 :=
    uadd_ofNat_toNat (by omega) (by decide) (by omega)
  simp only [safeRuntime_block_3163_stack, safeRuntime_block_3163_memory, hf,
    wordOfNatAdd ptr 160 hp, ulit_toNat' ptr (by omega), h128] at h₁
  exact ⟨aw', k', C', h₁⟩

theorem safeSetupEventEncode {I g s0 σ k C aw mem rdata ptr n len}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3163⟩ (setupDecodedStack I.calldata n len R)
      mem aw rdata σ k C)
    (hf : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr)
    (hm : mem.size ≤ ptr) (hn : n < UInt256.size)
    (hp : ptr + 160 + 32 * n < UInt256.size)
    (hs : setupOwnersStart I.calldata + 32 * n < UInt256.size)
    (hc : ∀ w ∈ calldataWords I.calldata (setupOwnersStart I.calldata) n,
      w.toNat < EVM.addressModulus)
    (hov : R.length + 32 ≤ 1024) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨3195⟩
      (UInt256.ofNat n :: UInt256.ofNat n ::
        UInt256.ofNat (setupOwnersStart I.calldata + 32 * n) ::
        UInt256.ofNat (ptr + 160 + 32 * n) :: setupEventSaved I n len ptr R)
      (setupEventHeader mem ptr n ++
        wordBytes (calldataWords I.calldata (setupOwnersStart I.calldata) n))
      aw' rdata σ k' C' := by
  obtain ⟨_, _, _, h₁⟩ := safeSetupEventEncodeStart h hf (by omega) hov
  exact safeAddressCalldataCopyLoop (i := 0) n h₁ (Nat.zero_add _) hn hs hp
    (setupEventHeader_size mem ptr n hm) hc (by simp [setupEventSaved]; omega)

theorem safeSetupEventEncodeRevert {I g s0 σ k C aw mem rdata ptr n len}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3163⟩ (setupDecodedStack I.calldata n len R)
      mem aw rdata σ k C)
    (hf : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr)
    (hn : n < UInt256.size) (hp : ptr + 160 + 32 * n < UInt256.size)
    (hs : setupOwnersStart I.calldata + 32 * n < UInt256.size)
    (hc : ¬∀ w ∈ calldataWords I.calldata (setupOwnersStart I.calldata) n,
      w.toNat < EVM.addressModulus)
    (hov : R.length + 32 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  obtain ⟨_, _, _, h₁⟩ := safeSetupEventEncodeStart h hf (by omega) hov
  exact safeAddressCalldataCopyLoopRevert (i := 0) n h₁ (Nat.zero_add _) hn hs hp hc
    (by simp [setupEventSaved]; omega)

end Benchmarks.Safe.ViaIR
