import Benchmarks.Safe.SetupEventEncoder
import Benchmarks.Safe.SetupAllocatedMemory
import Benchmarks.Safe.SetupDecodeScalars
import Benchmarks.Safe.AddressArrayMemory
import Benchmarks.Safe.Blocks.Runtime_023

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

def setupEventSaved (I : ExecutionEnv) (n len : Nat) (R : List UInt256) : List UInt256 :=
  ⟨9099209990975222275878227567888657751121033986150727063335030356512757686696⟩ ::
    UInt256.land solcAddrMask (UInt256.ofNat I.source.val) ::
      setupDecodedStack I.calldata n len R

set_option maxRecDepth 100000 in
theorem safeSetupEventStart {I g s0 σ k C aw rdata n len} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨4561⟩ (setupDecodedStack I.calldata n len R)
      solcFreePtrMem aw rdata σ k C)
    (hov : R.length + 32 ≤ 1024) :
    ∃ aw' k' C', RD safeBytecode I g s0 ⟨11525⟩
      (⟨128⟩ :: calldataWord I.calldata 132 :: calldataWord I.calldata 68 ::
        calldataWord I.calldata 36 :: UInt256.ofNat n ::
        UInt256.ofNat (setupOwnersStart I.calldata) :: ⟨4626⟩ :: setupEventSaved I n len R)
      solcFreePtrMem aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', h₁⟩ := safeRuntime_block_4561_packed
    (by simp; omega) (by jump_dest) h
  have hf : memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ := solcFreePtrMem_mload64
  simp only [safeRuntime_block_4561_stack, hf, safeAddressMask] at h₁
  exact ⟨aw', k', C', h₁⟩

set_option maxRecDepth 100000 in
theorem safeSetupEventTrace {I g s0 σ k C aw rdata n len} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨4561⟩ (setupDecodedStack I.calldata n len R)
      solcFreePtrMem aw rdata σ k C)
    (hb : SetupCalldataBounds I.calldata n len)
    (hc : ∀ w ∈ calldataWords I.calldata (setupOwnersStart I.calldata) n,
      w.toNat < EVM.addressModulus)
    (hov : R.length + 32 ≤ 1024) :
    ∃ aw' k' C', RD safeBytecode I g s0 ⟨4626⟩
      (UInt256.ofNat (288 + 32 * n) :: setupEventSaved I n len R)
      (setupEventInitialMemory I.calldata n) aw' rdata σ k' C' := by
  have hu : UInt256.size = 2 ^ 256 := rfl
  have hn := hb.ownersLength
  obtain ⟨_, _, _, h₁⟩ := safeSetupEventStart h hov
  exact safeSetupEventEncode h₁ (by rw [solcFreePtrMem_size]; decide) (by omega)
    (by omega) (lt_of_le_of_lt hb.ownersEnd (lt_size_of_lt_sign hb.small)) hc
    hb.target hb.fallbackHandler (by simp [setupEventSaved, setupDecodedStack]; omega)
    (by jump_dest)

set_option maxRecDepth 100000 in
theorem safeSetupEventTraceRevert {I g s0 σ k C aw rdata n len} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨4561⟩ (setupDecodedStack I.calldata n len R)
      solcFreePtrMem aw rdata σ k C)
    (hb : SetupCalldataBounds I.calldata n len)
    (hc : ¬∀ w ∈ calldataWords I.calldata (setupOwnersStart I.calldata) n,
      w.toNat < EVM.addressModulus)
    (hov : R.length + 32 ≤ 1024) : RDrev safeBytecode g s0 := by
  have hu : UInt256.size = 2 ^ 256 := rfl
  have hn := hb.ownersLength
  obtain ⟨_, _, _, h₁⟩ := safeSetupEventStart h hov
  exact safeSetupEventEncodeRevert (ptr := 128) h₁ (by omega) (by omega)
    (lt_of_le_of_lt hb.ownersEnd (lt_size_of_lt_sign hb.small)) hc
    (by simp [setupEventSaved, setupDecodedStack]; omega)

set_option maxRecDepth 100000 in
theorem safeSetupEventStatic {I g s0 σ k C aw mem rdata finish topic sender}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨4626⟩ (finish :: topic :: sender :: R) mem aw rdata σ k C)
    (hp : I.perm = false) (hov : R.length + 6 ≤ 1024) : RDstatic safeBytecode g s0 := by
  have h₁ := evm_run h with [jumpdest, push1 ⟨64⟩, genMload, dup1, swap2, sub, swap1]
  exact RD.log2Static h₁ hp (by native_decide) (by omega)

set_option maxRecDepth 100000 in
theorem safeSetupOwnersAllocate {I g s0 σ k C aw rdata n len} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨4626⟩
      (UInt256.ofNat (288 + 32 * n) :: setupEventSaved I n len R)
      (setupEventInitialMemory I.calldata n) aw rdata σ k C)
    (hb : SetupCalldataBounds I.calldata n len)
    (hp : I.perm = true) (hov : R.length + 32 ≤ 1024) :
    ∃ aw' k' C', RD safeBytecode I g s0 ⟨7975⟩
      (calldataWord I.calldata 36 :: ⟨128⟩ :: ⟨4695⟩ :: setupDecodedStack I.calldata n len R)
      (setupOwnersAllocatedMemory I.calldata n) aw' rdata σ k' C' := by
  have hu : UInt256.size = 2 ^ 256 := rfl
  have hn := hb.ownersLength
  have hs : setupOwnersStart I.calldata < UInt256.size :=
    lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ _) hb.ownersEnd)
      (lt_size_of_lt_sign hb.small)
  have hmul : (UInt256.mul (UInt256.ofNat 32) (UInt256.ofNat n)).toNat = 32 * n := by
    change (32 * (UInt256.ofNat n).toNat) % UInt256.size = _
    rw [ulit_toNat' n (by omega), Nat.mod_eq_of_lt (by omega)]
  have hend : ((UInt256.ofNat 32 + (⟨128⟩ : UInt256)) +
      UInt256.mul (UInt256.ofNat 32) (UInt256.ofNat n)).toNat = 160 + 32 * n := by
    rw [uadd_toNat, hmul]
    change (160 + 32 * n) % UInt256.size = _
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨aw', k', C', h₁⟩ := safeRuntime_block_4626_packed (by simp; omega) hp (by jump_dest) h
  have hf : memLoad (UInt256.ofNat 64) (setupEventInitialMemory I.calldata n) = ⟨128⟩ :=
    setupEventInitialMemory_free _ _
  simp only [safeRuntime_block_4626_stack, safeRuntime_block_4626_memory,
    hf, addressArrayFreePtr_eq n hn,
    ulit_toNat' (setupOwnersStart I.calldata) hs, hmul, hend] at h₁
  exact ⟨aw', k', C', h₁⟩

end Benchmarks.Safe
