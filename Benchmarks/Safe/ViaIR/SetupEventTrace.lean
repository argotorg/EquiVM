import Benchmarks.Safe.ViaIR.SetupEventEncoder
import Benchmarks.Safe.ViaIR.SetupAllocatedMemory
import Benchmarks.Safe.ViaIR.AddressArrayMemory
import Benchmarks.Safe.ViaIR.GetOwnersAllocation
import Benchmarks.Safe.ViaIR.IRMemoryAllocation

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

def setupEventArrayMemory (cd : ByteArray) (n : Nat) : ByteArray :=
  setupEventHeader solcFreePtrMem 128 n ++ wordBytes (calldataWords cd (setupOwnersStart cd) n)

def setupOwnersSaved (cd : ByteArray) (len : Nat) (R : List UInt256) : List UInt256 :=
  [calldataWord cd 36, calldataWord cd 132, calldataWord cd 132, UInt256.ofNat len,
    UInt256.ofNat (setupDataStart cd), calldataWord cd 68, calldataWord cd 68,
    calldataWord cd 164, calldataWord cd 228, calldataWord cd 196, ⟨128⟩, ⟨0⟩] ++ R

set_option maxRecDepth 2000
set_option maxHeartbeats 800000

theorem safeSetupEventStart {I g s0 σ k C aw rdata n len} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3163⟩ (setupDecodedStack I.calldata n len R)
      solcFreePtrMem aw rdata σ k C)
    (hov : R.length + 32 ≤ 1024) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨3187⟩
      (⟨0⟩ :: UInt256.ofNat n :: UInt256.ofNat (setupOwnersStart I.calldata) ::
        ⟨288⟩ :: setupEventSaved I n len 128 R)
      (setupEventHeader solcFreePtrMem 128 n) aw' rdata σ k' C' :=
  safeSetupEventEncodeStart h solcFreePtrMem_mload64 (by decide) hov

theorem safeSetupEventTrace {I g s0 σ k C aw rdata n len} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3163⟩ (setupDecodedStack I.calldata n len R)
      solcFreePtrMem aw rdata σ k C)
    (hb : SetupCalldataBounds I.calldata n len)
    (hc : ∀ w ∈ calldataWords I.calldata (setupOwnersStart I.calldata) n,
      w.toNat < EVM.addressModulus)
    (hov : R.length + 32 ≤ 1024) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨3195⟩
      (UInt256.ofNat n :: UInt256.ofNat n ::
        UInt256.ofNat (setupOwnersStart I.calldata + 32 * n) ::
        UInt256.ofNat (288 + 32 * n) :: setupEventSaved I n len 128 R)
      (setupEventArrayMemory I.calldata n) aw' rdata σ k' C' := by
  have hu : UInt256.size = 2 ^ 256 := rfl
  have hn := hb.ownersLength
  exact safeSetupEventEncode h solcFreePtrMem_mload64
    (by rw [solcFreePtrMem_size]; decide) (by omega) (by omega)
    (lt_of_le_of_lt hb.ownersEnd (lt_size_of_lt_sign hb.small)) hc hov

theorem safeSetupEventTraceRevert {I g s0 σ k C aw rdata n len} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3163⟩ (setupDecodedStack I.calldata n len R)
      solcFreePtrMem aw rdata σ k C)
    (hb : SetupCalldataBounds I.calldata n len)
    (hc : ¬∀ w ∈ calldataWords I.calldata (setupOwnersStart I.calldata) n,
      w.toNat < EVM.addressModulus)
    (hov : R.length + 32 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have hu : UInt256.size = 2 ^ 256 := rfl
  have hn := hb.ownersLength
  exact safeSetupEventEncodeRevert (ptr := 128) h solcFreePtrMem_mload64 (by omega) (by omega)
    (lt_of_le_of_lt hb.ownersEnd (lt_size_of_lt_sign hb.small)) hc hov

theorem safeSetupEventStatic {I g s0 σ k C aw mem rdata n len} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3195⟩
      (UInt256.ofNat n :: UInt256.ofNat n ::
        UInt256.ofNat (setupOwnersStart I.calldata + 32 * n) ::
        UInt256.ofNat (288 + 32 * n) :: setupEventSaved I n len 128 R)
      mem aw rdata σ k C)
    (hp : I.perm = false) (hov : R.length + 32 ≤ 1024) : RDstatic fork safeBytecode g s0 := by
  simp only [setupEventSaved, List.cons_append, List.nil_append] at h
  have h₁ := evm_run h with [pop, pop, pop, dup4, push1 ⟨32⟩, dup12, add, genMstore]
  have h₂ := h₁.pushConst
    (UInt256.ofNat 9099209990975222275878227567888657751121033986150727063335030356512757686696)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by simp; omega)
  have h₃ := evm_run h₂ with [push1 ⟨1⟩, dup1, push1 ⟨160⟩, shl, sub, dup11, and,
    swap11, dup12, push1 ⟨64⟩, dup3, add, genMstore, dup7, push1 ⟨96⟩, dup3,
    add, genMstore, dup1, caller, swap4, sub, swap1]
  exact RD.log2Static h₃ hp (by native_decide) (by simp; omega)

theorem safeSetupOwnersAllocateStart {I g s0 σ k C aw rdata n len} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3195⟩
      (UInt256.ofNat n :: UInt256.ofNat n ::
        UInt256.ofNat (setupOwnersStart I.calldata + 32 * n) ::
        UInt256.ofNat (288 + 32 * n) :: setupEventSaved I n len 128 R)
      (setupEventArrayMemory I.calldata n) aw rdata σ k C)
    (hb : SetupCalldataBounds I.calldata n len)
    (hp : I.perm = true) (hov : R.length + 32 ≤ 1024) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨7128⟩
      (⟨128⟩ :: UInt256.ofNat (32 + 32 * n) :: ⟨3287⟩ :: UInt256.ofNat n ::
        UInt256.ofNat (setupOwnersStart I.calldata) ::
        UInt256.ofNat (setupOwnersStart I.calldata + 32 * n) ::
        setupOwnersSaved I.calldata len R)
      (setupEventInitialMemory I.calldata n) aw' rdata σ k' C' := by
  have hu : UInt256.size = 2 ^ 256 := rfl
  have hn := hb.ownersLength
  have hnword : (UInt256.ofNat n).toNat = n := ulit_toNat' _ (by omega)
  obtain ⟨_, _, _, h₁⟩ := safeRuntime_block_3195_packed (by simp; omega) hp (by jump_dest) h
  simp only [safeRuntime_block_3195_stack, safeRuntime_block_3195_memory, safeAddressMask] at h₁
  change RD fork safeBytecode I g s0 ⟨8927⟩
    (UInt256.ofNat n :: ⟨3273⟩ :: UInt256.ofNat (setupOwnersStart I.calldata) ::
      UInt256.ofNat (setupOwnersStart I.calldata + 32 * n) :: calldataWord I.calldata 36 ::
      calldataWord I.calldata 132 :: calldataWord I.calldata 132 :: UInt256.ofNat len ::
      UInt256.ofNat (setupDataStart I.calldata) :: calldataWord I.calldata 68 ::
      UInt256.land (calldataWord I.calldata 68) solcAddrMask :: calldataWord I.calldata 164 ::
      calldataWord I.calldata 228 :: calldataWord I.calldata 196 :: UInt256.ofNat n :: ⟨0⟩ :: R)
    (writeWord (writeWord (writeWord (setupEventArrayMemory I.calldata n) 160
      (calldataWord I.calldata 36)) 192 (UInt256.land (calldataWord I.calldata 68) solcAddrMask))
      224 (calldataWord I.calldata 132)) _ rdata σ _ _ at h₁
  rw [solcAddrMask_clean hb.target] at h₁
  have hm : writeWord (writeWord (writeWord (setupEventArrayMemory I.calldata n) 160
      (calldataWord I.calldata 36)) 192 (calldataWord I.calldata 68))
      224 (calldataWord I.calldata 132) = setupEventInitialMemory I.calldata n := by
    simp only [setupEventInitialMemory, setupEventMemory, calldataWords_length,
      setupEventArrayMemory]
  rw [hm] at h₁
  obtain ⟨_, _, h₂⟩ := safeGetOwnersCountCheck h₁ (by simp; omega)
    (by rwa [hnword]) (by jump_dest)
  have hlen : UInt256.ofNat 32 + UInt256.shiftLeft (UInt256.ofNat n) (UInt256.ofNat 5) =
      UInt256.ofNat (32 + 32 * n) := by
    have hshift : UInt256.shiftLeft (UInt256.ofNat n) (UInt256.ofNat 5) =
        UInt256.ofNat (32 * n) := shiftLeft5_ofNat_eq (by omega)
    rw [hshift, wordOfNatAdd _ _ (by omega)]
  rw [hlen] at h₂
  obtain ⟨aw', k', C', h₃⟩ := safeRuntime_block_3273_packed (by simp; omega) (by jump_dest) h₂
  simp only [safeRuntime_block_3273_stack,
    show memLoad (UInt256.ofNat 64) (setupEventInitialMemory I.calldata n) = ⟨128⟩ from
      setupEventInitialMemory_free _ _] at h₃
  exact ⟨aw', k', C', h₃⟩

theorem safeSetupOwnersAllocate {I g s0 σ k C aw rdata n len} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3195⟩
      (UInt256.ofNat n :: UInt256.ofNat n ::
        UInt256.ofNat (setupOwnersStart I.calldata + 32 * n) ::
        UInt256.ofNat (288 + 32 * n) :: setupEventSaved I n len 128 R)
      (setupEventArrayMemory I.calldata n) aw rdata σ k C)
    (hb : SetupCalldataBounds I.calldata n len)
    (hc : ∀ w ∈ calldataWords I.calldata (setupOwnersStart I.calldata) n,
      w.toNat < EVM.addressModulus)
    (ha : 160 + 32 * n < 2 ^ 64)
    (hp : I.perm = true) (hov : R.length + 32 ≤ 1024) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨3302⟩
      (UInt256.ofNat (160 + 32 * n) ::
        UInt256.ofNat (setupOwnersStart I.calldata + 32 * n) ::
        UInt256.ofNat (setupOwnersStart I.calldata + 32 * n) ::
        setupOwnersSaved I.calldata len R)
      (setupOwnersAllocatedMemory I.calldata n) aw' rdata σ k' C' := by
  have hu : UInt256.size = 2 ^ 256 := rfl
  have he : 128 + ABI.paddedSize (32 + 32 * n) = 160 + 32 * n := by
    unfold ABI.paddedSize; omega
  obtain ⟨_, _, _, h₁⟩ := safeSetupOwnersAllocateStart h hb hp hov
  obtain ⟨_, _, _, h₂⟩ := safeIRAllocateValidTrace h₁ (by omega) (by rwa [he])
    (by simp [setupOwnersSaved]; omega) (by jump_dest)
  rw [he] at h₂
  obtain ⟨_, _, _, h₃⟩ := safeRuntime_block_3287_packed (by simp; omega) h₂
  change RD fork safeBytecode I g s0 ⟨3294⟩
    (UInt256.ofNat 160 :: UInt256.ofNat (setupOwnersStart I.calldata) ::
      UInt256.ofNat (setupOwnersStart I.calldata + 32 * n) :: setupOwnersSaved I.calldata len R)
    (calldataBufferHeader (setupEventInitialMemory I.calldata n) 128 n (160 + 32 * n))
    _ rdata σ _ _ at h₃
  exact safeSetupOwnersCopyLoop n h₃ rfl
    (lt_of_le_of_lt hb.ownersEnd (lt_size_of_lt_sign hb.small)) (by omega) hc
    (by simp [setupOwnersSaved]; omega)

theorem safeSetupOwnersAllocateRevert {I g s0 σ k C aw rdata n len} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3195⟩
      (UInt256.ofNat n :: UInt256.ofNat n ::
        UInt256.ofNat (setupOwnersStart I.calldata + 32 * n) ::
        UInt256.ofNat (288 + 32 * n) :: setupEventSaved I n len 128 R)
      (setupEventArrayMemory I.calldata n) aw rdata σ k C)
    (hb : SetupCalldataBounds I.calldata n len)
    (ha : ¬160 + 32 * n < 2 ^ 64)
    (hp : I.perm = true) (hov : R.length + 32 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have hu : UInt256.size = 2 ^ 256 := rfl
  have hn := hb.ownersLength
  have he : 128 + ABI.paddedSize (32 + 32 * n) = 160 + 32 * n := by
    unfold ABI.paddedSize; omega
  obtain ⟨_, _, _, h₁⟩ := safeSetupOwnersAllocateStart h hb hp hov
  obtain hr | ⟨_, _, _, hfit, _⟩ := safeIRAllocateTrace h₁ (by omega)
    (by rw [he]; omega) (by simp [setupOwnersSaved]; omega) (by jump_dest)
  · exact hr
  · exact (ha (by rwa [he] at hfit)).elim

end Benchmarks.Safe.ViaIR
