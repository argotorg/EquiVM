import Benchmarks.Safe.ViaIR.SetupModulesSource
import Benchmarks.Safe.ViaIR.SetupOwnersStore
import Benchmarks.Safe.ViaIR.Blocks.Runtime_017

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

def setupModulesMemory (mem : ByteArray) : ByteArray :=
  twoWordHashMem ⟨1⟩ ⟨1⟩ (twoWordHashMem ⟨1⟩ ⟨1⟩ mem)

theorem setupModulesMemory_size (mem : ByteArray) (hm : 64 ≤ mem.size) :
    (setupModulesMemory mem).size = mem.size := by
  rw [setupModulesMemory, twoWordHashMem_size_of_ge64 _ _ (by
      rw [twoWordHashMem_size_of_ge64 _ _ hm]; exact hm),
    twoWordHashMem_size_of_ge64 _ _ hm]

theorem setupModulesMemory_read (mem : ByteArray) (off count : Nat)
    (hin : off + count ≤ mem.size) (hlo : 64 ≤ off) :
    (setupModulesMemory mem).readWithPadding off count = mem.readWithPadding off count := by
  have hm : 64 ≤ mem.size := by omega
  rw [setupModulesMemory, twoWordHashRead _ _ _ _ _ (by
      rw [twoWordHashMem_size_of_ge64 _ _ hm]; exact hin) hlo,
    twoWordHashRead _ _ _ _ _ hin hlo]

def setupModulesAccounts (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (mapSlot ⟨1⟩ ⟨1⟩)
    (setAddressOffset0Word (solcSlotWordAt (mapSlot ⟨1⟩ ⟨1⟩) σ I) ⟨1⟩)

theorem setupModulesState_accounts (p : SetupModulesInput) (evm : EVM.State) :
    (p.state evm).accountMap = setupModulesAccounts evm.accountMap evm.executionEnv := by
  simp only [SetupModulesInput.state, writeModuleLink, setupModulesAccounts,
    storageStore_accountMap, storageLoad_eq_solcSlotWord]
  rfl

set_option maxRecDepth 2000 in
theorem safeSetupModulesInitStore (p : SetupModulesInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata} {ptr token receiver payment : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3439⟩
      (p.target :: p.target :: ptr :: token :: receiver :: payment :: ⟨0⟩ :: R)
      mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ)
    (hperm : I.perm = true) (hov : R.length + 12 ≤ 1024) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 (if p.target = ⟨0⟩ then ⟨3475⟩ else ⟨3503⟩)
      (p.target :: ptr :: token :: receiver :: payment :: ⟨0⟩ :: R)
      (twoWordHashMem ⟨1⟩ ⟨1⟩ mem) aw' rdata (p.state evm).accountMap k' C' := by
  have hh := twoWordHashMemMapSlotAny ⟨1⟩ ⟨1⟩ mem
  change keccakWord ⟨0⟩ (UInt256.ofNat 64)
    ((UInt256.ofNat 1).toByteArray.write 0
      ((UInt256.ofNat 1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)
      (UInt256.ofNat 32).toNat 32) = _ at hh
  have hw (word : UInt256) : UInt256.lor (UInt256.land word (UInt256.lnot solcAddrMask))
      (UInt256.ofNat 1) = setAddressOffset0Word word ⟨1⟩ := by
    rw [setAddressOffset0Word]
    congr 1
  have ha : setupModulesAccounts σ I = (p.state evm).accountMap := by
    rw [setupModulesState_accounts, hee, hacc]
  by_cases hz : p.target = ⟨0⟩
  · obtain ⟨aw', k', C', h'⟩ := safeRuntime_block_3439_fallthrough_packed hov hperm hz h
    simp only [safeRuntime_block_3439_fallthrough_stack, safeRuntime_block_3439_fallthrough_memory,
      safeAddressHighMask, hh, hw] at h'
    change RD fork safeBytecode I g s0 ⟨3475⟩
      (p.target :: ptr :: token :: receiver :: payment :: ⟨0⟩ :: R)
      (twoWordHashMem ⟨1⟩ ⟨1⟩ mem) aw' rdata (setupModulesAccounts σ I) k' C' at h'
    rw [ha] at h'
    exact ⟨aw', k', C', by simpa only [if_pos hz] using h'⟩
  · obtain ⟨aw', k', C', h'⟩ := safeRuntime_block_3439_taken_packed hov hperm hz
      (by jump_dest) h
    simp only [safeRuntime_block_3439_taken_stack, safeRuntime_block_3439_taken_memory,
      safeAddressHighMask, hh, hw] at h'
    change RD fork safeBytecode I g s0 ⟨3503⟩
      (p.target :: ptr :: token :: receiver :: payment :: ⟨0⟩ :: R)
      (twoWordHashMem ⟨1⟩ ⟨1⟩ mem) aw' rdata (setupModulesAccounts σ I) k' C' at h'
    rw [ha] at h'
    exact ⟨aw', k', C', by simpa only [if_neg hz] using h'⟩

set_option maxRecDepth 2000 in
theorem safeSetupModulesPrepare (p : SetupModulesInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata} {ptr token receiver payment : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3409⟩
      (ptr :: p.target :: p.target :: token :: receiver :: payment :: ⟨0⟩ :: R)
      mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ)
    (hperm : I.perm = true) (hov : R.length + 12 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧
      ExecFuncBody fork config p.frame evm setupModulesFunction.body .reverted) ∨
    ∃ aw' k' C', moduleLink evm ⟨1⟩ = ⟨0⟩ ∧
      RD fork safeBytecode I g s0 (if p.target = ⟨0⟩ then ⟨3475⟩ else ⟨3503⟩)
        (p.target :: ptr :: token :: receiver :: payment :: ⟨0⟩ :: R)
        (setupModulesMemory mem) aw' rdata (p.state evm).accountMap k' C' := by
  have hs : moduleLinkAt σ I ⟨1⟩ = moduleLink evm ⟨1⟩ := by
    rw [moduleLink_eq_at, hee, hacc]
  have hh := twoWordHashMemMapSlotAny ⟨1⟩ ⟨1⟩ mem
  change keccakWord ⟨0⟩ (UInt256.ofNat 64)
    ((UInt256.ofNat 1).toByteArray.write 0
      ((UInt256.ofNat 1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)
      (UInt256.ofNat 32).toNat 32) = _ at hh
  by_cases he : moduleLink evm ⟨1⟩ = ⟨0⟩
  · obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeRuntime_block_3409_fallthrough_packed (by omega)
      (by
        rw [safeAddressMask, hh, u256_land_comm]
        exact hs.trans he) h
    simp only [safeRuntime_block_3409_fallthrough_stack,
      safeRuntime_block_3409_fallthrough_memory] at h₁
    obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeSetupModulesInitStore p evm h₁ hee hacc hperm hov
    exact .inr ⟨aw₂, k₂, C₂, he, h₂⟩
  · obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeRuntime_block_3409_taken_packed (by omega)
      (by
        rw [safeAddressMask, hh, u256_land_comm]
        exact fun hz ↦ he (hs.symm.trans hz)) (by jump_dest) h
    exact .inl ⟨safeRuntime_block_3626
      (by simp [safeRuntime_block_3409_taken_stack]; omega) h₁,
      safeSetupModulesAlreadyInitialized p evm he⟩

end Benchmarks.Safe.ViaIR
