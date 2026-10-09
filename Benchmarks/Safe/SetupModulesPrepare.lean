import Benchmarks.Safe.SetupModulesSource
import Benchmarks.Safe.SetupOwnersStore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

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

set_option maxRecDepth 100000 in
theorem safeSetupModulesInitStore (p : SetupModulesInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata} {ptr ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨8393⟩ (ptr :: p.target :: ret :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ)
    (hc : p.target.toNat < EVM.addressModulus) (hperm : I.perm = true)
    (hov : R.length + 12 ≤ 1024) :
    ∃ aw' k' C', RD safeBytecode I g s0 (if p.target = ⟨0⟩ then ⟨1936⟩ else ⟨8470⟩)
      (ptr :: p.target :: ret :: R) (twoWordHashMem ⟨1⟩ ⟨1⟩ mem) aw' rdata
      (p.state evm).accountMap k' C' := by
  have hw (word : UInt256) : UInt256.lor (UInt256.ofNat 1)
      (UInt256.land (UInt256.lnot solcAddrMask) word) = setAddressOffset0Word word ⟨1⟩ := by
    simpa only [show UInt256.land (⟨1⟩ : UInt256) solcAddrMask = ⟨1⟩ from by decide] using
      maskedAddressStoreWord word ⟨1⟩
  have ha : setupModulesAccounts σ I = (p.state evm).accountMap := by
    rw [setupModulesState_accounts, hee, hacc]
  by_cases hz : p.target = ⟨0⟩
  · obtain ⟨aw', k', C', h'⟩ := safeRuntime_block_8393_taken_packed (by simp; omega) hperm
      (by rw [safeAddressMask, solcAddrMask_clean hc, hz]; decide) (by jump_dest) h
    simp only [safeRuntime_block_8393_taken_memory, safeAddressMask,
      ← safeModuleSentinelSlot, hw] at h'
    change RD safeBytecode I g s0 ⟨1936⟩ (ptr :: p.target :: ret :: R)
      (twoWordHashMem ⟨1⟩ ⟨1⟩ mem) aw' rdata (setupModulesAccounts σ I) k' C' at h'
    rw [ha] at h'
    exact ⟨aw', k', C', by simpa only [if_pos hz] using h'⟩
  · obtain ⟨aw', k', C', h'⟩ := safeRuntime_block_8393_fallthrough_packed (by simp; omega)
      hperm (by rw [safeAddressMask, solcAddrMask_clean hc]; exact isZero_eq_zero_of_ne hz) h
    simp only [safeRuntime_block_8393_fallthrough_memory, safeAddressMask,
      ← safeModuleSentinelSlot, hw] at h'
    change RD safeBytecode I g s0 ⟨8470⟩ (ptr :: p.target :: ret :: R)
      (twoWordHashMem ⟨1⟩ ⟨1⟩ mem) aw' rdata (setupModulesAccounts σ I) k' C' at h'
    rw [ha] at h'
    exact ⟨aw', k', C', by simpa only [if_neg hz] using h'⟩

set_option maxRecDepth 100000 in
theorem safeSetupModulesPrepare (p : SetupModulesInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata} {ptr ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨8319⟩ (ptr :: p.target :: ret :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ)
    (hc : p.target.toNat < EVM.addressModulus) (hperm : I.perm = true)
    (hov : R.length + 20 ≤ 1024) :
    (RDrev safeBytecode g s0 ∧
      ExecFuncBody config p.frame evm setupModulesFunction.body .reverted) ∨
    ∃ aw' k' C', moduleLink evm ⟨1⟩ = ⟨0⟩ ∧
      RD safeBytecode I g s0 (if p.target = ⟨0⟩ then ⟨1936⟩ else ⟨8470⟩)
        (ptr :: p.target :: ret :: R) (setupModulesMemory mem) aw' rdata
        (p.state evm).accountMap k' C' := by
  have hs : moduleLinkAt σ I ⟨1⟩ = moduleLink evm ⟨1⟩ := by
    rw [moduleLink_eq_at, hee, hacc]
  by_cases he : moduleLink evm ⟨1⟩ = ⟨0⟩
  · obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeRuntime_block_8319_taken_packed (by simp; omega)
      (by
        rw [safeAddressMask, ← safeModuleSentinelSlot, u256_land_comm]
        change UInt256.isZero (moduleLinkAt σ I ⟨1⟩) ≠ UInt256.ofNat 0
        rw [hs, he]; decide) (by jump_dest) h
    obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeSetupModulesInitStore p evm h₁ hee hacc hc hperm (by omega)
    exact .inr ⟨aw₂, k₂, C₂, he, h₂⟩
  · obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeRuntime_block_8319_fallthrough_packed (by simp; omega)
      (by
        rw [safeAddressMask, ← safeModuleSentinelSlot, u256_land_comm]
        change UInt256.isZero (moduleLinkAt σ I ⟨1⟩) = UInt256.ofNat 0
        rw [hs]; exact isZero_eq_zero_of_ne he) h
    have h₂ := safeRuntime_block_8377 (by simp; omega) (by jump_dest) h₁
    exact .inl ⟨safeRuntime_block_6898 (by simp; omega) h₂,
      safeSetupModulesAlreadyInitialized p evm he⟩

end Benchmarks.Safe
