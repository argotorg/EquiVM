import Benchmarks.Safe.SwapOwnerSource
import Benchmarks.Safe.Blocks.Runtime_028
import Benchmarks.Safe.Blocks.Runtime_006

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

def swapOwnerAccounts (σ : AccountMap) (I : ExecutionEnv) (prev old new : UInt256) : AccountMap :=
  let σ₁ := sstoreAccountMap I.codeOwner σ (mapSlot new ⟨2⟩)
    (setAddressOffset0Word (solcSlotWordAt (mapSlot new ⟨2⟩) σ I) (ownerLinkAt σ I old))
  let σ₂ := sstoreAccountMap I.codeOwner σ₁ (mapSlot prev ⟨2⟩)
    (setAddressOffset0Word (solcSlotWordAt (mapSlot prev ⟨2⟩) σ₁ I) new)
  sstoreAccountMap I.codeOwner σ₂ (mapSlot old ⟨2⟩)
    (setAddressOffset0Word (solcSlotWordAt (mapSlot old ⟨2⟩) σ₂ I) ⟨0⟩)

theorem safeSwapOwnerAccounts (evm : EVM.State) (prev old new : UInt256) :
    (swapOwnerState evm prev old new).accountMap =
      swapOwnerAccounts evm.accountMap evm.executionEnv prev old new := by
  simp only [swapOwnerState, writeOwnerLink, ownerLink, storageStore_executionEnv,
    storageLoad_eq_solcSlotWord, storageStore_accountMap]
  rfl

theorem safeSwapOwnerTrace {I g s0 σ k C aw mem rdata} {prev old new : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨6275⟩ (new :: old :: prev :: ⟨664⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 16 ≤ 1024) (hm : mem.size = 96)
    (hp : prev.toNat < EVM.addressModulus) (ho : old.toNat < EVM.addressModulus)
    (hn : new.toNat < EVM.addressModulus) (hperm : I.perm = true) :
    RDret safeBytecode g s0 (swapOwnerAccounts σ I prev old new) ByteArray.empty := by
  obtain ⟨_, _, h₁⟩ := safeRuntime_block_6275 (by simp; omega) hperm h
  obtain ⟨_, _, h₂⟩ := safeRuntime_block_6348 (by omega) hperm (by jump_dest) h₁
  have hret := safeRuntime_block_664 (by simp [safeRuntime_block_6348_stack]; omega) h₂
  simp only [safeAddressMask, solcAddrMask_clean_left hn, solcAddrMask_clean_left ho,
    solcAddrMask_clean hp] at hret
  have hOld := twoWordHashMemMapSlot old (UInt256.ofNat 2) hm
  change keccakWord ⟨0⟩ (UInt256.ofNat 64)
    ((UInt256.ofNat 2).toByteArray.write 0
      (old.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) =
      mapSlot old ⟨2⟩ at hOld
  have hNew := keyAfterSlotHash new (UInt256.ofNat 2) (wordAt0Mem_size_96 old hm)
  change keccakWord ⟨0⟩ (UInt256.ofNat 64)
    (new.toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0
      (old.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)
      (⟨0⟩ : UInt256).toNat 32) = mapSlot new ⟨2⟩ at hNew
  have hm' : (wordAt0Mem new (twoWordHashMem old ⟨2⟩ mem)).size = 96 :=
    wordAt0Mem_size_96 new (twoWordHashMem_size_96 old ⟨2⟩ hm)
  have h32 : (wordAt0Mem new (twoWordHashMem old ⟨2⟩ mem)).readWithPadding 32 32 =
      (⟨2⟩ : UInt256).toByteArray := by
    unfold wordAt0Mem
    rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size])
      (by rw [twoWordHashMem_size_96 old ⟨2⟩ hm]; omega) (by omega)
      (by rw [twoWordHashMem_size_96 old ⟨2⟩ hm]; omega)]
    exact twoWordHashMem_read32 old ⟨2⟩ hm
  have hPrev := wordAt0Mem_solcMappingSlot_of_read32 prev ⟨2⟩ hm' h32
  change keccakWord ⟨0⟩ (UInt256.ofNat 64)
    (prev.toByteArray.write 0 (new.toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0
      (old.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)
      (⟨0⟩ : UInt256).toNat 32) (⟨0⟩ : UInt256).toNat 32) = mapSlot prev ⟨2⟩ at hPrev
  rw [hOld, hNew, hPrev] at hret
  have hfirst (word next : UInt256) :
      UInt256.lor (UInt256.land (UInt256.lnot solcAddrMask) word)
        (UInt256.land solcAddrMask next) =
      setAddressOffset0Word word (UInt256.land next solcAddrMask) := by
    rw [setAddressOffset0Word, maskTwice, u256_land_comm (UInt256.lnot solcAddrMask) word,
      u256_land_comm solcAddrMask next]
  have hsecond (word : UInt256) :
      UInt256.lor new (UInt256.land (UInt256.lnot solcAddrMask) word) =
      setAddressOffset0Word word new := by
    rw [← solcAddrMask_clean hn, setAddressOffset0Word_bytecode, solcAddrMask_clean hn]
  have hthird (word : UInt256) : UInt256.land (UInt256.lnot solcAddrMask) word =
      setAddressOffset0Word word ⟨0⟩ := by
    rw [setAddressOffset0Word, u256_land_zero_left, u256_lor_zero, u256_land_comm]
  simp only [hfirst, hsecond] at hret
  change RDret safeBytecode g s0 (sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σ (mapSlot new ⟨2⟩)
        (setAddressOffset0Word (solcSlotWordAt (mapSlot new ⟨2⟩) σ I) (ownerLinkAt σ I old)))
      (mapSlot prev ⟨2⟩) (setAddressOffset0Word _ new))
    (mapSlot old ⟨2⟩) (UInt256.land (UInt256.lnot solcAddrMask) _)) ByteArray.empty at hret
  rw [hthird] at hret
  exact hret

theorem safeSwapOwnerTraceStatic {I g s0 σ k C aw mem rdata} {prev old new : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨6275⟩ (new :: old :: prev :: R) mem aw rdata σ k C)
    (hov : R.length + 15 ≤ 1024) (hperm : I.perm = false) :
    RDstatic safeBytecode g s0 := by
  have hhash := evm_run h with [jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup3, dup2, and, push0, dup2, dup2, genMstore, push1 ⟨2⟩, push1 ⟨32⟩, genMstore,
    push1 ⟨64⟩, dup1, dup3, genKeccak256, dup1]
  obtain ⟨_, _, hnext⟩ := RD.sload hhash (by native_decide) (by simp; omega)
  have hnewhash := evm_run hnext with [dup7, dup7, and, dup1, dup6, genMstore, dup4, dup6,
    genKeccak256, dup1]
  obtain ⟨_, _, hload⟩ := RD.sload hnewhash (by native_decide) (by simp; omega)
  have hstore := evm_run hload with [swap3, dup9, and, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨160⟩, shl, sub, not, swap4, dup5, and, or, swap1]
  exact hstore.sstoreStatic hperm (by native_decide) (by simp; omega)

end Benchmarks.Safe
