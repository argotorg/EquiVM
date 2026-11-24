import Benchmarks.Safe.ViaIR.SwapOwnerSource
import Benchmarks.Safe.ViaIR.Blocks.Runtime_008

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

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
    (h : RD fork safeBytecode I g s0 ⟨1255⟩ (old :: prev :: new :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 16 ≤ 1024) (hm : mem.size = 96)
    (hp : prev.toNat < EVM.addressModulus) (ho : old.toNat < EVM.addressModulus)
    (hn : new.toNat < EVM.addressModulus) (hperm : I.perm = true) :
    RDret fork safeBytecode g s0 (swapOwnerAccounts σ I prev old new) ByteArray.empty := by
  obtain ⟨_, _, h₁⟩ := safeRuntime_block_1255 (by omega) hperm h
  have hret := safeRuntime_block_1328 (by omega) hperm h₁
  simp only [safeRuntime_block_1255_stack, safeRuntime_block_1255_memory,
    safeAddressMask, solcAddrMask_clean_left hn, solcAddrMask_clean_left ho,
    solcAddrMask_clean_left hp, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, byteArray_readWithPadding_zero] at hret
  have hOld := twoWordHashMemMapSlot old (UInt256.ofNat 2) hm
  have hm₁ := twoWordHashMem_size_96 old (UInt256.ofNat 2) hm
  have hNew := twoWordHashMemMapSlot new (UInt256.ofNat 2) hm₁
  have hm₂ := twoWordHashMem_size_96 new (UInt256.ofNat 2) hm₁
  have hPrev := twoWordHashMemMapSlot prev (UInt256.ofNat 2) hm₂
  have hm₃ := twoWordHashMem_size_96 prev (UInt256.ofNat 2) hm₂
  have hClear := twoWordHashMemMapSlot old (UInt256.ofNat 2) hm₃
  dsimp only [twoWordHashMem, wordAt0Mem, wordAt32Mem] at hOld hNew hPrev hClear
  rw [hOld, hNew, hPrev, hClear] at hret
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
  change RDret fork safeBytecode g s0 (sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σ (mapSlot new ⟨2⟩)
        (setAddressOffset0Word (solcSlotWordAt (mapSlot new ⟨2⟩) σ I) (ownerLinkAt σ I old)))
      (mapSlot prev ⟨2⟩) (setAddressOffset0Word _ new))
    (mapSlot old ⟨2⟩) (UInt256.land (UInt256.lnot solcAddrMask) _)) ByteArray.empty at hret
  rw [hthird] at hret
  exact hret

theorem safeSwapOwnerTraceStatic {I g s0 σ k C aw mem rdata} {prev old new : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1255⟩ (old :: prev :: new :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 15 ≤ 1024) (hperm : I.perm = false) :
    RDstatic fork safeBytecode g s0 := by
  have hhash := evm_run h with [jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩,
    shl, sub, swap1, dup2, and, dup1, dup6, genMstore, push1 ⟨2⟩, push1 ⟨32⟩,
    dup2, dup2, genMstore, push1 ⟨64⟩, dup1, dup9, genKeccak256]
  obtain ⟨_, _, hnext⟩ := RD.sload hhash (by native_decide) (by simp; omega)
  have hnewhash := evm_run hnext with [swap7, dup6, and, dup1, dup10, genMstore,
    dup4, dup4, genMstore, dup2, dup10, genKeccak256, dup1]
  obtain ⟨_, _, hload⟩ := RD.sload hnewhash (by native_decide) (by simp; omega)
  have hstore := evm_run hload with [swap9, dup8, and, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨160⟩, shl, sub, not, swap10, dup11, and, or, swap1]
  exact hstore.sstoreStatic hperm (by native_decide) (by simp; omega)

end Benchmarks.Safe.ViaIR
