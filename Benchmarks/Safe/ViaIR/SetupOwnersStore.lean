import Benchmarks.Safe.ViaIR.SetupOwnersSource
import Benchmarks.Safe.ViaIR.OwnerHeapTraces
import Benchmarks.Safe.ViaIR.WordArrayBuffer
import Benchmarks.Safe.ViaIR.Blocks.Runtime_016
import Benchmarks.Safe.ViaIR.Blocks.Runtime_018

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

-- LIBRARY CANDIDATE: the two operand orders of a packed address store agree.
theorem maskedAddressStoreWord (old value : UInt256) :
    UInt256.lor (UInt256.land value solcAddrMask)
      (UInt256.land (UInt256.lnot solcAddrMask) old) = setAddressOffset0Word old value := by
  rw [setAddressOffset0Word, u256_land_comm (UInt256.lnot solcAddrMask), u256_lor_comm]

theorem writeOwnerLinkAccounts (evm : EVM.State) (key value : UInt256) :
    (writeOwnerLink evm key value).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap (mapSlot key ⟨2⟩)
        (setAddressOffset0Word (solcSlotWordAt (mapSlot key ⟨2⟩)
          evm.accountMap evm.executionEnv) value) := by
  simp only [writeOwnerLink, storageStore_accountMap, storageLoad_eq_solcSlotWord]
  rfl

theorem safeAddressHighMask :
    UInt256.shiftLeft (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
      (UInt256.ofNat 96)) (UInt256.ofNat 1)) (UInt256.ofNat 160) =
      UInt256.lnot solcAddrMask := by native_decide

set_option maxRecDepth 2000 in
theorem safeSetupOwnersStore (evm : EVM.State) {I g s0 σ k C aw mem rdata i}
    {owner current src n : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3742⟩
      (current :: ⟨0⟩ :: ⟨64⟩ :: owner :: ⟨1⟩ :: src :: UInt256.ofNat i :: n :: R)
      mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ)
    (hfit : i + 1 < UInt256.size) (hperm : I.perm = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨3333⟩
      (src :: UInt256.ofNat (i + 1) :: owner :: R)
      (twoWordHashMem current ⟨2⟩ mem) aw' rdata (writeOwnerLink evm current owner).accountMap
      k' C' := by
  obtain ⟨aw', k', C', h'⟩ := safeRuntime_block_3742_packed hov hperm (by jump_dest) h
  simp only [safeRuntime_block_3742_stack, safeRuntime_block_3742_memory,
    safeAddressHighMask] at h'
  have hlow : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) (UInt256.ofNat 160)) ⟨1⟩ =
      solcAddrMask := by native_decide
  rw [hlow] at h'
  have hh := twoWordHashMemMapSlotAny current ⟨2⟩ mem
  change keccakWord ⟨0⟩ ⟨64⟩
    ((UInt256.ofNat 2).toByteArray.write 0
      (current.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)
      (UInt256.ofNat 32).toNat 32) = _ at hh
  have hinc : UInt256.ofNat i + (⟨1⟩ : UInt256) = UInt256.ofNat (i + 1) := by
    rw [u256_add_comm]
    exact uInt256_one_add_ofNat_of_lt hfit
  rw [hh, hinc] at h'
  change RD fork safeBytecode I g s0 ⟨3333⟩
    (src :: UInt256.ofNat (i + 1) :: owner :: R)
    (twoWordHashMem current ⟨2⟩ mem) aw' rdata
    (sstoreAccountMap I.codeOwner σ (mapSlot current ⟨2⟩)
      (setAddressOffset0Word (solcSlotWordAt (mapSlot current ⟨2⟩) σ I) owner)) k' C' at h'
  rw [← hee, ← hacc, ← writeOwnerLinkAccounts] at h'
  exact ⟨aw', k', C', by simpa only [hee] using h'⟩

end Benchmarks.Safe.ViaIR
