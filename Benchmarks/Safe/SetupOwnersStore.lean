import Benchmarks.Safe.SetupOwnersSource
import Benchmarks.Safe.OwnerHeapTraces
import Benchmarks.Safe.WordArrayBuffer
import Benchmarks.Safe.Blocks.Runtime_035
import Benchmarks.Safe.Blocks.Runtime_036

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

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

set_option maxRecDepth 100000 in
theorem safeSetupOwnersStore (evm : EVM.State) {I g s0 σ k C aw mem rdata i n}
    {owner current threshold src ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨8145⟩
      (owner :: UInt256.ofNat i :: UInt256.ofNat n :: current :: threshold :: src :: ret :: R)
      mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ)
    (hc : current.toNat < EVM.addressModulus) (hfit : i + 1 < UInt256.size)
    (hperm : I.perm = true) (hov : R.length + 12 ≤ 1024) :
    ∃ aw' k' C', RD safeBytecode I g s0 ⟨8057⟩
      (UInt256.ofNat (i + 1) :: UInt256.ofNat n :: owner :: threshold :: src :: ret :: R)
      (twoWordHashMem current ⟨2⟩ mem) aw' rdata (writeOwnerLink evm current owner).accountMap
      k' C' := by
  obtain ⟨aw', k', C', h'⟩ := safeRuntime_block_8145_packed (by simp; omega)
    hperm (by jump_dest) h
  simp only [safeRuntime_block_8145_stack, safeRuntime_block_8145_memory, safeAddressMask,
    solcAddrMask_clean_left hc, uInt256_one_add_ofNat_of_lt hfit] at h'
  have hh := twoWordHashMemMapSlotAny current ⟨2⟩ mem
  change keccakWord ⟨0⟩ (UInt256.ofNat 64)
    ((UInt256.ofNat 2).toByteArray.write 0
      (current.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)
      (UInt256.ofNat 32).toNat 32) = _ at hh
  have hinc : UInt256.ofNat 1 + UInt256.ofNat i = UInt256.ofNat (i + 1) :=
    uInt256_one_add_ofNat_of_lt hfit
  rw [hh, hinc] at h'
  change RD safeBytecode I g s0 ⟨8057⟩
    (UInt256.ofNat (i + 1) :: UInt256.ofNat n :: owner :: threshold :: src :: ret :: R)
    (twoWordHashMem current ⟨2⟩ mem) aw' rdata
    (sstoreAccountMap I.codeOwner σ (mapSlot current ⟨2⟩)
      (UInt256.lor (UInt256.land owner solcAddrMask)
        (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWordAt (mapSlot current ⟨2⟩) σ I))))
    k' C' at h'
  rw [maskedAddressStoreWord, ← hee, ← hacc, ← writeOwnerLinkAccounts] at h'
  exact ⟨aw', k', C', by simpa only [hee] using h'⟩

end Benchmarks.Safe
