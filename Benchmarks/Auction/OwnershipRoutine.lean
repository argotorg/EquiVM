import Benchmarks.Auction.SetterSource
import Benchmarks.Auction.Events

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem assignOwner (evm : EVM.State) (locals : Store) (value : UInt256)
    (hbase : locals.get? "_owner" = none) (hc : value.toNat < EVM.addressModulus) :
    assignStorageRef? auctionConfig { contract := auctionContract, locals := locals } evm
      .storage ownerRef (.address (AccountAddress.ofNat value.toNat)) =
      .ok ({ contract := auctionContract, locals := locals },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨151⟩
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) value)) := by
  exact scalarWrite evm _ locals "_owner" (.elem .address) (auctionAddrLoc ⟨151⟩) _
    hbase (by native_decide) rfl (by trivial) (storageLocStore_address_offset0 evm ⟨151⟩ value hc)

theorem transferOwnerRoutine {I g s0 value ret R rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨3574⟩ (value :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hperm : I.perm = true) (hret : (D_J auctionBytecode 0).contains ret = true)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret R solcFreePtrMem (UInt256.ofNat 3)
      rdata (cA, sstoreAccountMap I.codeOwner σ ⟨151⟩
        (setAddressOffset0Word (storedWord σ I ⟨151⟩) value)) k' C' := by
  have rd3578 := evm_run h with [jumpdest, push1 ⟨151⟩, dup1]
  obtain ⟨_, _, rd3579⟩ := rd3578.sload (by native_decide) (by evm_ov)
  have rd3590 := evm_run rd3579 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, dup2, and ]
  have rd3605 := evm_run rd3590 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, dup4, and, dup2, or, swap1, swap4 ]
  obtain ⟨_, _, rd3606⟩ := rd3605.sstore hperm (by native_decide) (by evm_ov)
  have rd3615 := evm_run rd3606 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
      solcFreePtrMem_mload64 (by decide) (by evm_ov),
    swap2, and, swap2, swap1, dup3, swap1 ]
  have rd3648 := rd3615.pushConst
    ⟨0x8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e0⟩
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rdRet := evm_run rd3648 with [
    swap1, push0, swap1,
    raw log3 0 (UInt256.ofNat 3) (by native_decide) hperm mem_cost
      (by decide) (by evm_ov),
    pop, pop, jump hret ]
  change RD _ _ _ _ _ _ _ _ _
    (cA, sstoreAccountMap I.codeOwner σ ⟨151⟩
      (UInt256.lor (UInt256.land solcAddrMask value)
        (UInt256.land (storedWord σ I ⟨151⟩) (UInt256.lnot solcAddrMask)))) _ _ at rdRet
  rw [u256_land_comm solcAddrMask value, u256_lor_comm (UInt256.land value solcAddrMask)]
    at rdRet
  exact ⟨_, _, rdRet⟩

theorem auctionInternalReturn {I g s0 ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨1163⟩ (ret :: R) mem aw rdata acc k C)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 1 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret R mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run h with [jumpdest, jump hret]⟩

end Auction
