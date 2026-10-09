import Benchmarks.Auction.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Reasoning.Reach

theorem RD.auctionReturn32 {ee g s0 val R rdata acc k C}
    (h : RD auctionBytecode ee g s0 ⟨318⟩ ((⟨160⟩ : UInt256) :: R)
      (solcReturnMem val) (UInt256.ofNat 5) rdata acc k C)
    (hov : R.length + 5 ≤ 1024) :
    RDret auctionBytecode g s0 acc (UInt256.toByteArray val) := by
  exact evm_run h with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide) mem_cost
      (solcReturnMem_mload64 val) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray val) (by native_decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub (⟨160⟩ : UInt256) ⟨128⟩).toNat = 32 from by decide]
        exact solcReturnMem_read128 val)
      (by evm_ov) ]

theorem RD.auctionReturnWord {ee g s0 val R rdata acc k C}
    (h : RD auctionBytecode ee g s0 ⟨308⟩ (val :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 5 ≤ 1024) :
    RDret auctionBytecode g s0 acc (UInt256.toByteArray val) := by
  have rd318 := evm_run h with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
      solcFreePtrMem_mload64 (by decide) (by evm_ov),
    swap1, dup2,
    raw mstore 6 (solcReturnMem val) (UInt256.ofNat 5) (by native_decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, add ]
  exact rd318.auctionReturn32 hov

theorem RD.auctionReturnAddress {ee g s0 val R rdata acc k C}
    (h : RD auctionBytecode ee g s0 ⟨358⟩ (val :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 6 ≤ 1024) :
    RDret auctionBytecode g s0 acc (UInt256.toByteArray (UInt256.land val solcAddrMask)) := by
  have rd318 := evm_run h with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
      solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    swap1, swap2, and, dup2,
    raw mstore 6 (solcReturnMem (UInt256.land val solcAddrMask)) (UInt256.ofNat 5)
      (by native_decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨318⟩, jump (by jump_dest) ]
  exact rd318.auctionReturn32 (by omega)

end Reasoning.Reach
