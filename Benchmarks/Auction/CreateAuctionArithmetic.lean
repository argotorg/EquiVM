import Benchmarks.Auction.UnpauseCreateAuction
import Benchmarks.Auction.DynamicMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem auctionCreateAuctionCheckedAddNoOverflowGt (a b : UInt256)
    (hfit : a.toNat + b.toNat < UInt256.size) :
    UInt256.gt a (b + a) = ⟨0⟩ := by
  have hsum : (b + a).toNat = b.toNat + a.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt (by omega)]
  exact ugt_zero (by rw [hsum]; omega)

theorem auctionCreateAuctionCheckedAddOverflowGt (a b : UInt256)
    (hover : UInt256.size ≤ a.toNat + b.toNat) :
    UInt256.gt a (b + a) = ⟨1⟩ := by
  have hsum_lt2 : b.toNat + a.toNat < 2 * UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have hover' : UInt256.size ≤ b.toNat + a.toNat := by omega
  have hmod : (b.toNat + a.toNat) % UInt256.size =
      b.toNat + a.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover']
    exact Nat.mod_eq_of_lt (by omega)
  have haddNat : (b + a).toNat = b.toNat + a.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  apply ugt_one
  rw [haddNat]
  have hb : b.toNat < UInt256.size := b.val.isLt
  omega

theorem auctionCreateAuctionCheckedAddOk {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5704⟩ (a :: b :: ret :: R) mem aw rdata acc k C)
    (hfit : a.toNat + b.toNat < UInt256.size)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD auctionBytecode ee g s0 ret ((b + a) :: R) mem aw rdata acc k' C' := by
  have hgt : UInt256.gt a (b + a) = ⟨0⟩ :=
    auctionCreateAuctionCheckedAddNoOverflowGt a b hfit
  have rd5711₀ := evm_run h with [
    jumpdest, dup1, dup3, add, dup1, dup3, gt]
  have rd5711 := rd5711₀
  rw [hgt] at rd5711
  have rd5712₀ := evm_run rd5711 with [iszero]
  have rd5712 := rd5712₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd5712
  have rd4886 := evm_run rd5712 with [
    push2 ⟨4886⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  exact ⟨_, _, evm_run rd4886 with [
    jumpdest, swap3, swap2, pop, pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem auctionPanicOverflowRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {R : List UInt256} {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5630⟩ R mem (UInt256.ofNat 5) rdata acc k C)
    (hov : R.length + 2 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  have hsel : UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
      ⟨35408467139433450592217433187231851964531694900788300625387963629091585785856⟩ := by
    decide
  have rd5639₀ := evm_run h with [
    jumpdest, push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0]
  have rd5639 := rd5639₀
  rw [hsel] at rd5639
  have rd5643 := evm_run rd5639 with [
    raw mstore 0
      ((UInt256.toByteArray
        (⟨35408467139433450592217433187231851964531694900788300625387963629091585785856⟩ :
          UInt256)).write 0 mem 0 32)
      (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨17⟩, push1 ⟨4⟩]
  have rd5648 := evm_run rd5643 with [
    raw mstore 0
      ((UInt256.toByteArray (⟨17⟩ : UInt256)).write 0
        ((UInt256.toByteArray
          (⟨35408467139433450592217433187231851964531694900788300625387963629091585785856⟩ :
            UInt256)).write 0 mem 0 32) 4 32)
      (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, push0]
  exact rd5648.rev 0 (by native_decide) mem_cost (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem auctionCreateAuctionCheckedAddOverflow {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5704⟩ (a :: b :: ret :: R) mem (UInt256.ofNat 5)
      rdata acc k C)
    (hover : UInt256.size ≤ a.toNat + b.toNat) (hov : R.length + 9 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  have hgt : UInt256.gt a (b + a) = ⟨1⟩ :=
    auctionCreateAuctionCheckedAddOverflowGt a b hover
  have rd5711₀ := evm_run h with [
    jumpdest, dup1, dup3, add, dup1, dup3, gt]
  have rd5711 := rd5711₀
  rw [hgt] at rd5711
  have rd5712₀ := evm_run rd5711 with [iszero]
  have rd5712 := rd5712₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd5712
  have rd5630 := evm_run rd5712 with [
    push2 ⟨4886⟩, jumpiNT (by decide), push2 ⟨4886⟩, push2 ⟨5630⟩,
    jump (by jump_dest)]
  exact auctionPanicOverflowRevert rd5630 (by evm_ov)

theorem auctionPanicOverflowDynamic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {mem rdata : ByteArray} {R : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (h : RD auctionBytecode I g s0 ⟨5630⟩ R mem aw rdata acc k C)
    (hR : R.length + 2 ≤ 1024) : RDrev auctionBytecode g s0 := by
  have h5639 := evm_run h with [jumpdest, push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0]
  obtain ⟨_, _, h5640⟩ := auctionMstoreDynamic h5639 (by native_decide) (by evm_ov)
  have h5644 := evm_run h5640 with [push1 ⟨17⟩, push1 ⟨4⟩]
  obtain ⟨_, _, h5645⟩ := auctionMstoreDynamic h5644 (by native_decide) (by evm_ov)
  have h5648 := evm_run h5645 with [push1 ⟨36⟩, push0]
  exact auctionRevertDynamic h5648 (by native_decide) (by evm_ov)

theorem auctionCheckedAddOverflowDynamic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {a b ret aw : UInt256} {mem rdata : ByteArray} {R : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (h : RD auctionBytecode I g s0 ⟨5704⟩ (a :: b :: ret :: R) mem aw rdata acc k C)
    (hover : UInt256.size ≤ a.toNat + b.toNat) (hR : R.length + 9 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  have h5711 := evm_run h with [jumpdest, dup1, dup3, add, dup1, dup3, gt]
  rw [auctionCreateAuctionCheckedAddOverflowGt a b hover] at h5711
  have h5630 := evm_run h5711 with [iszero, push2 ⟨4886⟩, jumpiNT (by native_decide),
    push2 ⟨4886⟩, push2 ⟨5630⟩, jump (by jump_dest)]
  exact auctionPanicOverflowDynamic h5630 (by evm_ov)


end Auction
