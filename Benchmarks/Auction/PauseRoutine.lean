import Benchmarks.Auction.PausableSource
import Benchmarks.Auction.AddressEvent
import Benchmarks.Auction.PausableErrors

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem pausePrefix {I g s0 R mem aw rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨3655⟩ R mem aw rdata (cA, σ) k C)
    (hov : R.length + 2 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨3663⟩ (UInt256.isZero (pausedWord σ I) :: R)
      mem aw rdata (cA, σ) k' C' := by
  have rd3658 := evm_run h with [jumpdest, push1 ⟨51⟩]
  obtain ⟨_, _, rd3659⟩ := rd3658.sload (by native_decide) (by evm_ov)
  have rd3663 := evm_run rd3659 with [push1 ⟨255⟩, and, iszero]
  change RD _ _ _ _ _ (UInt256.isZero (UInt256.land ⟨255⟩ (storedWord σ I ⟨51⟩)) :: R)
    _ _ _ _ _ _ at rd3663
  rw [u256_land_comm ⟨255⟩] at rd3663
  exact ⟨_, _, rd3663⟩

theorem pauseStore {I g s0 ret R mem aw rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨3725⟩ (ret :: R) mem aw rdata (cA, σ) k C)
    (hperm : I.perm = true) (hret : (D_J auctionBytecode 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret R (addressEventMem mem aw (solcSourceWord I))
      (addressEventWords mem aw (solcSourceWord I)) rdata
      (cA, sstoreAccountMap I.codeOwner σ ⟨51⟩ (pauseWord (storedWord σ I ⟨51⟩))) k' C' := by
  have rd3729 := evm_run h with [jumpdest, push1 ⟨51⟩, dup1]
  obtain ⟨_, _, rd3730⟩ := rd3729.sload (by native_decide) (by evm_ov)
  have rd3738 := evm_run rd3730 with [push1 ⟨255⟩, not, and, push1 ⟨1⟩, or, swap1]
  obtain ⟨_, _, rd3739⟩ := rd3738.sstore hperm (by native_decide) (by evm_ov)
  have rd3772 := rd3739.pushConst
    ⟨0x62e78cea01bee320cd4e420270b5ea74000d11b0c9f74754ebdbfc544b05a258⟩
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd2971 := evm_run rd3772 with [push2 ⟨2971⟩, caller, swap1, jump (by jump_dest)]
  change RD _ _ _ _ _ _ _ _ _ (cA, sstoreAccountMap I.codeOwner σ ⟨51⟩
    (UInt256.lor ⟨1⟩ (UInt256.land (UInt256.lnot ⟨255⟩) (storedWord σ I ⟨51⟩)))) _ _
    at rd2971
  rw [u256_land_comm (UInt256.lnot ⟨255⟩), u256_lor_comm ⟨1⟩] at rd2971
  exact addressEventReturn rd2971 hperm hret hov

theorem pauseRoutineOk {I g s0 ret R mem aw rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨3655⟩ (ret :: R) mem aw rdata (cA, σ) k C)
    (hp : pausedWord σ I = ⟨0⟩) (hperm : I.perm = true)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret R (addressEventMem mem aw (solcSourceWord I))
      (addressEventWords mem aw (solcSourceWord I)) rdata
      (cA, sstoreAccountMap I.codeOwner σ ⟨51⟩ (pauseWord (storedWord σ I ⟨51⟩))) k' C' := by
  obtain ⟨_, _, rd3663⟩ := pausePrefix h (by evm_ov)
  have rd3725 := evm_run rd3663 with [
    push2 ⟨3725⟩, jumpiT (by rw [hp]; decide) (by jump_dest) ]
  exact pauseStore rd3725 hperm hret hov

theorem pauseRoutineRevert {I g s0 R mem aw rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨3655⟩ R mem aw rdata (cA, σ) k C)
    (hp : pausedWord σ I ≠ ⟨0⟩) (hov : R.length + 6 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  obtain ⟨_, _, rd3663⟩ := pausePrefix h (by omega)
  have rd3667 := evm_run rd3663 with [
    push2 ⟨3725⟩, jumpiNT (isZero_eq_zero_of_ne hp) ]
  exact pausableError 1 rd3667 hov

end Auction
