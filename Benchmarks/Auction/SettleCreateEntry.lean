import Benchmarks.Auction.SettleEntry
import Benchmarks.Auction.CreateInternal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem settleCreateEnter {I g s0 R mem aw rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨2607⟩ R mem aw rdata (cA, σ) k C)
    (hperm : I.perm = true) (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨2623⟩
      (⟨2682⟩ :: UInt256.isZero (pausedWord (sstoreAccountMap I.codeOwner σ ⟨101⟩ ⟨2⟩) I) :: R)
      mem aw rdata (cA, sstoreAccountMap I.codeOwner σ ⟨101⟩ ⟨2⟩) k' C' := by
  have rd2612 := evm_run h with [jumpdest, push1 ⟨2⟩, push1 ⟨101⟩]
  obtain ⟨_, _, rd2613⟩ := rd2612.sstore hperm (by native_decide) (by evm_ov)
  have rd2615 := evm_run rd2613 with [push1 ⟨51⟩]
  obtain ⟨_, _, rd2616⟩ := rd2615.sload (by native_decide) (by evm_ov)
  have rd2623 := evm_run rd2616 with [push1 ⟨255⟩, and, iszero, push2 ⟨2682⟩]
  rw [u256_land_comm ⟨255⟩] at rd2623
  exact ⟨_, _, rd2623⟩

theorem settleCreateUnpaused {I g s0 R mem aw rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨2623⟩ (⟨2682⟩ :: UInt256.isZero (pausedWord σ I) :: R)
      mem aw rdata (cA, σ) k C)
    (hp : pausedWord σ I = ⟨0⟩) (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨4086⟩ (⟨2690⟩ :: R)
      mem aw rdata (cA, σ) k' C' := by
  exact ⟨_, _, evm_run h with [jumpiT (by rw [hp]; decide) (by jump_dest), jumpdest,
    push2 ⟨2690⟩, push2 ⟨4086⟩, jump (by jump_dest)]⟩

theorem settleCreatePaused {I g s0 R mem aw rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨2623⟩ (⟨2682⟩ :: UInt256.isZero (pausedWord σ I) :: R)
      mem aw rdata (cA, σ) k C)
    (hp : pausedWord σ I ≠ ⟨0⟩) (hov : R.length + 6 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  have rd2624 := evm_run h with [jumpiNT (isZero_eq_zero_of_ne hp)]
  exact pausableError 0 rd2624 hov

theorem settleCreateNext {I g s0 R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨2690⟩ R mem aw rdata acc k C)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨3000⟩ (⟨2471⟩ :: R) mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run h with [jumpdest, push2 ⟨2471⟩, push2 ⟨3000⟩, jump (by jump_dest)]⟩

end Auction
