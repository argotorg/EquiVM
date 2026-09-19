import Solm.Benchmarks.Auction.ReentrancyGuard
import Solm.Benchmarks.Auction.SettleInternal
import Solm.Benchmarks.Auction.PausableSource
import Solm.Benchmarks.Auction.PausableErrors

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem settlePausedPrefix {I g s0 R mem aw rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨2351⟩ R mem aw rdata (cA, σ) k C)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨2361⟩ (⟨2424⟩ :: pausedWord σ I :: R)
      mem aw rdata (cA, σ) k' C' := by
  have rd2354 := evm_run h with [jumpdest, push1 ⟨51⟩]
  obtain ⟨_, _, rd2355⟩ := rd2354.sload (by native_decide) (by evm_ov)
  have rd2361 := evm_run rd2355 with [push1 ⟨255⟩, and, push2 ⟨2424⟩]
  rw [u256_land_comm ⟨255⟩] at rd2361
  exact ⟨_, _, rd2361⟩

theorem settlePaused {I g s0 R mem aw rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨2351⟩ R mem aw rdata (cA, σ) k C)
    (hp : pausedWord σ I ≠ ⟨0⟩) (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨2424⟩ R mem aw rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rd2361⟩ := settlePausedPrefix h hov
  exact ⟨_, _, evm_run rd2361 with [jumpiT hp (by jump_dest)]⟩

theorem settleNotPaused {I g s0 R mem aw rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨2351⟩ R mem aw rdata (cA, σ) k C)
    (hp : pausedWord σ I = ⟨0⟩) (hov : R.length + 7 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  obtain ⟨_, _, rd2361⟩ := settlePausedPrefix h (by omega)
  have rd2362 := evm_run rd2361 with [jumpiNT hp]
  exact pausableError 2 rd2362 (by omega)

theorem settleEnter {I g s0 ret R mem aw rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨2458⟩ (ret :: R) mem aw rdata (cA, σ) k C)
    (hperm : I.perm = true) (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨4086⟩ (⟨2471⟩ :: ret :: R)
      mem aw rdata (cA, sstoreAccountMap I.codeOwner σ ⟨101⟩ ⟨2⟩) k' C' := by
  have rd2463 := evm_run h with [jumpdest, push1 ⟨2⟩, push1 ⟨101⟩]
  obtain ⟨_, _, rd2464⟩ := rd2463.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd2464 with [push2 ⟨2471⟩, push2 ⟨4086⟩, jump (by jump_dest)]⟩

theorem settleExit {I g s0 ret R mem aw rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨2471⟩ (ret :: R) mem aw rdata (cA, σ) k C)
    (hperm : I.perm = true) (hret : (D_J auctionBytecode 0).contains ret = true)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret R mem aw rdata
      (cA, sstoreAccountMap I.codeOwner σ ⟨101⟩ ⟨1⟩) k' C' := by
  have rd2476 := evm_run h with [jumpdest, push1 ⟨1⟩, push1 ⟨101⟩]
  obtain ⟨_, _, rd2477⟩ := rd2476.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd2477 with [jump hret]⟩

end Auction
