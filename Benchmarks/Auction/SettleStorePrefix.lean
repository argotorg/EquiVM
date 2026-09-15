import Benchmarks.Auction.SettleStorage
import Benchmarks.Auction.SettleGuards

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem settleStorePrefix {I g s0 s ptr ret R mem aw rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨4397⟩ (ptr :: ret :: R) mem aw rdata (cA, σ) k C)
    (hm : SnapshotMemory s mem aw ptr) (hperm : I.perm = true) (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨4434⟩
      (⟨4536⟩ :: s.bidderWord :: ptr :: ret :: R) mem aw rdata
      (cA, settledAccounts σ I) k' C' := by
  have rd4401 := evm_run h with [jumpdest, push1 ⟨211⟩, dup1]
  obtain ⟨_, _, rd4402⟩ := rd4401.sload (by native_decide) (by evm_ov)
  have rd4416 := evm_run rd4402 with [push1 ⟨255⟩, push1 ⟨160⟩, shl, not, and,
    push1 ⟨1⟩, push1 ⟨160⟩, shl, or, swap1]
  obtain ⟨_, _, rd4417⟩ := rd4416.sstore hperm (by native_decide) (by evm_ov)
  have hl : loadedWord mem aw (ptr + ⟨128⟩) = s.bidderWord := hm.load ⟨4, by decide⟩
  have ha : expandedWords aw (ptr + ⟨128⟩) ⟨32⟩ = aw := hm.expand_eq ⟨4, by decide⟩
  have rd4422 := evm_run rd4417 with [push1 ⟨128⟩, dup2, add,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hl, ha] at rd4422
  have rd4434 := evm_run rd4422 with [push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    push2 ⟨4536⟩]
  have hmask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  rw [hmask, u256_land_comm solcAddrMask, Snapshot.bidderWord, maskTwice] at rd4434
  rw [u256_land_comm (UInt256.lnot (UInt256.shiftLeft ⟨255⟩ ⟨160⟩)),
    u256_lor_comm (UInt256.shiftLeft ⟨1⟩ ⟨160⟩)] at rd4434
  exact ⟨_, _, rd4434⟩

end Auction
