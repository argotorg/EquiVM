import Solm.Benchmarks.Auction.BidInitialChecks
import Solm.Benchmarks.Auction.CheckedMul
import Solm.Benchmarks.Auction.CheckedDivSub

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem bidMinimumPrefix {I g s0 s noun ptr ret R mem aw rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨1511⟩ (ptr :: noun :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hm : SnapshotMemory s mem aw ptr) (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨5650⟩
      (s.amount :: bidPercentage σ I :: ⟨1537⟩ :: ⟨100⟩ :: ptr :: noun :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
  have rd1514 := evm_run h with [jumpdest, push1 ⟨205⟩]
  obtain ⟨_, _, rd1515⟩ := rd1514.sload (by native_decide) (by evm_ov)
  have rd1520 := evm_run rd1515 with [push1 ⟨32⟩, dup3, add,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  have hl : loadedWord mem aw (ptr + ⟨32⟩) = s.amount := hm.load ⟨1, by decide⟩
  have ha : expandedWords aw (ptr + ⟨32⟩) ⟨32⟩ = aw := hm.expand_eq ⟨1, by decide⟩
  rw [hl, ha] at rd1520
  exact ⟨_, _, evm_run rd1520 with [push1 ⟨100⟩, swap2, push2 ⟨1537⟩, swap2,
    push1 ⟨255⟩, swap1, swap2, and, swap1, push2 ⟨5650⟩, jump (by jump_dest)]⟩

theorem bidMinimumCheck {I g s0 s noun ptr ret R mem aw rdata cA σ k C evm locals}
    (h : RD auctionBytecode I g s0 ⟨1511⟩ (ptr :: noun :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hm : SnapshotMemory s mem aw ptr)
    (hv : BidValues locals s noun) (hov : R.length + 13 ≤ 1024) :
    (∃ k' C',
      ExecStmt auctionConfig { contract := auctionContract, locals := locals } evm
        (.require bidMinimumGuard) (.ok { contract := auctionContract, locals := locals } evm) ∧
      RD auctionBytecode I g s0 ⟨1681⟩ (ptr :: noun :: ret :: R)
        mem aw rdata (cA, σ) k' C') ∨
    (ExecStmt auctionConfig { contract := auctionContract, locals := locals } evm
      (.require bidMinimumGuard) .reverted ∧ RDrev auctionBytecode g s0) := by
  obtain ⟨_, _, rd5650⟩ := bidMinimumPrefix h hm (by omega)
  by_cases hmul : s.amount.toNat * (bidPercentage σ I).toNat < UInt256.size
  · obtain ⟨_, _, rd1537⟩ := checkedMulOk rd5650 (by rwa [Nat.mul_comm])
      (by jump_dest) (by evm_ov)
    have hc : UInt256.mul (bidPercentage σ I) s.amount =
        UInt256.mul s.amount (bidPercentage σ I) := u256_mul_comm _ _
    rw [hc] at rd1537
    have rd5673 := evm_run rd1537 with [jumpdest, push2 ⟨1547⟩, swap2, swap1,
      push2 ⟨5673⟩, jump (by jump_dest)]
    obtain ⟨_, _, rd1547⟩ := checkedDivOk rd5673 (by decide) (by jump_dest) (by evm_ov)
    change RD _ _ _ _ ⟨1547⟩ (bidIncrement s.amount (bidPercentage σ I) :: ptr :: noun :: ret :: R)
      mem aw rdata (cA, σ) _ _ at rd1547
    have rd1553 := evm_run rd1547 with [jumpdest, dup2, push1 ⟨32⟩, add,
      raw mloadSymbolic (by native_decide) (by evm_ov)]
    have hl : loadedWord mem aw (ptr + ⟨32⟩) = s.amount := hm.load ⟨1, by decide⟩
    have ha : expandedWords aw (ptr + ⟨32⟩) ⟨32⟩ = aw := hm.expand_eq ⟨1, by decide⟩
    rw [u256_add_comm ⟨32⟩ ptr, hl, ha] at rd1553
    have rd5704 := evm_run rd1553 with [push2 ⟨1562⟩, swap2, swap1,
      push2 ⟨5704⟩, jump (by jump_dest)]
    by_cases hadd : s.amount.toNat + (bidIncrement s.amount (bidPercentage σ I)).toNat <
        UInt256.size
    · obtain ⟨_, _, rd1562⟩ := checkedAddOk rd5704 hadd (by jump_dest) (by evm_ov)
      rw [u256_add_comm (bidIncrement s.amount (bidPercentage σ I))] at rd1562
      have rd1569 := evm_run rd1562 with [jumpdest, callvalue, lt, iszero, push2 ⟨1681⟩]
      have he := bidMinimumSource hs hv hmul hadd
      by_cases hmin : (s.amount + bidIncrement s.amount (bidPercentage σ I)).toNat ≤
          I.weiValue.toNat
      · rw [decide_eq_true hmin] at he
        exact Or.inl ⟨_, _, ExecStmt.requireTrue he,
          evm_run rd1569 with [jumpiT (by rw [ult_zero hmin]; decide) (by jump_dest)]⟩
      · rw [decide_eq_false hmin] at he
        have rd1570 := evm_run rd1569 with [jumpiNT (by rw [ult_one (by omega)]; decide)]
        exact Or.inr ⟨ExecStmt.requireFalse he, bidIncrementError rd1570 (by evm_ov)⟩
    · exact Or.inr ⟨ExecStmt.requireRevert (bidMinimumAddOverflow hs hv hmul (by omega)),
        checkedAddOverflow rd5704 (by omega) (by evm_ov)⟩
  · exact Or.inr ⟨ExecStmt.requireRevert (bidMinimumMulOverflow hs hv (by omega)),
      checkedMulOverflow rd5650 (by rw [Nat.mul_comm]; omega) (by evm_ov)⟩

end Auction
