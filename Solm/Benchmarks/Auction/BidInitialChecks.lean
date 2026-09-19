import Solm.Benchmarks.Auction.BidSource
import Solm.Benchmarks.Auction.BidErrors
import Solm.Benchmarks.Auction.BidSnapshot

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem bidInitialChecks {I g s0 s noun ptr ret R mem aw rdata cA σ k C evm locals}
    (h : RD auctionBytecode I g s0 ⟨1282⟩ (ptr :: Snapshot.nounId s :: noun :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hm : SnapshotMemory s mem aw ptr)
    (hv : BidValues locals s noun) (hov : R.length + 10 ≤ 1024) :
    (∃ k' C',
      ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
        bidInitialGuardStmts (.ok { contract := auctionContract, locals := locals } evm) ∧
      (UInt256.ofNat I.header.timestamp).toNat < s.endTime.toNat ∧
      RD auctionBytecode I g s0 ⟨1511⟩ (ptr :: noun :: ret :: R)
        mem aw rdata (cA, σ) k' C') ∨
    (ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
      bidInitialGuardStmts .reverted ∧ RDrev auctionBytecode g s0) := by
  have he := bidNounGuardSource (evm := evm) hv
  have rd1288 := evm_run h with [swap1, dup3, eq, push2 ⟨1360⟩]
  by_cases hn : s.nounId = noun
  · rw [decide_eq_true hn] at he
    have rd1360 := evm_run rd1288 with [jumpiT (by rw [hn, uInt256_eq_self]; decide)
      (by jump_dest)]
    have ht := bidTimeGuardSource hs hv
    have hl : loadedWord mem aw (ptr + ⟨96⟩) = s.endTime := hm.load ⟨3, by decide⟩
    have ha : expandedWords aw (ptr + ⟨96⟩) ⟨32⟩ = aw := hm.expand_eq ⟨3, by decide⟩
    have rd1366 := evm_run rd1360 with [jumpdest, dup1, push1 ⟨96⟩, add,
      raw mloadSymbolic (by native_decide) (by evm_ov)]
    rw [u256_add_comm ⟨96⟩ ptr, hl, ha] at rd1366
    have rd1371 := evm_run rd1366 with [timestamp, lt, push2 ⟨1429⟩]
    by_cases htime : (UInt256.ofNat I.header.timestamp).toNat < s.endTime.toNat
    · rw [decide_eq_true htime] at ht
      have rd1429 := evm_run rd1371 with [jumpiT (by rw [ult_one htime]; decide)
        (by jump_dest)]
      have hr := bidReserveGuardSource hs hv
      have rd1432 := evm_run rd1429 with [jumpdest, push1 ⟨204⟩]
      obtain ⟨_, _, rd1433⟩ := rd1432.sload (by native_decide) (by evm_ov)
      change RD _ _ _ _ ⟨1433⟩ (storedWord σ I ⟨204⟩ :: ptr :: noun :: ret :: R)
        mem aw rdata (cA, σ) _ _ at rd1433
      have rd1439 := evm_run rd1433 with [callvalue, lt, iszero, push2 ⟨1511⟩]
      by_cases hres : (storedWord σ I ⟨204⟩).toNat ≤ I.weiValue.toNat
      · rw [decide_eq_true hres] at hr
        have rd1511 := evm_run rd1439 with [jumpiT (by rw [ult_zero hres]; decide)
          (by jump_dest)]
        exact Or.inl ⟨_, _, ExecBlock.consNormal (ExecStmt.requireTrue he)
          (ExecBlock.consNormal (ExecStmt.requireTrue ht)
            (ExecBlock.consNormal (ExecStmt.requireTrue hr) ExecBlock.nil)), htime, rd1511⟩
      · rw [decide_eq_false hres] at hr
        have rd1440 := evm_run rd1439 with [jumpiNT (by rw [ult_one (by omega)]; decide)]
        exact Or.inr ⟨ExecBlock.consNormal (ExecStmt.requireTrue he)
          (ExecBlock.consNormal (ExecStmt.requireTrue ht)
            (ExecBlock.consRevert (ExecStmt.requireFalse hr))),
          bidReserveError rd1440 (by evm_ov)⟩
    · rw [decide_eq_false htime] at ht
      have rd1372 := evm_run rd1371 with [jumpiNT (ult_zero (by omega))]
      exact Or.inr ⟨ExecBlock.consNormal (ExecStmt.requireTrue he)
        (ExecBlock.consRevert (ExecStmt.requireFalse ht)), bidExpiredError rd1372 (by evm_ov)⟩
  · rw [decide_eq_false hn] at he
    have rd1289 := evm_run rd1288 with [jumpiNT (u256_eq_of_ne (Ne.symm hn))]
    exact Or.inr ⟨ExecBlock.consRevert (ExecStmt.requireFalse he),
      bidWrongNounError rd1289 (by evm_ov)⟩

end Auction
