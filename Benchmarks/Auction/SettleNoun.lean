import Benchmarks.Auction.SettleStorePrefix
import Benchmarks.Auction.NounRoutines
import Benchmarks.Auction.CallGrowth

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def settleNounStmt : Stmt :=
  .ite (.binary .eq (auctionMemField "bidder") zeroAddr) settleBurnStmts settleTransferStmts

theorem settleBidderGuardSource {evm locals s}
    (hs : locals.get? "_auction" = some (Snapshot.value s)) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.binary .eq (auctionMemField "bidder") zeroAddr) =
      .ok (.bool (decide (s.bidderWord = ⟨0⟩))) := by
  simp only [zeroAddr, evalExpr?, snapshotBidderSource hs, pure, bind, EvalResult.bind,
    evalBinaryOp?, castValue?, addrSt, EvalResult.ofOption, Int.lt_irrefl, ↓reduceIte]
  change EvalResult.ok (Value.bool ((Value.address (AccountAddress.ofNat s.bidderWord.toNat)) ==
    .address 0)) = EvalResult.ok (Value.bool (decide (s.bidderWord = ⟨0⟩)))
  congr 2
  by_cases hz : s.bidderWord = ⟨0⟩
  · rw [hz]; rfl
  · have hc := solcAddrMask_result_canonical s.packed
    have hn : s.bidderWord.toNat < AccountAddress.size := hc
    have hne : Value.address (AccountAddress.ofNat s.bidderWord.toNat) ≠ .address 0 := by
      intro he
      have hv := congrArg Fin.val (Value.address.inj he)
      change s.bidderWord.toNat % AccountAddress.size = 0 at hv
      rw [Nat.mod_eq_of_lt hn] at hv
      exact hz (u256_inj hv)
    rw [beq_eq_false_iff_ne.mpr hne, decide_eq_false hz]

theorem settleNounRoutine {I g s0 s snap ret R mem aw ptr rdata cA σ k C evm locals}
    (h : RD auctionBytecode I g s0 ⟨4434⟩
      (⟨4536⟩ :: Snapshot.bidderWord s :: snap :: ret :: R) mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 100 ≤ 2 ^ 200)
    (hsm : SnapshotMemory s mem aw snap) (hsep : snap.toNat + 192 ≤ ptr.toNat)
    (hv : SettleValues locals s ptr) (hov : R.length + 17 ≤ 1024) :
    (∃ (evm' : EVM.State) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
        (locals' : Store) (mem' : ByteArray) (aw' : UInt256) (out : ByteArray) (k' C' : Nat),
      ExecStmt auctionConfig { contract := auctionContract, locals := locals } evm
        settleNounStmt (.ok { contract := auctionContract, locals := locals' } evm') ∧
      SettleValues locals' s ptr ∧ SourceState s0 I cA' σ' evm' ∧
      RD auctionBytecode I g s0 ⟨4647⟩ (snap :: ret :: R) mem' aw' out (cA', σ') k' C' ∧
      HeapMemory mem' aw' ptr ∧ SnapshotMemory s mem' aw' snap ∧
      MemoryPrefix mem mem' ptr.toNat ∧ aw.toNat ≤ aw'.toNat) ∨
    (ExecStmt auctionConfig { contract := auctionContract, locals := locals } evm
      settleNounStmt .reverted ∧ RDrev auctionBytecode g s0) := by
  have hn : loadedWord mem aw snap = s.nounId := by
    have hl : loadedWord mem aw (snap + ⟨0⟩) = s.nounId := hsm.load ⟨0, by decide⟩
    rwa [u256_add_comm snap ⟨0⟩, u256_zero_add] at hl
  have ha : expandedWords aw snap ⟨32⟩ = aw := by
    have hl : expandedWords aw (snap + ⟨0⟩) ⟨32⟩ = aw := hsm.expand_eq ⟨0, by decide⟩
    rwa [u256_add_comm snap ⟨0⟩, u256_zero_add] at hl
  by_cases hz : s.bidderWord = ⟨0⟩
  · have he := settleBidderGuardSource (evm := evm) hv.snapshot
    rw [decide_eq_true hz] at he
    have rd4435 := evm_run h with [jumpiNT hz]
    have hargs : evalExprs? auctionConfig { contract := auctionContract, locals := locals } evm
        [auctionMemField "nounId"] = .ok [.int (Int.ofNat s.nounId.toNat)] := by
      simp only [evalExprs?, snapshotNounSource hv.snapshot, pure, bind, EvalResult.bind]
    rcases burnRoutine rd4435 hs hperm hm (by omega) hn ha hv.nouns hargs (by omega) with
      ⟨evm', cA', σ', out, _, _, hsrc, hs', rd4647, hm', hp⟩ | ⟨hsrc, hr⟩
    · have hg := burnCallWords_mono hm (show ptr.toNat + 36 ≤ 2 ^ 200 by omega)
      exact Or.inl ⟨evm', cA', σ', _, _, _, out, _, _, ExecStmt.iteTrue he hsrc,
        hv.insertOther _ (by decide) (by decide) (by decide) (by decide) (by decide),
        hs', rd4647, hm', hsm.transport hp hsep hm'.active hg, hp, hg⟩
    · exact Or.inr ⟨ExecStmt.iteTrue he hsrc, hr⟩
  · have he := settleBidderGuardSource (evm := evm) hv.snapshot
    rw [decide_eq_false hz] at he
    have rd4536 := evm_run h with [jumpiT hz (by jump_dest)]
    have hbid : loadedWord mem aw (snap + ⟨128⟩) = s.bidderWord := hsm.load ⟨4, by decide⟩
    have hab : expandedWords aw (snap + ⟨128⟩) ⟨32⟩ = aw := hsm.expand_eq ⟨4, by decide⟩
    have hargs : evalExprs? auctionConfig { contract := auctionContract, locals := locals } evm
        [.env .this, auctionMemField "bidder", auctionMemField "nounId"] =
        .ok [.address I.codeOwner,
          .address (AccountAddress.ofNat (UInt256.land s.bidderWord solcAddrMask).toNat),
          .int (Int.ofNat s.nounId.toNat)] := by
      simp only [evalExprs?, evalExpr?, envValue, hs.env, snapshotBidderSource hv.snapshot,
        snapshotNounSource hv.snapshot, pure, bind, EvalResult.bind]
      rw [Snapshot.bidderWord, maskTwice]
    rcases nounTransferRoutine rd4536 hs hperm hm hb hn ha hbid hab hv.nouns hargs hov with
      ⟨evm', cA', σ', out, _, _, hsrc, hs', rd4647, hm', hp⟩ | ⟨hsrc, hr⟩
    · have hg := nounTransferCallWords_mono hm hb
      exact Or.inl ⟨evm', cA', σ', _, _, _, out, _, _, ExecStmt.iteFalse he hsrc,
        hv.insertOther _ (by decide) (by decide) (by decide) (by decide) (by decide),
        hs', rd4647, hm', hsm.transport hp hsep hm'.active hg, hp, hg⟩
    · exact Or.inr ⟨ExecStmt.iteFalse he hsrc, hr⟩

end Auction
