import Benchmarks.Auction.BidSource
import Benchmarks.Auction.PaymentInternal
import Benchmarks.Auction.SnapshotMemory
import Benchmarks.Auction.AddressSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def bidRefundStmt : Stmt :=
  .ite (.binary .ne (.var "lastBidder") zeroAddr)
    [.internalCall "_safeTransferETHWithFallback"
      [.var "lastBidder", auctionMemField "amount", .intLit 320] "_refund"] []

def bidRefundStmts : List Stmt :=
  [.letDecl "lastBidder" (some addr) (auctionMemField "bidder"), bidRefundStmt]

theorem bidRefundRoutine {I g s0 s noun ret R mem aw rdata cA σ k C evm locals}
    (h : RD auctionBytecode I g s0 ⟨1681⟩ (⟨128⟩ :: noun :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hm : HeapMemory mem aw ⟨320⟩) (hsm : SnapshotMemory s mem aw ⟨128⟩)
    (hv : BidValues locals s noun) (hov : R.length + 28 ≤ 1024) :
    (∃ (evm' : EVM.State) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
        (locals' : Store) (mem' : ByteArray) (aw' ptr' : UInt256) (out : ByteArray) (k' C' : Nat),
      ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
        bidRefundStmts (.ok { contract := auctionContract, locals := locals' } evm') ∧
      BidValues locals' s noun ∧ SourceState s0 I cA' σ' evm' ∧
      RD auctionBytecode I g s0 ⟨1715⟩ (s.bidderWord :: ⟨128⟩ :: noun :: ret :: R)
        mem' aw' out (cA', σ') k' C' ∧
      MemoryCursor mem' aw' ptr' ∧ SnapshotMemory s mem' aw' ⟨128⟩ ∧
      320 ≤ ptr'.toNat ∧ ptr'.toNat ≤ 320 + 2 ^ 140) ∨
    (ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
      bidRefundStmts .reverted ∧ RDrev auctionBytecode g s0) := by
  let locals1 := locals.insert "lastBidder" (.address (AccountAddress.ofNat s.bidderWord.toNat))
  have hv1 : BidValues locals1 s noun :=
    hv.insertOther _ (by decide) (by decide) (by decide)
  have hb : evalExpr? auctionConfig { contract := auctionContract, locals := locals1 } evm
      (.var "lastBidder") = .ok (.address (AccountAddress.ofNat s.bidderWord.toNat)) := by
    simp only [evalExpr?, locals1, store_get_self, EvalResult.ofOption]
  have hlet := ExecStmt.letDecl (ty := some addr) (name := "lastBidder")
    (snapshotBidderSource (evm := evm) hv.snapshot)
  have hl : loadedWord mem aw (⟨128⟩ + ⟨128⟩) = s.bidderWord := hsm.load ⟨4, by decide⟩
  have ha : expandedWords aw (⟨128⟩ + ⟨128⟩) ⟨32⟩ = aw := hsm.expand_eq ⟨4, by decide⟩
  have rd1687 := evm_run h with [jumpdest, push1 ⟨128⟩, dup2, add,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hl, ha] at rd1687
  have rd1701 := evm_run rd1687 with [push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup2, and, iszero, push2 ⟨1715⟩]
  have hmask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  rw [hmask, Snapshot.bidderWord, maskTwice] at rd1701
  change RD _ _ _ _ ⟨1701⟩
    (⟨1715⟩ :: UInt256.isZero s.bidderWord :: s.bidderWord :: ⟨128⟩ :: noun :: ret :: R)
    mem aw rdata (cA, σ) _ _ at rd1701
  by_cases hz : s.bidderWord = ⟨0⟩
  · have he := evalAddressNeZero_false hb (by rw [hz]; rfl)
    have rd1715 := evm_run rd1701 with [jumpiT (by rw [hz]; decide) (by jump_dest)]
    exact Or.inl ⟨evm, cA, σ, locals1, mem, aw, ⟨320⟩, rdata, _, _,
      ExecBlock.consNormal hlet
        (ExecBlock.consNormal (ExecStmt.iteFalse he ExecBlock.nil) ExecBlock.nil),
      hv1, hs, rd1715, hm.cursor, hsm, by decide, by decide⟩
  · have he := evalAddressNeZero_true hb
      (fun he ↦ hz ((canonicalAddress_eq_zero_iff s.bidderWord
        (solcAddrMask_result_canonical s.packed)).mp he))
    have rd1702 := evm_run rd1701 with [jumpiNT (isZero_eq_zero_of_ne hz)]
    have rd1711 := evm_run rd1702 with [push2 ⟨1715⟩, dup2, dup4, push1 ⟨32⟩, add,
      raw mloadSymbolic (by native_decide) (by evm_ov)]
    have hl1 : loadedWord mem aw (⟨128⟩ + ⟨32⟩) = s.amount := hsm.load ⟨1, by decide⟩
    have ha1 : expandedWords aw (⟨128⟩ + ⟨32⟩) ⟨32⟩ = aw := hsm.expand_eq ⟨1, by decide⟩
    rw [show (⟨32⟩ : UInt256) + ⟨128⟩ = ⟨128⟩ + ⟨32⟩ by decide, hl1, ha1] at rd1711
    have rd3337 := evm_run rd1711 with [push2 ⟨3337⟩, jump (by jump_dest)]
    have hargs : evalExprs? auctionConfig { contract := auctionContract, locals := locals1 } evm
        [.var "lastBidder", auctionMemField "amount", .intLit 320] =
        .ok [.address (paymentAddress s.bidderWord), .int (Int.ofNat s.amount.toNat),
          .int (Int.ofNat (⟨320⟩ : UInt256).toNat)] := by
      simp only [evalExprs?, hb, snapshotAmountSource hv1.snapshot, evalExpr?, pure,
        bind, EvalResult.bind, paymentAddress, Snapshot.bidderWord, maskTwice, addressOfWord_eq]
      rfl
    rcases paymentInternalRoutine rd3337 hs hperm hm (by decide) hargs
        (retVar := "_refund") (by jump_dest) (by evm_ov) with
      ⟨evm', cA', σ', mem', aw', ptr', out, _, _, hsrc, hs', hr, hm', hp, hlo, hhi, hg⟩ |
        ⟨hsrc, hr⟩
    · exact Or.inl ⟨evm', cA', σ', _, mem', aw', ptr', out, _, _,
        ExecBlock.consNormal hlet
          (ExecBlock.consNormal (ExecStmt.iteTrue he (ExecBlock.consNormal hsrc ExecBlock.nil))
            ExecBlock.nil),
        hv1.insertOther _ (by decide) (by decide) (by decide), hs', hr, hm',
        hsm.transport hp (by decide) hm'.active hg, hlo, hhi⟩
    · exact Or.inr ⟨ExecBlock.consNormal hlet
        (ExecBlock.consRevert (ExecStmt.iteTrue he (ExecBlock.consRevert hsrc))), hr⟩

end Auction
