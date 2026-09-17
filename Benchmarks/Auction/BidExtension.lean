import Benchmarks.Auction.BidStorage
import Benchmarks.Auction.CheckedDivSub
import Benchmarks.Auction.SnapshotMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def bidExtendedExpr : Expr :=
  .binary .lt (.binary .sub (auctionMemField "endTime") now) (.storage timeBufferRef)

def bidExtendStmt : Stmt :=
  .ite (.var "extended")
    [.assign .storage (aField "endTime") (u256 (.binary .add now (.storage timeBufferRef)))] []

def bidExtendStmts : List Stmt :=
  [.letDecl "extended" (some boolTy) bidExtendedExpr, bidExtendStmt]

theorem bidTimeBufferSource {s0 I cA σ evm locals s noun}
    (hs : SourceState s0 I cA σ evm) (hv : BidValues locals s noun) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.storage timeBufferRef) = .ok (.int (Int.ofNat (storedWord σ I ⟨203⟩).toNat)) := by
  rw [timeBufferRef, scalarRead evm locals "timeBuffer" (.int uint256Int)
    (auctionUint256Loc ⟨203⟩) (hv.storage _ (by decide)) (by native_decide) rfl,
    loadUint256, hs.storageRead]

theorem bidExtendedSource {s0 I cA σ evm locals s noun}
    (hs : SourceState s0 I cA σ evm) (hv : BidValues locals s noun)
    (ht : (UInt256.ofNat I.header.timestamp).toNat ≤ s.endTime.toNat) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      bidExtendedExpr = .ok (.bool (decide
        ((UInt256.sub s.endTime (UInt256.ofNat I.header.timestamp)).toNat <
          (storedWord σ I ⟨203⟩).toNat))) := by
  have hsub := subSourceOk (snapshotEndSource (evm := evm) hv.snapshot)
    (rhs := now) (by simp only [now, evalExpr?, envValue, hs.env, pure]) ht
  simp only [bidExtendedExpr, evalExpr?, hsub, bidTimeBufferSource hs hv,
    bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast, Int.ofNat_lt]

theorem bidExtensionPrefix {I g s0 s bidder snap noun ret R mem aw rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨1738⟩ (bidder :: snap :: noun :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hm : SnapshotMemory s mem aw snap)
    (ht : (UInt256.ofNat I.header.timestamp).toNat ≤ s.endTime.toNat)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨1768⟩
      (⟨1792⟩ :: UInt256.isZero (UInt256.lt
          (UInt256.sub s.endTime (UInt256.ofNat I.header.timestamp)) (storedWord σ I ⟨203⟩)) ::
        UInt256.lt (UInt256.sub s.endTime (UInt256.ofNat I.header.timestamp))
          (storedWord σ I ⟨203⟩) :: bidder :: snap :: noun :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
  have rd1740 := evm_run h with [push1 ⟨203⟩]
  obtain ⟨_, _, rd1741⟩ := rd1740.sload (by native_decide) (by evm_ov)
  have rd1746 := evm_run rd1741 with [push1 ⟨96⟩, dup4, add,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  have hl : loadedWord mem aw (snap + ⟨96⟩) = s.endTime := hm.load ⟨3, by decide⟩
  have ha : expandedWords aw (snap + ⟨96⟩) ⟨32⟩ = aw := hm.expand_eq ⟨3, by decide⟩
  rw [hl, ha] at rd1746
  have rd5723 := evm_run rd1746 with [push0, swap2, swap1, push2 ⟨1759⟩, swap1,
    timestamp, swap1, push2 ⟨5723⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd1759⟩ := checkedSubOk rd5723 ht (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd1759 with [jumpdest, lt, swap1, pop, dup1, iszero, push2 ⟨1792⟩]⟩

theorem bidExtensionRoutine {I g s0 s bidder snap noun ret R mem aw rdata cA σ k C evm locals}
    (h : RD auctionBytecode I g s0 ⟨1738⟩ (bidder :: snap :: noun :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hm : SnapshotMemory s mem aw snap) (hv : BidValues locals s noun)
    (ht : (UInt256.ofNat I.header.timestamp).toNat < s.endTime.toNat)
    (hov : R.length + 13 ≤ 1024) :
    (∃ (evm' : EVM.State) (σ' : AccountMap) (locals' : Store) (extended : UInt256)
        (mem' : ByteArray) (aw' : UInt256) (k' C' : Nat),
      ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
        bidExtendStmts (.ok { contract := auctionContract, locals := locals' } evm') ∧
      BidValues locals' s noun ∧ SourceState s0 I cA σ' evm' ∧
      RD auctionBytecode I g s0 ⟨1792⟩ (extended :: bidder :: snap :: noun :: ret :: R)
        mem' aw' rdata (cA, σ') k' C') ∨
    (ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
      bidExtendStmts .reverted ∧ RDrev auctionBytecode g s0) := by
  obtain ⟨_, _, rd1768⟩ := bidExtensionPrefix h hm (by omega) hov
  have he := bidExtendedSource hs hv (by omega)
  by_cases hex : (UInt256.sub s.endTime (UInt256.ofNat I.header.timestamp)).toNat <
      (storedWord σ I ⟨203⟩).toNat
  · rw [decide_eq_true hex] at he
    rw [ult_one hex] at rd1768
    have rd1769 := evm_run rd1768 with [jumpiNT (by decide)]
    have rd1771 := evm_run rd1769 with [push1 ⟨203⟩]
    obtain ⟨_, _, rd1772⟩ := rd1771.sload (by native_decide) (by evm_ov)
    change RD _ _ _ _ ⟨1772⟩
      (storedWord σ I ⟨203⟩ :: ⟨1⟩ :: bidder :: snap :: noun :: ret :: R)
      mem aw rdata (cA, σ) _ _ at rd1772
    have rd5704 := evm_run rd1772 with [push2 ⟨1781⟩, swap1, timestamp,
      push2 ⟨5704⟩, jump (by jump_dest)]
    let locals1 := locals.insert "extended" (.bool true)
    have hv1 : BidValues locals1 s noun := hv.insertOther _ (by decide) (by decide) (by decide)
    have hvar : evalExpr? auctionConfig { contract := auctionContract, locals := locals1 } evm
        (.var "extended") = .ok (.bool true) := by
      simp only [evalExpr?, locals1, store_get_self, EvalResult.ofOption]
    have hn : evalExpr? auctionConfig { contract := auctionContract, locals := locals1 } evm now =
        .ok (.int (Int.ofNat (UInt256.ofNat I.header.timestamp).toNat)) := by
      simp only [now, evalExpr?, envValue, hs.env, pure]
    by_cases hno : (UInt256.ofNat I.header.timestamp).toNat + (storedWord σ I ⟨203⟩).toNat <
        UInt256.size
    · have ha := checkedAddSourceOk hn (bidTimeBufferSource hs hv1) hno
      obtain ⟨_, _, rd1781⟩ := checkedAddOk rd5704 hno (by jump_dest) (by evm_ov)
      rw [u256_add_comm (storedWord σ I ⟨203⟩)] at rd1781
      have rd1791 := evm_run rd1781 with [jumpdest, push1 ⟨96⟩, dup5, add, dup2, swap1,
        raw mstoreSymbolic (by native_decide) (by evm_ov), push1 ⟨210⟩]
      obtain ⟨_, _, rd1792⟩ := rd1791.sstore hperm (by native_decide) (by evm_ov)
      let finish := UInt256.ofNat I.header.timestamp + storedWord σ I ⟨203⟩
      let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨210⟩ finish
      have hs' : SourceState s0 I cA (sstoreAccountMap I.codeOwner σ ⟨210⟩ finish) evm' := by
        simpa only [evm', hs.env] using hs.storageWrite ⟨210⟩ finish
      refine Or.inl ⟨evm', _, locals1, ⟨1⟩, _, _, _, _, ?_, hv1, hs', rd1792⟩
      apply ExecBlock.consNormal (ExecStmt.letDecl he)
      refine ExecBlock.consNormal (ExecStmt.iteTrue hvar ?_) ExecBlock.nil
      exact ExecBlock.consNormal (ExecStmt.assign ha
        (auctionFieldWrite evm evm' locals1 "endTime" (.elem (.int uint256Int))
          (auctionUint256Loc ⟨210⟩) _ (hv1.storage _ (by decide)) (by native_decide) rfl
          (by trivial) (storageLocStore_uint256 evm ⟨210⟩ finish))) ExecBlock.nil
    · have ha := checkedAddSourceOverflow hn (bidTimeBufferSource hs hv1) (by omega)
      refine Or.inr ⟨?_, checkedAddOverflow rd5704 (by omega) (by evm_ov)⟩
      apply ExecBlock.consNormal (ExecStmt.letDecl he)
      exact ExecBlock.consRevert
        (ExecStmt.iteTrue hvar (ExecBlock.consRevert (ExecStmt.assignExprRevert ha)))
  · rw [decide_eq_false hex] at he
    rw [ult_zero (by omega)] at rd1768
    have rd1792 := evm_run rd1768 with [jumpiT (by decide) (by jump_dest)]
    let locals1 := locals.insert "extended" (.bool false)
    have hv1 : BidValues locals1 s noun := hv.insertOther _ (by decide) (by decide) (by decide)
    refine Or.inl ⟨evm, σ, locals1, ⟨0⟩, mem, aw, _, _, ?_, hv1, hs, rd1792⟩
    apply ExecBlock.consNormal (ExecStmt.letDecl he)
    apply ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil) ExecBlock.nil
    simp only [evalExpr?, store_get_self, EvalResult.ofOption]

end Auction
