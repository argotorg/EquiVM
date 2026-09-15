import Benchmarks.Auction.SettleNoun
import Benchmarks.Auction.PaymentInternal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def settlePaymentStmt : Stmt :=
  .ite (.binary .gt (auctionMemField "amount") (.intLit 0))
    [.internalCall "_safeTransferETHWithFallback"
      [.storage ownerRef, auctionMemField "amount", .var "_freePtr"] "_freePtr"] []

theorem settleAmountGuardSource {evm locals s}
    (hs : locals.get? "_auction" = some (Snapshot.value s)) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.binary .gt (auctionMemField "amount") (.intLit 0)) =
      .ok (.bool (decide (s.amount ≠ ⟨0⟩))) := by
  simp only [evalExpr?, snapshotAmountSource hs, pure, bind, EvalResult.bind, evalBinaryOp?]
  congr 2
  congr 1
  apply propext
  constructor
  · intro hn hz
    rw [hz] at hn
    exact (show ¬ (Int.ofNat (⟨0⟩ : UInt256).toNat > 0) by decide) hn
  · intro hz
    have hn : s.amount.toNat ≠ 0 := fun he ↦ hz (u256_inj he)
    change (s.amount.toNat : Int) > 0
    omega

theorem settlePaymentArgs {s0 I cA σ evm locals s ptr}
    (hs : SourceState s0 I cA σ evm) (hv : SettleValues locals s ptr) :
    evalExprs? auctionConfig { contract := auctionContract, locals := locals } evm
      [.storage ownerRef, auctionMemField "amount", .var "_freePtr"] =
      .ok [.address (paymentAddress (ownerWord σ I)), .int (Int.ofNat s.amount.toNat),
        .int (Int.ofNat ptr.toNat)] := by
  have hw : ownerWord evm.accountMap evm.executionEnv = ownerWord σ I := by
    rw [hs.env, ownerWord_equiv hs.accounts]
  have ht : AccountAddress.ofNat (ownerWord σ I).toNat = paymentAddress (ownerWord σ I) := by
    rw [paymentAddress, solcAddrMask_clean (ownerWord_canonical σ I), addressOfWord_eq]
  simp only [evalExprs?, ownerRead evm locals hv.owner, snapshotAmountSource hv.snapshot,
    evalExpr?, hv.ptr, EvalResult.ofOption, hw, ht, pure, bind, EvalResult.bind]

theorem settlePaymentPrefix {I g s0 s snap ret R mem aw rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨4658⟩ (snap :: ret :: R) mem aw rdata (cA, σ) k C)
    (hm : SnapshotMemory s mem aw snap) (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨3337⟩
      (s.amount :: ownerWord σ I :: ⟨4688⟩ :: snap :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
  have rd4666 := evm_run h with [push2 ⟨4688⟩, push2 ⟨4678⟩, push1 ⟨151⟩]
  obtain ⟨_, _, rd4667⟩ := rd4666.sload (by native_decide) (by evm_ov)
  have rd4678 := evm_run rd4667 with [push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    and, swap1, jump (by jump_dest)]
  have hmask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  rw [hmask] at rd4678
  have rd4684 := evm_run rd4678 with [jumpdest, dup3, push1 ⟨32⟩, add,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  have hl : loadedWord mem aw (snap + ⟨32⟩) = s.amount := hm.load ⟨1, by decide⟩
  have ha : expandedWords aw (snap + ⟨32⟩) ⟨32⟩ = aw := hm.expand_eq ⟨1, by decide⟩
  rw [u256_add_comm ⟨32⟩ snap, hl, ha] at rd4684
  exact ⟨_, _, evm_run rd4684 with [push2 ⟨3337⟩, jump (by jump_dest)]⟩

theorem settlePaymentRoutine {I g s0 s snap ret R mem aw ptr rdata cA σ k C evm locals}
    (h : RD auctionBytecode I g s0 ⟨4647⟩ (snap :: ret :: R) mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 2 ^ 140 ≤ 2 ^ 200)
    (hsm : SnapshotMemory s mem aw snap) (hsep : snap.toNat + 192 ≤ ptr.toNat)
    (hv : SettleValues locals s ptr) (hov : R.length + 26 ≤ 1024) :
    (∃ (evm' : EVM.State) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
        (locals' : Store) (mem' : ByteArray) (aw' ptr' : UInt256) (out : ByteArray) (k' C' : Nat),
      ExecStmt auctionConfig { contract := auctionContract, locals := locals } evm
        settlePaymentStmt (.ok { contract := auctionContract, locals := locals' } evm') ∧
      SettleValues locals' s ptr' ∧ SourceState s0 I cA' σ' evm' ∧
      RD auctionBytecode I g s0 ⟨4688⟩ (snap :: ret :: R) mem' aw' out (cA', σ') k' C' ∧
      MemoryCursor mem' aw' ptr' ∧ SnapshotMemory s mem' aw' snap ∧
      MemoryPrefix mem mem' ptr.toNat ∧ ptr.toNat ≤ ptr'.toNat ∧
      ptr'.toNat ≤ ptr.toNat + 2 ^ 140 ∧ aw.toNat ≤ aw'.toNat) ∨
    (ExecStmt auctionConfig { contract := auctionContract, locals := locals } evm
      settlePaymentStmt .reverted ∧ RDrev auctionBytecode g s0) := by
  have hl : loadedWord mem aw (snap + ⟨32⟩) = s.amount := hsm.load ⟨1, by decide⟩
  have ha : expandedWords aw (snap + ⟨32⟩) ⟨32⟩ = aw := hsm.expand_eq ⟨1, by decide⟩
  have rd4653 := evm_run h with [jumpdest, push1 ⟨32⟩, dup2, add,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hl, ha] at rd4653
  have rd4657 := evm_run rd4653 with [iszero, push2 ⟨4688⟩]
  have he := settleAmountGuardSource (evm := evm) hv.snapshot
  by_cases hz : s.amount = ⟨0⟩
  · rw [decide_eq_false (not_not_intro hz)] at he
    have rd4688 := evm_run rd4657 with [jumpiT (by rw [hz]; decide) (by jump_dest)]
    exact Or.inl ⟨evm, cA, σ, locals, mem, aw, ptr, rdata, _, _,
      ExecStmt.iteFalse he ExecBlock.nil, hv, hs, rd4688, hm.cursor, hsm, .refl _ _,
      le_refl _, by omega, le_refl _⟩
  · rw [decide_eq_true hz] at he
    have rd4658 := evm_run rd4657 with [jumpiNT (isZero_eq_zero_of_ne hz)]
    obtain ⟨_, _, rd3337⟩ := settlePaymentPrefix rd4658 hsm (by omega)
    rcases paymentInternalRoutine rd3337 hs hperm hm hb (settlePaymentArgs hs hv)
        (by jump_dest) (by evm_ov) with
      ⟨evm', cA', σ', mem', aw', ptr', out, _, _, hsrc, hs', hr, hm', hp, hlo, hhi, hg⟩ |
        ⟨hsrc, hr⟩
    · exact Or.inl ⟨evm', cA', σ', _, mem', aw', ptr', out, _, _,
        ExecStmt.iteTrue he (ExecBlock.consNormal hsrc ExecBlock.nil), hv.setFree ptr',
        hs', hr, hm', hsm.transport hp hsep hm'.active hg, hp, hlo, hhi, hg⟩
    · exact Or.inr ⟨ExecStmt.iteTrue he (ExecBlock.consRevert hsrc), hr⟩

end Auction
