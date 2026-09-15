import Benchmarks.Auction.UnpauseCondition
import Benchmarks.Auction.CreateInternal
import Benchmarks.Auction.OwnershipRoutine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def unpauseCreateStmt : Stmt :=
  .ite unpauseCreateExpr [.internalCall "_createAuction" [.intLit 128] "_c"] []

theorem unpauseAfterRoutine {I g s0 ret R mem aw rdata cA σ k C evm}
    (h : RD auctionBytecode I g s0 ⟨1126⟩ (ret :: R) mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hm : HeapMemory mem aw ⟨128⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 20 ≤ 1024) :
    (∃ (evm' : EVM.State) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
        (locals' : Store) (mem' : ByteArray) (aw' : UInt256) (out : ByteArray) (k' C' : Nat),
      ExecStmt auctionConfig { contract := auctionContract, locals := ∅ } evm unpauseCreateStmt
        (.ok { contract := auctionContract, locals := locals' } evm') ∧
      SourceState s0 I cA' σ' evm' ∧
      RD auctionBytecode I g s0 ret R mem' aw' out (cA', σ') k' C') ∨
    (ExecStmt auctionConfig { contract := auctionContract, locals := ∅ } evm
      unpauseCreateStmt .reverted ∧ RDrev auctionBytecode g s0) := by
  have he := unpauseCreateSource (locals := ∅) hs (by simp)
  obtain ⟨_, _, rd1150⟩ := unpauseCondition h (by evm_ov)
  by_cases hn : UnpauseCreates σ I
  · rw [decide_eq_true hn] at he
    have hw := (unpauseCreateWord_nonzero σ I).mpr hn
    have rd3000 := evm_run rd1150 with [jumpdest, iszero, push2 ⟨1163⟩,
      jumpiNT (isZero_eq_zero_of_ne hw), push2 ⟨1163⟩, push2 ⟨3000⟩, jump (by jump_dest)]
    have hargs : evalExprs? auctionConfig { contract := auctionContract, locals := ∅ }
        evm [.intLit 128] = .ok [.int (Int.ofNat (⟨128⟩ : UInt256).toNat)] := by
      simp only [evalExprs?, evalExpr?, pure, bind, EvalResult.bind]
      rfl
    rcases createInternalRoutine rd3000 hs hperm hm
        (by change 128 + 2 ^ 140 ≤ 2 ^ 200; decide) hargs (retVar := "_c")
        (by jump_dest) (by evm_ov) with
      ⟨evm', cA', σ', mem', aw', out, _, _, hcall, hs', rd1163⟩ | ⟨hcall, hr⟩
    · obtain ⟨_, _, rdret⟩ := auctionInternalReturn rd1163 hret (by evm_ov)
      exact Or.inl ⟨evm', cA', σ', _, mem', aw', out, _, _,
        ExecStmt.iteTrue he (ExecBlock.consNormal hcall ExecBlock.nil), hs', rdret⟩
    · exact Or.inr ⟨ExecStmt.iteTrue he (ExecBlock.consRevert hcall), hr⟩
  · rw [decide_eq_false hn] at he
    have hw : unpauseCreateWord σ I = ⟨0⟩ := by
      by_contra hne
      exact hn ((unpauseCreateWord_nonzero σ I).mp hne)
    have rd1163 := evm_run rd1150 with [jumpdest, iszero, push2 ⟨1163⟩,
      jumpiT (by rw [hw]; decide) (by jump_dest)]
    obtain ⟨_, _, rdret⟩ := auctionInternalReturn rd1163 hret (by evm_ov)
    exact Or.inl ⟨evm, cA, σ, ∅, mem, aw, rdata, _, _,
      ExecStmt.iteFalse he ExecBlock.nil, hs, rdret⟩

end Auction
