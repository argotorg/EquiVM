import Solm.Benchmarks.Auction.PaymentRoutine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def paymentParams (recipient amount ptr : UInt256) : Store :=
  (((∅ : Store).insert "_freePtr" (.int (Int.ofNat ptr.toNat))).insert
    "amount" (.int (Int.ofNat amount.toNat))).insert "to" (.address (paymentAddress recipient))

theorem paymentParams_bind (recipient amount ptr : UInt256) :
    bindParams? safeTransferETHWithFallback.params
      [.address (paymentAddress recipient), .int (Int.ofNat amount.toNat),
        .int (Int.ofNat ptr.toNat)] = some (paymentParams recipient amount ptr) := rfl

theorem paymentParams_values (recipient amount ptr : UInt256) :
    PaymentValues (paymentParams recipient amount ptr) recipient amount ptr := by
  unfold paymentParams
  exact ⟨store_get_self _ _ _,
    (store_get_ne _ _ (by decide)).trans (store_get_self _ _ _),
    (store_get_ne _ _ (by decide)).trans
      ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)), by simp⟩

theorem paymentLookup : lookupCallable? auctionContract "_safeTransferETHWithFallback" =
    some safeTransferETHWithFallback.toCallable := by rfl

theorem paymentInternalRoutine
    {I g s0 amount recipient ret R mem aw ptr rdata cA σ k C evm locals args retVar}
    (h : RD auctionBytecode I g s0 ⟨3337⟩ (amount :: recipient :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 2 ^ 140 ≤ 2 ^ 200)
    (hargs : evalExprs? auctionConfig { contract := auctionContract, locals := locals } evm args =
      .ok [.address (paymentAddress recipient), .int (Int.ofNat amount.toNat),
        .int (Int.ofNat ptr.toNat)])
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 24 ≤ 1024) :
    (∃ (evm' : EVM.State) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
        (mem' : ByteArray) (aw' ptr' : UInt256) (out : ByteArray) (k' C' : Nat),
      ExecStmt auctionConfig { contract := auctionContract, locals := locals } evm
        (.internalCall "_safeTransferETHWithFallback" args retVar)
        (.ok
          { contract := auctionContract
            locals := locals.insert retVar (.int (Int.ofNat ptr'.toNat)) } evm') ∧
      SourceState s0 I cA' σ' evm' ∧
      RD auctionBytecode I g s0 ret R mem' aw' out (cA', σ') k' C' ∧
      MemoryCursor mem' aw' ptr' ∧ MemoryPrefix mem mem' ptr.toNat ∧
      ptr.toNat ≤ ptr'.toNat ∧ ptr'.toNat ≤ ptr.toNat + 2 ^ 140 ∧ aw.toNat ≤ aw'.toNat) ∨
    (ExecStmt auctionConfig { contract := auctionContract, locals := locals } evm
      (.internalCall "_safeTransferETHWithFallback" args retVar) .reverted ∧
      RDrev auctionBytecode g s0) := by
  rcases paymentRoutine h hs hperm hm hb (paymentParams_values recipient amount ptr) hret hov with
    ⟨evm', cA', σ', calleeLocals, mem', aw', ptr', out, _, _, hsrc, hs', hr, hm', hp,
      hlo, hhi, hg⟩ | ⟨hsrc, hr⟩
  · exact Or.inl ⟨evm', cA', σ', mem', aw', ptr', out, _, _,
      internalCallFunctionReturn hargs paymentLookup (paymentParams_bind recipient amount ptr)
        hsrc, hs', hr, hm', hp, hlo, hhi, hg⟩
  · exact Or.inr ⟨internalCallFunctionRevert hargs paymentLookup
      (paymentParams_bind recipient amount ptr) hsrc, hr⟩

end Auction
