import Solm.Benchmarks.Auction.SettleRoutine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def settleParams (ptr : UInt256) : Store :=
  (∅ : Store).insert "_freePtr" (.int (Int.ofNat ptr.toNat))

theorem settleParams_bind (ptr : UInt256) :
    bindParams? settleAuctionFn.params [.int (Int.ofNat ptr.toNat)] = some (settleParams ptr) := rfl

theorem settleLookup : lookupCallable? auctionContract "_settleAuction" =
    some settleAuctionFn.toCallable := by rfl

theorem settleInternalRoutine {I g s0 ret R mem aw ptr rdata cA σ k C evm locals args retVar}
    (h : RD auctionBytecode I g s0 ⟨4086⟩ (ret :: R) mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 2 ^ 142 ≤ 2 ^ 200)
    (hargs : evalExprs? auctionConfig { contract := auctionContract, locals := locals } evm args =
      .ok [.int (Int.ofNat ptr.toNat)])
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 26 ≤ 1024) :
    (∃ (evm' : EVM.State) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
        (mem' : ByteArray) (aw' ptr' : UInt256) (out : ByteArray) (k' C' : Nat),
      ExecStmt auctionConfig { contract := auctionContract, locals := locals } evm
        (.internalCall "_settleAuction" args retVar)
        (.ok
          { contract := auctionContract
            locals := locals.insert retVar (.int (Int.ofNat ptr'.toNat)) } evm') ∧
      SourceState s0 I cA' σ' evm' ∧
      RD auctionBytecode I g s0 ret R mem' aw' out (cA', σ') k' C' ∧
      HeapMemory mem' aw' ptr' ∧ MemoryPrefix mem mem' ptr.toNat ∧
      ptr.toNat ≤ ptr'.toNat ∧ ptr'.toNat ≤ ptr.toNat + 2 ^ 141 ∧ aw.toNat ≤ aw'.toNat) ∨
    (ExecStmt auctionConfig { contract := auctionContract, locals := locals } evm
      (.internalCall "_settleAuction" args retVar) .reverted ∧ RDrev auctionBytecode g s0) := by
  have hp : (settleParams ptr).get? "_freePtr" = some (.int (Int.ofNat ptr.toNat)) :=
    store_get_self _ _ _
  rcases settleRoutine h hs hperm hm hb hp (by simp [settleParams]) (by simp [settleParams])
      (by simp [settleParams]) hret hov with
    ⟨evm', cA', σ', calleeLocals, mem', aw', ptr', out, _, _, hsrc, hs', hr, hm', hp',
      hlo, hhi, hg⟩ | ⟨hsrc, hr⟩
  · exact Or.inl ⟨evm', cA', σ', mem', aw', ptr', out, _, _,
      internalCallFunctionReturn hargs settleLookup (settleParams_bind ptr) hsrc,
      hs', hr, hm', hp', hlo, hhi, hg⟩
  · exact Or.inr ⟨internalCallFunctionRevert hargs settleLookup (settleParams_bind ptr) hsrc, hr⟩

end Auction
