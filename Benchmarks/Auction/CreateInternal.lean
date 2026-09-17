import Benchmarks.Auction.CreateRoutine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def createParams (ptr : UInt256) : Store :=
  (∅ : Store).insert "_freePtr" (.int (Int.ofNat ptr.toNat))

theorem createParams_bind (ptr : UInt256) :
    bindParams? createAuctionFn.params [.int (Int.ofNat ptr.toNat)] = some (createParams ptr) := rfl

theorem createLookup : lookupCallable? auctionContract "_createAuction" =
    some createAuctionFn.toCallable := by rfl

theorem createInternalRoutine {I g s0 ret R mem aw ptr rdata cA σ k C evm locals args retVar}
    (h : RD auctionBytecode I g s0 ⟨3000⟩ (ret :: R) mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 2 ^ 140 ≤ 2 ^ 200)
    (hargs : evalExprs? auctionConfig { contract := auctionContract, locals := locals } evm args =
      .ok [.int (Int.ofNat ptr.toNat)])
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 19 ≤ 1024) :
    (∃ (evm' : EVM.State) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
        (mem' : ByteArray) (aw' : UInt256) (out : ByteArray) (k' C' : Nat),
      ExecStmt auctionConfig { contract := auctionContract, locals := locals } evm
        (.internalCall "_createAuction" args retVar)
        (.ok { contract := auctionContract, locals := locals.insert retVar .unit } evm') ∧
      SourceState s0 I cA' σ' evm' ∧
      RD auctionBytecode I g s0 ret R mem' aw' out (cA', σ') k' C') ∨
    (ExecStmt auctionConfig { contract := auctionContract, locals := locals } evm
      (.internalCall "_createAuction" args retVar) .reverted ∧ RDrev auctionBytecode g s0) := by
  have hp : (createParams ptr).get? "_freePtr" = some (.int (Int.ofNat ptr.toNat)) :=
    store_get_self _ _ _
  rcases createRoutine h hs hperm hm hb hp (by simp [createParams]) (by simp [createParams])
      (by simp [createParams]) (by simp [createParams]) hret hov with
    ⟨evm', cA', σ', calleeLocals, mem', aw', out, _, _, hsrc, hs', hr⟩ | ⟨hsrc, hr⟩
  · exact Or.inl ⟨evm', cA', σ', mem', aw', out, _, _,
      internalCallFunctionReturn hargs createLookup (createParams_bind ptr) hsrc, hs', hr⟩
  · exact Or.inr ⟨internalCallFunctionRevert hargs createLookup (createParams_bind ptr) hsrc, hr⟩

end Auction
