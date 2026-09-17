import Benchmarks.Auction.NounSource
import Benchmarks.Auction.NounTransferCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def settleBurnStmts : List Stmt :=
  checkedExternalCallStmts (.storage nounsRef) "burn" (.intLit 0) [auctionMemField "nounId"] "_burn"

def settleTransferStmts : List Stmt :=
  checkedExternalCallStmts (.storage nounsRef) "transferFrom" (.intLit 0)
    [.env .this, auctionMemField "bidder", auctionMemField "nounId"] "_tf"

theorem burnRoutine {I g s0 snap nounId ret R mem aw ptr rdata cA σ k C evm locals}
    (h : RD auctionBytecode I g s0 ⟨4435⟩ (snap :: ret :: R) mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 36 ≤ 2 ^ 200)
    (hn : loadedWord mem aw snap = nounId) (ha : expandedWords aw snap ⟨32⟩ = aw)
    (hbase : locals.get? "nouns" = none)
    (hargs : evalExprs? auctionConfig { contract := auctionContract, locals := locals } evm
      [auctionMemField "nounId"] = .ok [.int (Int.ofNat nounId.toNat)])
    (hov : R.length + 16 ≤ 1024) :
    (∃ (evm' : EVM.State) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
        (out : ByteArray) (k' C' : Nat),
      ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
        settleBurnStmts
        (.ok { contract := auctionContract, locals := locals.insert "_burn" (collapseReturns []) }
          evm') ∧
      SourceState s0 I cA' σ' evm' ∧
      RD auctionBytecode I g s0 ⟨4647⟩ (snap :: ret :: R)
        (callMem1 mem ptr burnWord nounId) (burnCallWords aw ptr) out (cA', σ') k' C' ∧
      HeapMemory (callMem1 mem ptr burnWord nounId) (burnCallWords aw ptr) ptr ∧
      MemoryPrefix mem (callMem1 mem ptr burnWord nounId) ptr.toNat) ∨
    (ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
      settleBurnStmts .reverted ∧ RDrev auctionBytecode g s0) := by
  by_cases hcode : extCodeSizeWord σ (nounsWord σ I) = ⟨0⟩
  · exact Or.inr ⟨checkedNounSourceNoCode hs hbase hcode, burnNoCode h hm hb hn ha hcode hov⟩
  · obtain ⟨evm', cA', σ', z, out, _, _, hc, hs', rd4513, _⟩ :=
      burnCall h hs hperm hm hb hn ha hcode hov
    cases z with
    | false =>
      exact Or.inr ⟨checkedNounSourceFailure hs hbase hcode hargs (burnData_encode nounId) hc,
        burnAfterFailure rd4513 (by omega)⟩
    | true =>
      obtain ⟨_, _, rd4647⟩ := burnAfterSuccess rd4513 (by omega)
      exact Or.inl ⟨evm', cA', σ', out, _, _,
        checkedNounSourceSuccess hs hbase hcode hargs (burnData_encode nounId) hc rfl,
        hs', rd4647, burnCall_heap hm nounId hb, callMem1_prefix hm burnWord nounId⟩

theorem nounTransferRoutine {I g s0 snap nounId bidder ret R mem aw ptr rdata cA σ k C evm locals}
    (h : RD auctionBytecode I g s0 ⟨4536⟩ (snap :: ret :: R) mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 100 ≤ 2 ^ 200)
    (hn : loadedWord mem aw snap = nounId) (ha : expandedWords aw snap ⟨32⟩ = aw)
    (hbid : loadedWord mem aw (snap + ⟨128⟩) = bidder)
    (hab : expandedWords aw (snap + ⟨128⟩) ⟨32⟩ = aw)
    (hbase : locals.get? "nouns" = none)
    (hargs : evalExprs? auctionConfig { contract := auctionContract, locals := locals } evm
      [.env .this, auctionMemField "bidder", auctionMemField "nounId"] =
      .ok [.address I.codeOwner,
        .address (AccountAddress.ofNat (UInt256.land bidder solcAddrMask).toNat),
        .int (Int.ofNat nounId.toNat)]) (hov : R.length + 17 ≤ 1024) :
    (∃ (evm' : EVM.State) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
        (out : ByteArray) (k' C' : Nat),
      ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
        settleTransferStmts
        (.ok { contract := auctionContract, locals := locals.insert "_tf" (collapseReturns []) }
          evm') ∧
      SourceState s0 I cA' σ' evm' ∧
      RD auctionBytecode I g s0 ⟨4647⟩ (snap :: ret :: R)
        (callMem3 mem ptr transferFromWord (contractAddressWord I) (UInt256.land bidder
          solcAddrMask)
          nounId) (nounTransferCallWords aw ptr) out (cA', σ') k' C' ∧
      HeapMemory (callMem3 mem ptr transferFromWord (contractAddressWord I)
        (UInt256.land bidder solcAddrMask) nounId) (nounTransferCallWords aw ptr) ptr ∧
      MemoryPrefix mem (callMem3 mem ptr transferFromWord (contractAddressWord I)
        (UInt256.land bidder solcAddrMask) nounId) ptr.toNat) ∨
    (ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
      settleTransferStmts .reverted ∧ RDrev auctionBytecode g s0) := by
  by_cases hcode : extCodeSizeWord σ (nounsWord σ I) = ⟨0⟩
  · exact Or.inr ⟨checkedNounSourceNoCode hs hbase hcode,
      nounTransferNoCode h hm hb hn ha hbid hab hcode hov⟩
  · obtain ⟨evm', cA', σ', z, out, _, _, hc, hs', rd4628, _⟩ :=
      nounTransferCall h hs hperm hm hb hn ha hbid hab hcode hov
    cases z with
    | false =>
      exact Or.inr ⟨checkedNounSourceFailure hs hbase hcode hargs
        (nounTransferData_encode I bidder nounId) hc, nounTransferAfterFailure rd4628 (by omega)⟩
    | true =>
      obtain ⟨_, _, rd4647⟩ := nounTransferAfterSuccess rd4628 (by omega)
      exact Or.inl ⟨evm', cA', σ', out, _, _,
        checkedNounSourceSuccess hs hbase hcode hargs (nounTransferData_encode I bidder nounId)
          hc rfl,
        hs', rd4647, nounTransferCall_heap hm I bidder nounId hb,
        callMem3_prefix hm transferFromWord (contractAddressWord I)
          (UInt256.land bidder solcAddrMask) nounId⟩

end Auction
