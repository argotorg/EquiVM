import Benchmarks.Auction.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

theorem minBidIncrementPercentageBodyReturns (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? "minBidIncrementPercentage" = none) :
    ExecTransitionBody auctionConfig auctionContract evm locals minBidIncGetter.body
      (.returned { contract := auctionContract, locals := locals } evm
        (some [.int (Int.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat)])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns (by
      rw [minBidIncRef, scalarRead evm locals "minBidIncrementPercentage"
        (.int uint8Int) (auctionUint8LocAt ⟨205⟩ 0) hbase (by native_decide) rfl, loadUint8])

theorem minBidIncrementPercentageEncode {ee g s0 val R rdata acc k C}
    (h : RD auctionBytecode ee g s0 ⟨810⟩ (val :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 5 ≤ 1024) :
    RDret auctionBytecode g s0 acc (UInt256.toByteArray (UInt256.land val ⟨255⟩)) := by
  have rd318 := evm_run h with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
      solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push1 ⟨255⟩, swap1, swap2, and, dup2,
    raw mstore 6 (solcReturnMem (UInt256.land val ⟨255⟩)) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨318⟩, jump (by jump_dest) ]
  exact rd318.auctionReturn32 hov

theorem minBidIncrementPercentageX {cA gh bl σ σ₀ A I} {g : UInt256}
    (hreach : EntryReached 14 cA gh bl σ σ₀ A I g) (hwv : I.weiValue = ⟨0⟩) :
    RDret auctionBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (cA, σ)
      (UInt256.toByteArray (UInt256.land (storedWord σ I ⟨205⟩) ⟨255⟩)) := by
  obtain ⟨_, _, rd785⟩ := hreach
  obtain ⟨_, _, rd798⟩ := entryGuardZero 14 (by decide) rd785 hwv
  have rd800 := evm_run rd798 with [push1 ⟨205⟩]
  obtain ⟨_, _, rd801⟩ := rd800.sload (by native_decide) (by evm_ov)
  have rd810 := evm_run rd801 with [
    push2 ⟨810⟩, swap1, push1 ⟨255⟩, and, dup2, jump (by jump_dest) ]
  have hret := minBidIncrementPercentageEncode
    (val := UInt256.land ⟨255⟩ (storedWord σ I ⟨205⟩)) rd810 (by evm_ov)
  simpa only [u256_land_comm ⟨255⟩ (storedWord σ I ⟨205⟩), maskTwice] using hret

theorem minBidIncrementPercentageBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = auctionBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I (entryBytes 14))
    (hreach : EntryReached 14 cA gh bl σ_evm σ₀ A I g)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor auctionConfig auctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hsz := calldata_size_ge_of_selIs I (entryBytes 14) (entryBytes_size 14) hsel
    have hd := dispatchEntry 14 hsel
    have hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
        (minBidIncGetter.params.map Param.name)
        (transitionSignature minBidIncGetter).paramTypes I.calldata = some ∅ :=
      decodeCalldata_empty_ok hsz
    have hword := storedWord_equiv hAccounts I ⟨205⟩
    have hbody : ExecTransitionBody auctionConfig auctionContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ minBidIncGetter.body
        (.returned { contract := auctionContract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [.int (Int.ofNat (UInt256.land (storedWord σ_solm I ⟨205⟩) ⟨255⟩).toNat)])) := by
      simpa [storedWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
        minBidIncrementPercentageBodyReturns
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ hwv (by simp)
    exact (minBidIncrementPercentageX hreach hwv).reEquivExecutionTransport
      hcode hd hdec hbody (by rw [hword]) hAccounts
      (returnEquiv_of_encode (uint8ReturnEncoding
        (UInt256.land (storedWord σ_evm I ⟨205⟩) ⟨255⟩) (lowByte_bound _)))
  · exact entryNonpayableRevert 14 (by decide) hcode hsel hreach hwv

end Auction
