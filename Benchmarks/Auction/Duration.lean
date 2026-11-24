import Benchmarks.Auction.Storage

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

theorem durationBodyReturns (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hbase : locals.get? "duration" = none) :
    ExecTransitionBody fork auctionConfig auctionContract evm locals durationGetter.body
      (.returned { contract := auctionContract, locals := locals } evm
        (some [.int (Int.ofNat
          (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨206⟩).toNat)])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns (by
      rw [durationRef, scalarRead evm locals "duration" (.int uint256Int) (auctionUint256Loc ⟨206⟩)
        hbase (by native_decide) rfl, loadUint256])

theorem durationX {σ σ₀ A I} {g : UInt256}
    (hreach : EntryReached fork 0 σ σ₀ A I g) (hwv : I.weiValue = ⟨0⟩) :
    RDret fork auctionBytecode (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ
      (UInt256.toByteArray (solcSlotWord σ I ⟨206⟩)) := by
  obtain ⟨_, _, rd287⟩ := hreach
  obtain ⟨_, _, rd300⟩ := entryGuardZero 0 (by decide) rd287 hwv
  have rd305 := evm_run rd300 with [push2 ⟨308⟩, push1 ⟨206⟩]
  obtain ⟨_, _, rd306⟩ := rd305.sload (by native_decide) (by evm_ov)
  have rd308 := evm_run rd306 with [dup2, jump (by jump_dest)]
  exact rd308.auctionReturnWord (by evm_ov)

theorem durationBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = auctionBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (entryBytes 0))
    (hreach : EntryReached fork 0 σ σ₀ A I g) :
    runtimeRefinementFor fork auctionConfig auctionContract σ σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hsz := calldata_size_ge_of_selIs I (entryBytes 0) (entryBytes_size 0) hsel
    have hd := dispatchEntry 0 hsel
    have hdec : auctionConfig.externalABI.decodeCalldata?
        (durationGetter.params.map Param.name)
        (transitionSignature durationGetter).paramTypes I.calldata = some ∅ :=
      decodeCalldata_empty_ok hsz
    have hbody : ExecTransitionBody fork auctionConfig auctionContract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ durationGetter.body
        (.returned { contract := auctionContract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [.int (Int.ofNat (solcSlotWord σ I ⟨206⟩).toNat)])) := by
      simpa [solcSlotWord, initState, Stele.EVM.storageLoad, State.lookupAccount] using
        durationBodyReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          ∅ hwv (by simp)
    exact (durationX hreach hwv).reEquivExecution hcode hd hdec hbody
      (returnEquiv_of_encode (uint256ReturnEncoding (solcSlotWord σ I ⟨206⟩)))
  · exact entryNonpayableRevert 0 (by decide) hcode hsel hreach hwv

end Auction
