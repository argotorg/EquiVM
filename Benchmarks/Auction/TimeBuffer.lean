import Benchmarks.Auction.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

theorem timeBufferBodyReturns (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hbase : locals.get? "timeBuffer" = none) :
    ExecTransitionBody auctionConfig auctionContract evm locals timeBufferGetter.body
      (.returned { contract := auctionContract, locals := locals } evm
        (some [.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨203⟩).toNat)])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns (by
      rw [timeBufferRef, scalarRead evm locals "timeBuffer" (.int uint256Int) (auctionUint256Loc
        ⟨203⟩)
        hbase (by native_decide) rfl, loadUint256])

theorem timeBufferX {σ σ₀ A I} {g : UInt256}
    (hreach : EntryReached 17 σ σ₀ A I g) (hwv : I.weiValue = ⟨0⟩) :
    RDret auctionBytecode (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ
      (UInt256.toByteArray (storedWord σ I ⟨203⟩)) := by
  obtain ⟨_, _, rd880⟩ := hreach
  obtain ⟨_, _, rd893⟩ := entryGuardZero 17 (by decide) rd880 hwv
  have rd898 := evm_run rd893 with [push2 ⟨308⟩, push1 ⟨203⟩]
  obtain ⟨_, _, rd899⟩ := rd898.sload (by native_decide) (by evm_ov)
  have rd308 := evm_run rd899 with [dup2, jump (by jump_dest)]
  exact rd308.auctionReturnWord (by evm_ov)

theorem timeBufferBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = auctionBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I (entryBytes 17))
    (hreach : EntryReached 17 σ σ₀ A I g) :
    runtimeEquivalenceFor auctionConfig auctionContract
      σ σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hsz := calldata_size_ge_of_selIs I (entryBytes 17) (entryBytes_size 17) hsel
    have hd := dispatchEntry 17 hsel
    have hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
        (timeBufferGetter.params.map Param.name)
        (transitionSignature timeBufferGetter).paramTypes I.calldata = some ∅ :=
      decodeCalldata_empty_ok hsz
    have hbody : ExecTransitionBody auctionConfig auctionContract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ timeBufferGetter.body
        (.returned { contract := auctionContract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [.int (Int.ofNat (storedWord σ I ⟨203⟩).toNat)])) := by
      simpa [storedWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
        timeBufferBodyReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          ∅ hwv (by simp)
    exact (timeBufferX hreach hwv).reEquivExecution hcode hd hdec hbody
      (returnEquiv_of_encode (uint256ReturnEncoding (storedWord σ I ⟨203⟩)))
  · exact entryNonpayableRevert 17 (by decide) hcode hsel hreach hwv

end Auction
