import Benchmarks.Auction.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

theorem reservePriceBodyReturns (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hbase : locals.get? "reservePrice" = none) :
    ExecTransitionBody auctionConfig auctionContract evm locals reservePriceGetter.body
      (.returned { contract := auctionContract, locals := locals } evm
        (some [.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨204⟩).toNat)])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns (by
      rw [reservePriceRef, scalarRead evm locals "reservePrice" (.int uint256Int)
        (auctionUint256Loc ⟨204⟩)
        hbase (by native_decide) rfl, loadUint256])

theorem reservePriceX {σ σ₀ A I} {g : UInt256}
    (hreach : EntryReached 16 σ σ₀ A I g) (hwv : I.weiValue = ⟨0⟩) :
    RDret auctionBytecode (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ
      (UInt256.toByteArray (solcSlotWord σ I ⟨204⟩)) := by
  obtain ⟨_, _, rd859⟩ := hreach
  obtain ⟨_, _, rd872⟩ := entryGuardZero 16 (by decide) rd859 hwv
  have rd877 := evm_run rd872 with [push2 ⟨308⟩, push1 ⟨204⟩]
  obtain ⟨_, _, rd878⟩ := rd877.sload (by native_decide) (by evm_ov)
  have rd308 := evm_run rd878 with [dup2, jump (by jump_dest)]
  exact rd308.auctionReturnWord (by evm_ov)

theorem reservePriceBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = auctionBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (entryBytes 16))
    (hreach : EntryReached 16 σ σ₀ A I g) :
    runtimeRefinementFor auctionConfig auctionContract
      σ σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hsz := calldata_size_ge_of_selIs I (entryBytes 16) (entryBytes_size 16) hsel
    have hd := dispatchEntry 16 hsel
    have hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
        (reservePriceGetter.params.map Param.name)
        (transitionSignature reservePriceGetter).paramTypes I.calldata = some ∅ :=
      decodeCalldata_empty_ok hsz
    have hbody : ExecTransitionBody auctionConfig auctionContract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ reservePriceGetter.body
        (.returned { contract := auctionContract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [.int (Int.ofNat (solcSlotWord σ I ⟨204⟩).toNat)])) := by
      simpa [solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
        reservePriceBodyReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          ∅ hwv (by simp)
    exact (reservePriceX hreach hwv).reEquivExecution hcode hd hdec hbody
      (returnEquiv_of_encode (uint256ReturnEncoding (solcSlotWord σ I ⟨204⟩)))
  · exact entryNonpayableRevert 16 (by decide) hcode hsel hreach hwv

end Auction
