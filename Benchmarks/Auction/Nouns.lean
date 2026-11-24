import Benchmarks.Auction.Storage

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

theorem nounsBodyReturns (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hbase : locals.get? "nouns" = none) :
    ExecTransitionBody fork auctionConfig auctionContract evm locals nounsGetter.body
      (.returned { contract := auctionContract, locals := locals } evm
        (some [.address (AccountAddress.ofNat
          (UInt256.land (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
            solcAddrMask).toNat)])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns (by
      rw [nounsRef, scalarRead evm locals "nouns" .address (auctionAddrLoc ⟨201⟩)
        hbase (by native_decide) rfl, loadAddress])

theorem nounsX {σ σ₀ A I} {g : UInt256}
    (hreach : EntryReached fork 1 σ σ₀ A I g) (hwv : I.weiValue = ⟨0⟩) :
    RDret fork auctionBytecode (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ
      (UInt256.toByteArray (UInt256.land (solcSlotWord σ I ⟨201⟩) solcAddrMask)) := by
  obtain ⟨_, _, rd327⟩ := hreach
  obtain ⟨_, _, rd340⟩ := entryGuardZero 1 (by decide) rd327 hwv
  have rd342 := evm_run rd340 with [push1 ⟨201⟩]
  obtain ⟨_, _, rd343⟩ := rd342.sload (by native_decide) (by evm_ov)
  have rd358 := evm_run rd343 with [
    push2 ⟨358⟩, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩,
    shl, sub, and, dup2, jump (by jump_dest) ]
  have hret := RD.auctionReturnAddress
    (val := UInt256.land solcAddrMask (solcSlotWord σ I ⟨201⟩)) rd358 (by evm_ov)
  have hclean :
      UInt256.land (UInt256.land solcAddrMask (solcSlotWord σ I ⟨201⟩)) solcAddrMask =
        UInt256.land (solcSlotWord σ I ⟨201⟩) solcAddrMask := by
    rw [u256_land_comm solcAddrMask (solcSlotWord σ I ⟨201⟩)]
    exact solcAddrMask_clean (solcAddrMask_result_canonical _)
  simpa only [hclean] using hret

theorem nounsBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = auctionBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (entryBytes 1))
    (hreach : EntryReached fork 1 σ σ₀ A I g) :
    runtimeRefinementFor fork auctionConfig auctionContract
      σ σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hsz := calldata_size_ge_of_selIs I (entryBytes 1) (entryBytes_size 1) hsel
    have hd := dispatchEntry 1 hsel
    have hdec : auctionConfig.externalABI.decodeCalldata?
        (nounsGetter.params.map Param.name)
        (transitionSignature nounsGetter).paramTypes I.calldata = some ∅ :=
      decodeCalldata_empty_ok hsz
    have hbody : ExecTransitionBody fork auctionConfig auctionContract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ nounsGetter.body
        (.returned { contract := auctionContract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [.address (AccountAddress.ofNat
            (UInt256.land (solcSlotWord σ I ⟨201⟩) solcAddrMask).toNat)])) := by
      simpa [solcSlotWord, initState, Stele.EVM.storageLoad, State.lookupAccount] using
        nounsBodyReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          ∅ hwv (by simp)
    exact (nounsX hreach hwv).reEquivExecution hcode hd hdec hbody
      (returnEquiv_of_encode
        (solcAddressReturnEncoding (addrTy := addr) rfl (solcSlotWord σ I ⟨201⟩)))
  · exact entryNonpayableRevert 1 (by decide) hcode hsel hreach hwv

end Auction
