import Benchmarks.Auction.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

theorem ownerBodyReturns (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hbase : locals.get? "_owner" = none) :
    ExecTransitionBody auctionConfig auctionContract evm locals ownerGetter.body
      (.returned { contract := auctionContract, locals := locals } evm
        (some [.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩)
            solcAddrMask).toNat)])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns (by
      rw [ownerRef, scalarRead evm locals "_owner" .address (auctionAddrLoc ⟨151⟩)
        hbase (by native_decide) rfl, loadAddress])

theorem ownerX {σ σ₀ A I} {g : UInt256}
    (hreach : EntryReached 12 σ σ₀ A I g) (hwv : I.weiValue = ⟨0⟩) :
    RDret auctionBytecode (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ
      (UInt256.toByteArray (UInt256.land (solcSlotWord σ I ⟨151⟩) solcAddrMask)) := by
  obtain ⟨_, _, rd736⟩ := hreach
  obtain ⟨_, _, rd749⟩ := entryGuardZero 12 (by decide) rd736 hwv
  have rd751 := evm_run rd749 with [push1 ⟨151⟩]
  obtain ⟨_, _, rd752⟩ := rd751.sload (by native_decide) (by evm_ov)
  have rd358 := evm_run rd752 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    push2 ⟨358⟩, jump (by jump_dest) ]
  have hret := RD.auctionReturnAddress
    (val := UInt256.land solcAddrMask (solcSlotWord σ I ⟨151⟩)) rd358 (by evm_ov)
  have hclean :
      UInt256.land (UInt256.land solcAddrMask (solcSlotWord σ I ⟨151⟩)) solcAddrMask =
        UInt256.land (solcSlotWord σ I ⟨151⟩) solcAddrMask := by
    rw [u256_land_comm solcAddrMask (solcSlotWord σ I ⟨151⟩)]
    exact solcAddrMask_clean (solcAddrMask_result_canonical _)
  simpa only [hclean] using hret

theorem ownerBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = auctionBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (entryBytes 12))
    (hreach : EntryReached 12 σ σ₀ A I g) :
    runtimeRefinementFor auctionConfig auctionContract
      σ σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hsz := calldata_size_ge_of_selIs I (entryBytes 12) (entryBytes_size 12) hsel
    have hd := dispatchEntry 12 hsel
    have hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
        (ownerGetter.params.map Param.name)
        (transitionSignature ownerGetter).paramTypes I.calldata = some ∅ :=
      decodeCalldata_empty_ok hsz
    have hbody : ExecTransitionBody auctionConfig auctionContract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ ownerGetter.body
        (.returned { contract := auctionContract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [.address (AccountAddress.ofNat
            (UInt256.land (solcSlotWord σ I ⟨151⟩) solcAddrMask).toNat)])) := by
      simpa [solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
        ownerBodyReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          ∅ hwv (by simp)
    exact (ownerX hreach hwv).reEquivExecution hcode hd hdec hbody
      (returnEquiv_of_encode
        (solcAddressReturnEncoding (addrTy := addr) rfl (solcSlotWord σ I ⟨151⟩)))
  · exact entryNonpayableRevert 12 (by decide) hcode hsel hreach hwv

end Auction
