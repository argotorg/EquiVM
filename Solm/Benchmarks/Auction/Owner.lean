import Solm.Benchmarks.Auction.Storage

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

theorem ownerX {cA gh bl σ σ₀ A I} {g : UInt256}
    (hreach : EntryReached 12 cA gh bl σ σ₀ A I g) (hwv : I.weiValue = ⟨0⟩) :
    RDret auctionBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (cA, σ)
      (UInt256.toByteArray (UInt256.land (storedWord σ I ⟨151⟩) solcAddrMask)) := by
  obtain ⟨_, _, rd736⟩ := hreach
  obtain ⟨_, _, rd749⟩ := entryGuardZero 12 (by decide) rd736 hwv
  have rd751 := evm_run rd749 with [push1 ⟨151⟩]
  obtain ⟨_, _, rd752⟩ := rd751.sload (by native_decide) (by evm_ov)
  have rd358 := evm_run rd752 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    push2 ⟨358⟩, jump (by jump_dest) ]
  have hret := RD.auctionReturnAddress
    (val := UInt256.land solcAddrMask (storedWord σ I ⟨151⟩)) rd358 (by evm_ov)
  have hclean :
      UInt256.land (UInt256.land solcAddrMask (storedWord σ I ⟨151⟩)) solcAddrMask =
        UInt256.land (storedWord σ I ⟨151⟩) solcAddrMask := by
    rw [u256_land_comm solcAddrMask (storedWord σ I ⟨151⟩)]
    exact solcAddrMask_clean (solcAddrMask_result_canonical _)
  simpa only [hclean] using hret

theorem ownerBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = auctionBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I (entryBytes 12))
    (hreach : EntryReached 12 cA gh bl σ_evm σ₀ A I g)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor auctionConfig auctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hsz := calldata_size_ge_of_selIs I (entryBytes 12) (entryBytes_size 12) hsel
    have hd := dispatchEntry 12 hsel
    have hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
        (ownerGetter.params.map Param.name)
        (transitionSignature ownerGetter).paramTypes I.calldata = some ∅ :=
      decodeCalldata_empty_ok hsz
    have hword := storedWord_equiv hAccounts I ⟨151⟩
    have hbody : ExecTransitionBody auctionConfig auctionContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ ownerGetter.body
        (.returned { contract := auctionContract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [.address (AccountAddress.ofNat
            (UInt256.land (storedWord σ_solm I ⟨151⟩) solcAddrMask).toNat)])) := by
      simpa [storedWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
        ownerBodyReturns (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          ∅ hwv (by simp)
    exact (ownerX hreach hwv).reEquivExecutionTransport hcode hd hdec hbody
      (by rw [hword]) hAccounts
      (returnEquiv_of_encode
        (solcAddressReturnEncoding (addrTy := addr) rfl (storedWord σ_evm I ⟨151⟩)))
  · exact entryNonpayableRevert 12 (by decide) hcode hsel hreach hwv

end Auction
