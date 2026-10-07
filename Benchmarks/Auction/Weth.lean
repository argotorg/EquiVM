import Benchmarks.Auction.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

theorem wethBodyReturns (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hbase : locals.get? "weth" = none) :
    ExecTransitionBody auctionConfig auctionContract evm locals wethGetter.body
      (.returned { contract := auctionContract, locals := locals } evm
        (some [.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat)])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns (by
      rw [wethRef, scalarRead evm locals "weth" .address (auctionAddrLoc ⟨202⟩)
        hbase (by native_decide) rfl, loadAddress])

theorem wethX {σ σ₀ A I} {g : UInt256}
    (hreach : EntryReached 4 σ σ₀ A I g) (hwv : I.weiValue = ⟨0⟩) :
    RDret auctionBytecode (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ
      (UInt256.toByteArray (UInt256.land (storedWord σ I ⟨202⟩) solcAddrMask)) := by
  obtain ⟨_, _, rd435⟩ := hreach
  obtain ⟨_, _, rd448⟩ := entryGuardZero 4 (by decide) rd435 hwv
  have rd450 := evm_run rd448 with [push1 ⟨202⟩]
  obtain ⟨_, _, rd451⟩ := rd450.sload (by native_decide) (by evm_ov)
  have rd358 := evm_run rd451 with [
    push2 ⟨358⟩, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩,
    shl, sub, and, dup2, jump (by jump_dest) ]
  have hret := RD.auctionReturnAddress
    (val := UInt256.land solcAddrMask (storedWord σ I ⟨202⟩)) rd358 (by evm_ov)
  have hclean :
      UInt256.land (UInt256.land solcAddrMask (storedWord σ I ⟨202⟩)) solcAddrMask =
        UInt256.land (storedWord σ I ⟨202⟩) solcAddrMask := by
    rw [u256_land_comm solcAddrMask (storedWord σ I ⟨202⟩)]
    exact solcAddrMask_clean (solcAddrMask_result_canonical _)
  simpa only [hclean] using hret

theorem wethBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = auctionBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I (entryBytes 4))
    (hreach : EntryReached 4 σ σ₀ A I g) :
    runtimeRefinementFor auctionConfig auctionContract
      σ σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hsz := calldata_size_ge_of_selIs I (entryBytes 4) (entryBytes_size 4) hsel
    have hd := dispatchEntry 4 hsel
    have hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
        (wethGetter.params.map Param.name)
        (transitionSignature wethGetter).paramTypes I.calldata = some ∅ :=
      decodeCalldata_empty_ok hsz
    have hbody : ExecTransitionBody auctionConfig auctionContract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ wethGetter.body
        (.returned { contract := auctionContract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [.address (AccountAddress.ofNat
            (UInt256.land (storedWord σ I ⟨202⟩) solcAddrMask).toNat)])) := by
      simpa [storedWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
        wethBodyReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          ∅ hwv (by simp)
    exact (wethX hreach hwv).reEquivExecution hcode hd hdec hbody
      (returnEquiv_of_encode
        (solcAddressReturnEncoding (addrTy := addr) rfl (storedWord σ I ⟨202⟩)))
  · exact entryNonpayableRevert 4 (by decide) hcode hsel hreach hwv

end Auction
