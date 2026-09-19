import Solm.Benchmarks.Auction.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

theorem pausedBodyReturns (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hbase : locals.get? "_paused" = none) :
    ExecTransitionBody auctionConfig auctionContract evm locals pausedGetter.body
      (.returned { contract := auctionContract, locals := locals } evm
        (some [wordToElem .bool
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩)])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns (by
      rw [pausedRef, scalarRead evm locals "_paused" .bool (auctionBoolLoc ⟨51⟩)
        hbase (by native_decide) rfl, loadBool])

theorem pausedX {cA gh bl σ σ₀ A I} {g : UInt256}
    (hreach : EntryReached 5 cA gh bl σ σ₀ A I g) (hwv : I.weiValue = ⟨0⟩) :
    RDret auctionBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (cA, σ)
      (UInt256.toByteArray
        (UInt256.isZero (UInt256.isZero (UInt256.land (storedWord σ I ⟨51⟩) ⟨255⟩)))) := by
  obtain ⟨_, _, rd466⟩ := hreach
  obtain ⟨_, _, rd479⟩ := entryGuardZero 5 (by decide) rd466 hwv
  have rd481 := evm_run rd479 with [push1 ⟨51⟩]
  obtain ⟨_, _, rd482⟩ := rd481.sload (by native_decide) (by evm_ov)
  let val := UInt256.isZero (UInt256.isZero (UInt256.land ⟨255⟩ (storedWord σ I ⟨51⟩)))
  have rd318 := evm_run rd482 with [
    push1 ⟨255⟩, and, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
      solcFreePtrMem_mload64 (by decide) (by evm_ov),
    swap1, iszero, iszero, dup2,
    raw mstore 6 (solcReturnMem val) (UInt256.ofNat 5) (by native_decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨318⟩, jump (by jump_dest) ]
  have hret := rd318.auctionReturn32 (by evm_ov)
  simpa only [val, u256_land_comm ⟨255⟩ (storedWord σ I ⟨51⟩)] using hret

theorem pausedBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = auctionBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I (entryBytes 5))
    (hreach : EntryReached 5 cA gh bl σ_evm σ₀ A I g)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor auctionConfig auctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hsz := calldata_size_ge_of_selIs I (entryBytes 5) (entryBytes_size 5) hsel
    have hd := dispatchEntry 5 hsel
    have hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
        (pausedGetter.params.map Param.name)
        (transitionSignature pausedGetter).paramTypes I.calldata = some ∅ :=
      decodeCalldata_empty_ok hsz
    have hword := storedWord_equiv hAccounts I ⟨51⟩
    have hbody : ExecTransitionBody auctionConfig auctionContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ pausedGetter.body
        (.returned { contract := auctionContract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [wordToElem .bool (UInt256.land (storedWord σ_solm I ⟨51⟩) ⟨255⟩)])) := by
      simpa [storedWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
        pausedBodyReturns (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          ∅ hwv (by simp)
    exact (pausedX hreach hwv).reEquivExecutionTransport hcode hd hdec hbody
      (by rw [hword]) hAccounts
      (returnEquiv_of_encode (boolWordReturnEncoding (storedWord σ_evm I ⟨51⟩)))
  · exact entryNonpayableRevert 5 (by decide) hcode hsel hreach hwv

end Auction
