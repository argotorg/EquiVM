import Solm.Benchmarks.Auction.Snapshot

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

theorem auctionBodyReturns (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hbase : locals.get? "auction" = none) :
    ExecTransitionBody auctionConfig auctionContract evm locals auctionGetter.body
      (.returned { contract := auctionContract, locals := locals } evm
        (some (snapshotOfState evm).values)) := by
  have h0 := auctionFieldRead evm locals "nounId" (.int uint256Int)
    (auctionUint256Loc ⟨207⟩) hbase (by native_decide) rfl
  rw [loadUint256] at h0
  have h1 := auctionFieldRead evm locals "amount" (.int uint256Int)
    (auctionUint256Loc ⟨208⟩) hbase (by native_decide) rfl
  rw [loadUint256] at h1
  have h2 := auctionFieldRead evm locals "startTime" (.int uint256Int)
    (auctionUint256Loc ⟨209⟩) hbase (by native_decide) rfl
  rw [loadUint256] at h2
  have h3 := auctionFieldRead evm locals "endTime" (.int uint256Int)
    (auctionUint256Loc ⟨210⟩) hbase (by native_decide) rfl
  rw [loadUint256] at h3
  have h4 := auctionFieldRead evm locals "bidder" .address
    (auctionAddrLoc ⟨211⟩) hbase (by native_decide) rfl
  rw [loadAddress] at h4
  have h5 := auctionFieldRead evm locals "settled" .bool
    (auctionBoolLocAt ⟨211⟩ 20) hbase (by native_decide) rfl
  rw [loadBoolAt] at h5
  apply ExecFuncBody.execBlockRet
  apply (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
  apply ExecBlock.consReturn
  apply ExecStmt.return
  simp only [evalExprs?, h0, h1, h2, h3, h4, h5, EvalResult.bind, bind, pure]
  rfl

theorem auctionEncode {ee g s0 R rdata acc k C} (s : Snapshot)
    (h : RD auctionBytecode ee g s0 ⟨629⟩
      (s.settledByte :: s.bidderWord :: s.endTime :: s.startTime :: s.amount :: s.nounId :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 10 ≤ 1024) :
    RDret auctionBytecode g s0 acc (wordBytes s.words) := by
  have rd637 := evm_run h with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
      solcFreePtrMem_mload64 (by decide) (by evm_ov),
    swap7, dup8,
    raw mstore 6 (returnMem [s.nounId]) (UInt256.ofNat 5) (by native_decide) mem_cost
      (by rw [← returnMem_single]; rfl) (by decide) (by evm_ov) ]
  have rd645 := evm_run rd637 with [
    push1 ⟨32⟩, dup8, add, swap6, swap1, swap6,
    raw mstore 3 (returnMem [s.nounId, s.amount]) (UInt256.ofNat 6)
      (by native_decide) mem_cost
      (by simpa using returnMem_write [s.nounId] s.amount) (by decide) (by evm_ov) ]
  have rd652 := evm_run rd645 with [
    swap4, dup6, add, swap3, swap1, swap3,
    raw mstore 3 (returnMem [s.nounId, s.amount, s.startTime]) (UInt256.ofNat 7)
      (by native_decide) mem_cost
      (by simpa using returnMem_write [s.nounId, s.amount] s.startTime)
      (by decide) (by evm_ov) ]
  have rd657 := evm_run rd652 with [
    push1 ⟨96⟩, dup5, add,
    raw mstore 3 (returnMem [s.nounId, s.amount, s.startTime, s.endTime]) (UInt256.ofNat 8)
      (by native_decide) mem_cost
      (by simpa using returnMem_write [s.nounId, s.amount, s.startTime] s.endTime)
      (by decide) (by evm_ov) ]
  have rd671 := evm_run rd657 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, push1 ⟨128⟩, dup4, add,
    raw mstore 3 (returnMem [s.nounId, s.amount, s.startTime, s.endTime, s.bidderWord])
      (UInt256.ofNat 9) (by native_decide) mem_cost
      (by
        change (UInt256.toByteArray (UInt256.land solcAddrMask s.bidderWord)).write 0
          (returnMem [s.nounId, s.amount, s.startTime, s.endTime]) 256 32 = _
        rw [show UInt256.land solcAddrMask s.bidderWord = s.bidderWord from
          solcAddrMask_clean_left (solcAddrMask_result_canonical s.packed)]
        simpa using returnMem_write [s.nounId, s.amount, s.startTime, s.endTime] s.bidderWord)
      (by decide) (by evm_ov) ]
  have rd681 := evm_run rd671 with [
    iszero, iszero, push1 ⟨160⟩, dup3, add,
    raw mstore 3 (returnMem s.words) (UInt256.ofNat 10) (by native_decide) mem_cost
      (by simpa [Snapshot.words, Snapshot.settledWord] using
        returnMem_write [s.nounId, s.amount, s.startTime, s.endTime, s.bidderWord] s.settledWord)
      (by decide) (by evm_ov),
    push1 ⟨192⟩, add ]
  have rd318 := evm_run rd681 with [push2 ⟨318⟩, jump (by jump_dest)]
  exact evm_run rd318 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 10) (by native_decide) mem_cost
      (mloadFreePtrValue (by rw [returnMem_size]; omega) (by decide) (returnMem_read64 s.words))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (wordBytes s.words) (by native_decide) mem_cost
      (by
        change (returnMem s.words).readWithPadding 128 192 = _
        exact returnMem_read128 s.words (by simp [Snapshot.words]) (by simp [Snapshot.words]))
      (by evm_ov) ]

theorem auctionX {cA gh bl σ σ₀ A I} {g : UInt256}
    (hreach : EntryReached 9 cA gh bl σ σ₀ A I g) (hwv : I.weiValue = ⟨0⟩) :
    RDret auctionBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (cA, σ)
      (wordBytes (snapshotOf σ I).words) := by
  obtain ⟨_, _, rd570⟩ := hreach
  obtain ⟨_, _, rd583⟩ := entryGuardZero 9 (by decide) rd570 hwv
  have rd585 := evm_run rd583 with [push1 ⟨207⟩]
  obtain ⟨_, _, rd586⟩ := rd585.sload (by native_decide) (by evm_ov)
  have rd588 := evm_run rd586 with [push1 ⟨208⟩]
  obtain ⟨_, _, rd589⟩ := rd588.sload (by native_decide) (by evm_ov)
  have rd591 := evm_run rd589 with [push1 ⟨209⟩]
  obtain ⟨_, _, rd592⟩ := rd591.sload (by native_decide) (by evm_ov)
  have rd594 := evm_run rd592 with [push1 ⟨210⟩]
  obtain ⟨_, _, rd595⟩ := rd594.sload (by native_decide) (by evm_ov)
  have rd597 := evm_run rd595 with [push1 ⟨211⟩]
  obtain ⟨_, _, rd598⟩ := rd597.sload (by native_decide) (by evm_ov)
  have rd617 := evm_run rd598 with [
    push2 ⟨629⟩, swap5, swap4, swap3, swap2, swap1,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, swap1 ]
  have rd629 := evm_run rd617 with [
    push1 ⟨1⟩, push1 ⟨160⟩, shl, swap1, div, push1 ⟨255⟩, and, dup7,
    jump (by jump_dest) ]
  have hmask : UInt256.land ⟨255⟩ (snapshotOf σ I).settledSourceWord =
      (snapshotOf σ I).settledByte :=
    u256_land_comm _ _
  change RD _ _ _ _ _
    [UInt256.land ⟨255⟩ (snapshotOf σ I).settledSourceWord, (snapshotOf σ I).bidderWord,
      (snapshotOf σ I).endTime, (snapshotOf σ I).startTime, (snapshotOf σ I).amount,
      (snapshotOf σ I).nounId, ⟨629⟩, solcSelectorWord I] _ _ _ _ _ _ at rd629
  rw [hmask] at rd629
  exact auctionEncode (snapshotOf σ I) rd629 (by evm_ov)

theorem auctionBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = auctionBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I (entryBytes 9))
    (hreach : EntryReached 9 cA gh bl σ_evm σ₀ A I g)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor auctionConfig auctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hsz := calldata_size_ge_of_selIs I (entryBytes 9) (entryBytes_size 9) hsel
    have hd := dispatchEntry 9 hsel
    have hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
        (auctionGetter.params.map Param.name)
        (transitionSignature auctionGetter).paramTypes I.calldata = some ∅ :=
      decodeCalldata_empty_ok hsz
    have hsnapshot := snapshotOf_equiv hAccounts I
    have hbody : ExecTransitionBody auctionConfig auctionContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ auctionGetter.body
        (.returned { contract := auctionContract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (snapshotOf σ_solm I).values)) := by
      simpa [snapshotOf, snapshotOfState, storedWord, initState,
        Solm.EVM.storageLoad, State.lookupAccount] using
        auctionBodyReturns (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          ∅ hwv (by simp)
    exact (auctionX hreach hwv).reEquivExecutionTransport hcode hd hdec hbody
      (by rw [hsnapshot]) hAccounts
      (returnEquiv.returned rfl rfl (snapshotReturnEncoding (snapshotOf σ_evm I)))
  · exact entryNonpayableRevert 9 (by decide) hcode hsel hreach hwv

end Auction
