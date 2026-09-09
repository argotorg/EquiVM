import Benchmarks.Auction.CreateBidRefundFailure
import Benchmarks.Auction.CreateBidRefundSource
import Benchmarks.Auction.DynamicMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

namespace Auction

set_option maxHeartbeats 1000000 in
theorem auctionSafeTransferNotMadeWethCodeReverts {cA gh bl σ σ₀ A I}
    {g : Sat256} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {amount owner aw : UInt256} {mem o : ByteArray} {k C : ℕ} {R : List UInt256}
    (hR : R.length ≤ 990) (hperm : I.perm = true)
    (hnot : ¬ (amount ≤ (σ'.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)) ∧ I.depth ≠ 1024))
    (hwethCode :
      Reasoning.Theory.uniswapExtCodeSizeWord σ'
          (UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask) ≠
        ⟨0⟩)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3347⟩
      (⟨0⟩ :: amount :: owner :: R)
      mem aw o (cA', σ') k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let weth := UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask
  let freePtr :=
    if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))
  let awFree : UInt256 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let memSel := (UInt256.toByteArray auctionSettleAuctionDepositSelectorShifted).write 0
    mem freePtr.toNat 32
  let awSel : UInt256 := UInt256.ofNat (MachineState.M awFree.toNat freePtr.toNat 32)
  let freePtr2 :=
    if (⟨64⟩ : UInt256).toNat ≥ memSel.size ∨ (⟨64⟩ : UInt256) ≥ awSel * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat
      (fromByteArrayBigEndian (memSel.readWithPadding (⟨64⟩ : UInt256).toNat 32))
  let awFree2 : UInt256 :=
    UInt256.ofNat (MachineState.M awSel.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd3356 := evm_run rd with [
    jumpdest, push2 ⟨3570⟩, jumpiNT (by native_decide), push1 ⟨202⟩, push0, swap1]
  obtain ⟨_, _, rd3357₀⟩ := rd3356.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3357⟩ : ∃ k' C', RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3357⟩
      (auctionSlotWord ⟨202⟩ σ' I ::
        ⟨0⟩ :: amount :: owner :: R)
      mem aw o (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3357₀⟩
  have rd3417₀ := evm_run rd3357 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    push4 ⟨3504541104⟩, dup3, push1 ⟨64⟩,
    raw mload (Cₘ awFree - Cₘ aw) freePtr awFree (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    dup3, push4 ⟨0xffffffff⟩, and, push1 ⟨224⟩, shl, dup2,
    raw mstore (Cₘ awSel - Cₘ awFree) memSel awSel (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨4⟩, add, push0, push1 ⟨64⟩,
    raw mload (Cₘ awFree2 - Cₘ awSel) freePtr2 awFree2 (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    dup1, dup4, sub, dup2, dup6, dup9, dup1]
  have hdiv :
      UInt256.div (auctionSlotWord ⟨202⟩ σ' I)
        (UInt256.exp (⟨256⟩ : UInt256) ⟨0⟩) =
      auctionSlotWord ⟨202⟩ σ' I := by
    apply u256_inj
    rw [show UInt256.exp (⟨256⟩ : UInt256) ⟨0⟩ = ⟨1⟩ by native_decide]
    rw [udiv_toNat]
    exact Nat.div_one (auctionSlotWord ⟨202⟩ σ' I).toNat
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have hwethMask :
      UInt256.land solcAddrMask (UInt256.land solcAddrMask (auctionSlotWord ⟨202⟩ σ' I)) =
        weth := by
    change UInt256.land solcAddrMask (UInt256.land solcAddrMask (auctionSlotWord ⟨202⟩ σ' I)) =
      UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask
    rw [u256_land_comm solcAddrMask (auctionSlotWord ⟨202⟩ σ' I)]
    exact solcAddrMask_clean_left
      (solcAddrMask_result_canonical (auctionSlotWord ⟨202⟩ σ' I))
  have rd3417 := rd3417₀
  rw [hdiv, hmaskConst, hwethMask] at rd3417
  obtain ⟨gasWord, _, _, h3431⟩ := RD.uniswapExtcodesizeGuardOkGas
    (pc := ⟨3417⟩) (okPc := ⟨3428⟩) rd3417
    hwethCode (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
    (by native_decide) (by native_decide) (by evm_ov)
  obtain ⟨memCall, awCall, _, _, h3432⟩ := auctionCallNotMade h3431
    (by native_decide) hperm hnot (by evm_ov)
  have h3442 := evm_run h3432 with [iszero, dup1, iszero, push2 ⟨3446⟩,
    jumpiNT (by native_decide), returndatasize, push0, dup1]
  obtain ⟨_, _, _, _, h3443⟩ := auctionReturndataCopyDynamic h3442
    (by native_decide) (by native_decide) (by evm_ov)
  have h3445 := evm_run h3443 with [returndatasize, push0]
  exact auctionRevertDynamic h3445 (by native_decide) (by evm_ov)

theorem auctionSafeTransferNotMadeReverts (evm : EVM.State)
    (recipient : AccountAddress) (amount : UInt256)
    (hnot : ¬ (EVM.wordOfInt (Int.ofNat amount.toNat) ≤
      (evm.accountMap.find? evm.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)) ∧
      evm.executionEnv.depth ≠ 1024)) :
    ExecFuncBody auctionConfig
      { contract := auctionContract, locals := auctionSafeTransferStore recipient amount }
      evm safeTransferETHWithFallback.body .reverted := by
  let evmRefund :=
    { evm with substate := (evm.addAccessedAccount (EVM.address recipient)).substate }
  have hrefund : callViaEVM evm (EVM.address recipient) (Int.ofNat amount.toNat)
      ByteArray.empty (false, evmRefund, ByteArray.empty) true := by
    exact callViaEVM.callNotMade rfl rfl hnot
  by_cases hwethCode :
      (UInt256.ofNat (((evmRefund.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat = 0
  · exact auctionSafeTransferBodyReverts_lowLevelFailureWethNoCode
      evm evmRefund recipient amount hrefund hwethCode
  · let weth := EVM.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner ⟨202⟩)
        solcAddrMask).toNat)
    let evmDeposit :=
      { evmRefund with substate := (evmRefund.addAccessedAccount weth).substate }
    have hdeposit : typedCallViaEVM auctionConfig evmRefund weth "deposit"
        (Int.ofNat amount.toNat) [] (false, evmDeposit, ByteArray.empty) true := by
      refine ⟨depositSelector, rfl, ?_⟩
      exact callViaEVM.callNotMade rfl rfl hnot
    exact auctionSafeTransferBodyReverts_lowLevelFailureWethDepositFailure
      evm evmRefund evmDeposit recipient amount hrefund (Nat.pos_of_ne_zero hwethCode) hdeposit

theorem auctionCreateBidTransitionReverts_refundNotMade
    (evm : EVM.State) (I : ExecutionEnv)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hnoun :
      Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨207⟩ =
        auctionCreateBidArgWord I)
    (htime : (UInt256.ofNat
        (auctionCreateBidEnterState evm).executionEnv.header.timestamp).toNat <
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩).toNat)
    (hreserve : (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨204⟩).toNat ≤
      (auctionCreateBidEnterState evm).executionEnv.weiValue.toNat)
    (hmulFit :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
        (UInt256.land
          (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
          ⟨255⟩).toNat < UInt256.size)
    (haddFit :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat +
        ((Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
          (UInt256.land
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat) / 100 < UInt256.size)
    (hbid :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat +
        ((Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
          (UInt256.land
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat) / 100 ≤
      (auctionCreateBidEnterState evm).executionEnv.weiValue.toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnotMade :
      ¬ (EVM.wordOfInt (Int.ofNat
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat) ≤
          ((auctionCreateBidEnterState evm).accountMap.find?
            (auctionCreateBidEnterState evm).executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)) ∧
        (auctionCreateBidEnterState evm).executionEnv.depth ≠ 1024)) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionCreateBidStore I)
      createBidTransition.body .reverted := by
  exact auctionCreateBidTransitionReverts_refundReverted evm I
    hstatus hnoun htime hreserve hmulFit haddFit hbid hbidder
    (auctionSafeTransferNotMadeReverts _ _ _ hnotMade)

end Auction
