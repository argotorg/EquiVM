import Benchmarks.Auction.SettleAuctionDynamicWeth

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

set_option maxHeartbeats 1000000 in
theorem auctionSafeTransferFallbackToDepositCallAnyMem {cA gh bl σ σ₀ A I}
    {g : Sat256} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {amount owner aw : UInt256} {mem o : ByteArray} {k C : ℕ} {R : List UInt256}
    (hR : R.length ≤ 980)
    (hwethCode :
      Reasoning.Theory.uniswapExtCodeSizeWord σ'
          (UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask) ≠ ⟨0⟩)
    (hfreeStable :
      auctionSettleAuctionDynMload64
          (auctionSettleAuctionDynDepositMem mem aw)
          (auctionSettleAuctionDynDepositAw mem aw) =
        auctionSettleAuctionDynMload64 mem aw)
    (hlen :
      UInt256.sub (⟨4⟩ + auctionSettleAuctionDynMload64 mem aw)
          (auctionSettleAuctionDynMload64 mem aw) =
        ⟨4⟩)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3347⟩
      (⟨0⟩ :: amount :: owner :: R)
      mem aw o (cA', σ') k C) :
    let weth := UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask
    let freePtr := auctionSettleAuctionDynMload64 mem aw
    let memDeposit := auctionSettleAuctionDynDepositMem mem aw
    let awAfterLoad := auctionSettleAuctionDynDepositAwAfterMload64 mem aw
    ∃ gasWord k' C',
      RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3431⟩
        (gasWord :: weth :: amount :: freePtr :: ⟨4⟩ :: freePtr :: ⟨0⟩ :: (⟨4⟩ + freePtr) :: amount :: ⟨3504541104⟩ :: weth :: amount :: owner :: R)
        memDeposit awAfterLoad o (cA', σ') k' C' := by
  let weth := UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask
  let freePtr := auctionSettleAuctionDynMload64 mem aw
  let awFree := auctionSettleAuctionDynMload64Aw aw
  let memDeposit := auctionSettleAuctionDynDepositMem mem aw
  let awDeposit := auctionSettleAuctionDynDepositAw mem aw
  let freePtr2 := auctionSettleAuctionDynMload64 memDeposit awDeposit
  let awAfterLoad := auctionSettleAuctionDynDepositAwAfterMload64 mem aw
  have rd3356 := evm_run rd with [
    jumpdest, push2 ⟨3570⟩, jumpiNT (by native_decide), push1 ⟨202⟩, push0, swap1]
  obtain ⟨_, _, rd3357₀⟩ := rd3356.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3357⟩ : ∃ k' C', RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3357⟩
      (auctionSlotWord ⟨202⟩ σ' I ::
        (⟨0⟩ :: amount :: owner :: R))
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
    raw mstore (Cₘ awDeposit - Cₘ awFree) memDeposit awDeposit (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨4⟩, add, push0, push1 ⟨64⟩,
    raw mload (Cₘ awAfterLoad - Cₘ awDeposit) freePtr2 awAfterLoad (by native_decide)
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
  have rd3417Stable := rd3417
  have hfreeStableLocal : freePtr2 = freePtr := by
    simpa [freePtr2, freePtr, memDeposit, awDeposit] using hfreeStable
  have hlenLocal : UInt256.sub (⟨4⟩ + freePtr) freePtr = ⟨4⟩ := by
    simpa [freePtr] using hlen
  rw [hfreeStableLocal, hlenLocal] at rd3417Stable
  exact RD.uniswapExtcodesizeGuardOkGas (pc := ⟨3417⟩) (okPc := ⟨3428⟩) rd3417Stable
    hwethCode (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
    (by native_decide) (by native_decide) (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem auctionSafeTransferDepositSuccessToTransferLoadWethAnyMem
    {cA gh bl σ σ₀ A I}
    {g : Sat256} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {amount owner wethBefore aw freePtr : UInt256} {mem o : ByteArray} {k C : ℕ} {R : List UInt256}
    (hR : R.length ≤ 980)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3432⟩
      (⟨1⟩ :: (⟨4⟩ + freePtr) :: amount :: ⟨3504541104⟩ :: wethBefore :: amount :: owner :: R)
      mem aw o (cA', σ') k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3452⟩
      (auctionSlotWord ⟨202⟩ σ' I ::
        (amount :: ⟨3504541104⟩ :: wethBefore :: amount :: owner :: R))
      mem aw o (cA', σ') k' C' := by
  have rd3449 := evm_run rd with [
    iszero, dup1, iszero, push2 ⟨3446⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, pop, pop, push1 ⟨202⟩]
  obtain ⟨_, _, rd3452₀⟩ := rd3449.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [auctionSlotWord] using rd3452₀⟩

set_option maxHeartbeats 1000000 in
theorem auctionSafeTransferAfterDepositLoadFreePtrAnyMem
    {cA gh bl σ σ₀ A I}
    {g : Sat256} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {amount owner wethBefore aw freePtr : UInt256} {mem o : ByteArray} {k C : ℕ} {R : List UInt256}
    (hR : R.length ≤ 980)
    (hfree : auctionSettleAuctionDynMload64 mem aw = freePtr)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3452⟩
      (auctionSlotWord ⟨202⟩ σ' I ::
        (amount :: ⟨3504541104⟩ :: wethBefore :: amount :: owner :: R))
      mem aw o (cA', σ') k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3455⟩
      (freePtr :: auctionSlotWord ⟨202⟩ σ' I :: amount :: ⟨3504541104⟩ :: wethBefore :: amount :: owner :: R)
      mem (auctionSettleAuctionDynMload64Aw aw) o (cA', σ') k' C' := by
  have rdPart := evm_run rd with [
    push1 ⟨64⟩,
    raw mload
      (Cₘ (auctionSettleAuctionDynMload64Aw aw) - Cₘ aw)
      freePtr (auctionSettleAuctionDynMload64Aw aw) (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by simpa [auctionSettleAuctionDynMload64] using hfree)
      (by rfl) (by evm_ov)]
  exact ⟨_, _, by simpa using rdPart⟩

set_option maxHeartbeats 1000000 in
theorem auctionSafeTransferAfterDepositStoreTransferSelectorAnyMem
    {cA gh bl σ σ₀ A I}
    {g : Sat256} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {amount owner wethBefore aw freePtr : UInt256} {mem o : ByteArray} {k C : ℕ} {R : List UInt256}
    (hR : R.length ≤ 980)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3455⟩
      (freePtr :: auctionSlotWord ⟨202⟩ σ' I :: amount :: ⟨3504541104⟩ :: wethBefore :: amount :: owner :: R)
      mem (auctionSettleAuctionDynMload64Aw aw) o (cA', σ') k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3465⟩
      (freePtr :: auctionSlotWord ⟨202⟩ σ' I :: amount :: ⟨3504541104⟩ :: wethBefore :: amount :: owner :: R)
      (auctionSettleAuctionDynTransferSelMem mem freePtr)
      (auctionSettleAuctionDynTransferSelAw aw freePtr) o (cA', σ') k' C' := by
  let awFree := auctionSettleAuctionDynMload64Aw aw
  let memSel := auctionSettleAuctionDynTransferSelMem mem freePtr
  let awSel := auctionSettleAuctionDynTransferSelAw aw freePtr
  have rdPart := evm_run rd with [
    push4 ⟨2835717307⟩, push1 ⟨224⟩, shl, dup2,
    raw mstore (Cₘ awSel - Cₘ awFree) memSel awSel (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov)]
  exact ⟨_, _, by simpa [memSel, awSel] using rdPart⟩

set_option maxHeartbeats 1000000 in
theorem auctionSafeTransferAfterDepositStoreTransferOwnerAnyMem
    {cA gh bl σ σ₀ A I}
    {g : Sat256} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {amount owner wethBefore aw freePtr : UInt256} {mem o : ByteArray} {k C : ℕ} {R : List UInt256}
    (hR : R.length ≤ 980)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3465⟩
      (freePtr :: auctionSlotWord ⟨202⟩ σ' I :: amount :: ⟨3504541104⟩ :: wethBefore :: amount :: owner :: R)
      (auctionSettleAuctionDynTransferSelMem mem freePtr)
      (auctionSettleAuctionDynTransferSelAw aw freePtr) o (cA', σ') k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3481⟩
      (solcAddrMask :: freePtr :: auctionSlotWord ⟨202⟩ σ' I :: amount :: ⟨3504541104⟩ :: wethBefore :: amount :: owner :: R)
      (auctionSettleAuctionDynTransferArgMem mem freePtr amount owner)
      (auctionSettleAuctionDynTransferArgAw aw freePtr) o (cA', σ') k' C' := by
  let memArg := auctionSettleAuctionDynTransferArgMem mem freePtr amount owner
  let awSel := auctionSettleAuctionDynTransferSelAw aw freePtr
  let awArg := auctionSettleAuctionDynTransferArgAw aw freePtr
  have rdPart := evm_run rd with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup8, dup2, and,
    push1 ⟨4⟩, dup4, add,
    raw mstore (Cₘ awArg - Cₘ awSel) memArg awArg (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by
        dsimp [awArg, awSel, auctionSettleAuctionDynTransferArgAw]))
      (by rfl) (by rfl) (by evm_ov)]
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have rdPart' := rdPart
  rw [hmaskConst] at rdPart'
  exact ⟨_, _, by simpa [memArg, awArg] using rdPart'⟩

set_option maxHeartbeats 1000000 in
theorem auctionSafeTransferAfterDepositStoreTransferAmountAnyMem
    {cA gh bl σ σ₀ A I}
    {g : Sat256} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {amount owner wethBefore aw freePtr : UInt256} {mem o : ByteArray} {k C : ℕ} {R : List UInt256}
    (hR : R.length ≤ 980)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3481⟩
      (solcAddrMask :: freePtr :: auctionSlotWord ⟨202⟩ σ' I :: amount :: ⟨3504541104⟩ :: wethBefore :: amount :: owner :: R)
      (auctionSettleAuctionDynTransferArgMem mem freePtr amount owner)
      (auctionSettleAuctionDynTransferArgAw aw freePtr) o (cA', σ') k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3488⟩
      (solcAddrMask :: freePtr :: auctionSlotWord ⟨202⟩ σ' I :: amount :: ⟨3504541104⟩ :: wethBefore :: amount :: owner :: R)
      (auctionSettleAuctionDynTransferMem mem freePtr amount owner)
      (auctionSettleAuctionDynTransferAw aw freePtr) o (cA', σ') k' C' := by
  let memTransfer := auctionSettleAuctionDynTransferMem mem freePtr amount owner
  let awArg := auctionSettleAuctionDynTransferArgAw aw freePtr
  let awTransfer := auctionSettleAuctionDynTransferAw aw freePtr
  have rdPart := evm_run rd with [
    push1 ⟨36⟩, dup3, add, dup8, swap1,
    raw mstore (Cₘ awTransfer - Cₘ awArg) memTransfer awTransfer (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by
        dsimp [awTransfer, awArg, auctionSettleAuctionDynTransferAw]))
      (by rfl) (by rfl) (by evm_ov)]
  exact ⟨_, _, by simpa [memTransfer, awTransfer] using rdPart⟩

set_option maxHeartbeats 1000000 in
theorem auctionSafeTransferAfterDepositPrepTransferCallAnyMem
    {cA gh bl σ σ₀ A I}
    {g : Sat256} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {amount owner wethBefore aw freePtr : UInt256} {mem o : ByteArray} {k C : ℕ} {R : List UInt256}
    (hR : R.length ≤ 980)
    (hfree :
      auctionSettleAuctionDynMload64
          (auctionSettleAuctionDynTransferMem mem freePtr amount owner)
          (auctionSettleAuctionDynTransferAw aw freePtr) =
        freePtr)
    (hlen : UInt256.sub ((⟨68⟩ : UInt256) + freePtr) freePtr = ⟨68⟩)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3488⟩
      (solcAddrMask :: freePtr :: auctionSlotWord ⟨202⟩ σ' I :: amount :: ⟨3504541104⟩ :: wethBefore :: amount :: owner :: R)
      (auctionSettleAuctionDynTransferMem mem freePtr amount owner)
      (auctionSettleAuctionDynTransferAw aw freePtr) o (cA', σ') k C) :
    let weth := UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask
    ∃ gasWord k' C',
      RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3517⟩
        (gasWord :: weth :: ⟨0⟩ :: freePtr :: ⟨68⟩ :: freePtr :: ⟨32⟩ :: (⟨68⟩ + freePtr) :: ⟨2835717307⟩ :: weth :: amount :: owner :: R)
        (auctionSettleAuctionDynTransferMem mem freePtr amount owner)
        (auctionSettleAuctionDynTransferAwAfterMload64 aw freePtr)
        o (cA', σ') k' C' := by
  let weth := UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask
  let memTransfer := auctionSettleAuctionDynTransferMem mem freePtr amount owner
  let awTransfer := auctionSettleAuctionDynTransferAw aw freePtr
  let awAfterLoad := auctionSettleAuctionDynTransferAwAfterMload64 aw freePtr
  have rd3516Fn := evm_run rd with [
    swap1, swap2, and, swap4, pop, push4 ⟨2835717307⟩, swap3, pop,
    push1 ⟨68⟩, add, swap1, pop, push1 ⟨32⟩, push1 ⟨64⟩,
    raw mload (Cₘ awAfterLoad - Cₘ awTransfer) freePtr awAfterLoad (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by
        dsimp [awAfterLoad, awTransfer, auctionSettleAuctionDynTransferAwAfterMload64]))
      (by simpa [memTransfer, awTransfer, auctionSettleAuctionDynMload64] using hfree)
      (by rfl) (by evm_ov),
    dup1, dup4, sub, dup2, push0, dup8]
  have rd3516 := rd3516Fn
  rw [hlen] at rd3516
  obtain ⟨gasWord, rd3517⟩ := rd3516.gas (by native_decide) (by evm_ov)
  exact ⟨gasWord, _, _, by simpa [weth, memTransfer, awAfterLoad] using rd3517⟩

end Auction
