import Benchmarks.Auction.SettleAuctionCallPaths

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem auctionDispatch_settleCurrentAndCreateNewAuction {I : ExecutionEnv}
    (hsel : selIs I (auctionSelBytes 18)) :
    dispatchMsg auctionContract I.calldata = some settleAndCreateTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [initializeTransition, createBidTransition])
    (post := [settleAuctionTransition, pauseTransition, unpauseTransition,
      setTimeBufferTransition, setReservePriceTransition, setMinBidIncTransition,
      transferOwnershipTransition, renounceOwnershipTransition, ownerGetter, pausedGetter,
      nounsGetter, wethGetter, timeBufferGetter, reservePriceGetter, minBidIncGetter,
      durationGetter, auctionGetter])
    (ti := settleAndCreateTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = auctionSelBytes 18 := (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl
    all_goals
      simp [selectorOf, initializeSelectorBytes, createBidSelectorBytes, hcd, auctionSelBytes]
      native_decide
  · rw [selectorOf, settleAndCreateSelectorBytes]
    simpa [selIs, auctionSelBytes] using hsel

theorem auctionDecode_settleCurrentAndCreateNewAuction {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
      (settleAndCreateTransition.params.map Param.name)
      (transitionSignature settleAndCreateTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode auctionConfig.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem auctionReachSettleCurrentAndCreateNewAuctionBody {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hcode : I.code = auctionBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (auctionSelBytes 18)) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨901⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsel' : ((⟨#[0xf2, 0x5e, 0xff, 0xfc]⟩ : ByteArray) ==
      I.calldata.extract 0 4) = true := by
    simpa [selIs, auctionSelBytes] using hsel
  have hword : auctionSelWord I = ⟨0xf25efffc⟩ :=
    auctionSelWord_eq_of_beq I hsz 0xf2 0x5e 0xff 0xfc ⟨0xf25efffc⟩
      (by decide) hsel'
  obtain ⟨_, _, hsplit⟩ := auctionReachRootSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
  have hroot :
      UInt256.gt (armSelNat auctionBytecode auctionSplitPc) (auctionSelWord I) =
        ⟨0⟩ := by
    rw [hword]
    decide
  have h29 := RD.selectorSplitNotTakenAuto hsplit auctionSplitWellFormed hroot (by simp)
  have hupper :
      UInt256.gt (armSelNat auctionBytecode auctionUpperSplitPc) (auctionSelWord I) =
        ⟨0⟩ := by
    rw [hword]
    decide
  have h40 := RD.selectorSplitNotTakenAuto h29 auctionUpperSplitWellFormed hupper (by simp)
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat auctionBytecode
        (nthArmPc auctionBytecode auctionUpperMidFirstArmPc j)) (auctionSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> decide
  have htake :
      UInt256.eq
          (armSelNat auctionBytecode (nthArmPc auctionBytecode auctionUpperMidFirstArmPc 3))
          (auctionSelWord I) ≠
        ⟨0⟩ := by
    rw [hword]
    decide
  exact RD.dispatchTo (code := auctionBytecode) (ee := I) (g := g)
    (s0 := initState cA gh bl σ σ₀ g A I) (selWord := auctionSelWord I)
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (acc := (cA, σ)) ⟨901⟩ 3 h40
    (fun j hj => auctionUpperMidArmsWellFormed j (by omega)) heq0 htake
    (by jump_dest)
    (by native_decide)
    (by simp)

theorem auctionX_settleCurrentAndCreateNewAuction_callvalue_ne {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨901⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd901⟩ := hreach
  exact evm_run rd901 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨912⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv),
    push0, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem auctionSettleCurrentAndCreateNewAuctionX_toBody {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨901⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2573⟩
      [⟨413⟩, sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd901⟩ := hreach
  exact ⟨_, _, evm_run rd901 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨912⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push2 ⟨413⟩, push2 ⟨2573⟩, jump (by jump_dest)]⟩

theorem auctionSettleAndCreateTransitionReverts_statusEntered (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ = ⟨2⟩) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAndCreateTransition.body .reverted := by
  dsimp [settleAndCreateTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_settleAuction_status_ne_entered_false evm hstatus))

theorem auctionX_settleCurrentAndCreateNewAuction_revert_statusEntered
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hstatus : auctionSlotWord ⟨101⟩ σ I = ⟨2⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨901⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2573⟩ := auctionSettleCurrentAndCreateNewAuctionX_toBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := auctionSelWord I) hreach hwv
  have rd2578₀ := evm_run rd2573 with [jumpdest, push1 ⟨2⟩, push1 ⟨101⟩]
  obtain ⟨_, _, rd2578₁⟩ := rd2578₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2579⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2579⟩
      (auctionSlotWord ⟨101⟩ σ I :: ⟨2⟩ :: ⟨413⟩ :: auctionSelWord I :: [])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2578₁⟩
  have rd2580 := evm_run rd2579 with [sub]
  have hcond : UInt256.sub (auctionSlotWord ⟨101⟩ σ I) ⟨2⟩ = ⟨0⟩ := by
    rw [hstatus]
    decide
  have rd2587 := evm_run rd2580 with [
    push2 ⟨2607⟩, jumpiNT hcond,
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov)]
  have rd2591 := rd2587.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd2599 := evm_run rd2591 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 6 (solcErrorStringMem0 solcFreePtrMem) (UInt256.ofNat 5)
      (by decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨4⟩, add]
  obtain ⟨_, _, rd2599'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2599⟩
      [((⟨4⟩ : UInt256) + ⟨128⟩), ⟨413⟩, auctionSelWord I]
      (solcErrorStringMem0 solcFreePtrMem) (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C := by
    exact ⟨_, _, by simpa using rd2599⟩
  have rd5575 := evm_run rd2599' with [
    push2 ⟨994⟩, swap1, push2 ⟨5575⟩, jump (by jump_dest)]
  have rd5587 := evm_run rd5575 with [
    jumpdest, push1 ⟨32⟩, dup1, dup3,
    raw mstore 3 (solcErrorStringMem1 solcFreePtrMem) (UInt256.ofNat 6)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨31⟩, swap1, dup3, add,
    raw mstore 3 (solcErrorStringMem2 ⟨31⟩ solcFreePtrMem) (UInt256.ofNat 7)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd5620 := rd5587.pushConst auctionReentrancyGuardReentrantStringWord
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd5629₀ := evm_run rd5620 with [
    push1 ⟨64⟩, dup3, add,
    raw mstore 3
      (solcErrorStringMem3 ⟨31⟩ auctionReentrancyGuardReentrantStringWord solcFreePtrMem)
      (UInt256.ofNat 8) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨96⟩, add, swap1]
  have rd5629 := rd5629₀
  rw [show (⟨96⟩ : UInt256) + ((⟨4⟩ : UInt256) + ⟨128⟩) = ⟨228⟩ by decide]
    at rd5629
  have rd994 := evm_run rd5629 with [jump (by jump_dest)]
  have rd1001₀ := evm_run rd994 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨31⟩ auctionReentrancyGuardReentrantStringWord
        solcFreePtrMem_size solcFreePtrMem_read64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd1001 := rd1001₀
  rw [show UInt256.sub (⟨228⟩ : UInt256) ⟨128⟩ = ⟨100⟩ by decide] at rd1001
  exact evm_run rd1001 with [raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem auctionSettleCurrentAndCreateNewAuctionX_toStatusOpen {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨901⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2607⟩
      [⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2573⟩ := auctionSettleCurrentAndCreateNewAuctionX_toBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := auctionSelWord I) hreach hwv
  have rd2578₀ := evm_run rd2573 with [jumpdest, push1 ⟨2⟩, push1 ⟨101⟩]
  obtain ⟨_, _, rd2578₁⟩ := rd2578₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2579⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2579⟩
      (auctionSlotWord ⟨101⟩ σ I :: ⟨2⟩ :: ⟨413⟩ :: auctionSelWord I :: [])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2578₁⟩
  have rd2580 := evm_run rd2579 with [sub]
  have hcond : UInt256.sub (auctionSlotWord ⟨101⟩ σ I) ⟨2⟩ ≠ ⟨0⟩ :=
    u256_sub_ne_zero_of_ne hstatus
  exact ⟨_, _, evm_run rd2580 with [push2 ⟨2607⟩, jumpiT hcond (by jump_dest)]⟩

theorem auctionSettleAndCreateTransitionReverts_paused (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAndCreateTransition.body .reverted := by
  dsimp [settleAndCreateTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  have hpausedEnter :
      UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨51⟩)
          ⟨255⟩ ≠
        ⟨0⟩ := by
    have hload :
        Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm) evm.executionEnv.codeOwner
            ⟨51⟩ =
          Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩ := by
      simpa [auctionSettleAuctionEnterState] using
        storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
          (readSlot := ⟨51⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
    have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
      simpa [auctionSettleAuctionEnterState] using
        storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
    simpa [henv, hload] using hpaused
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_pause_notPaused_false
      (auctionSettleAuctionEnterState evm) hpausedEnter))

theorem auctionSettleAndCreateTransitionReverts_settleNotStarted (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ =
        ⟨0⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ = ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAndCreateTransition.body .reverted := by
  dsimp [settleAndCreateTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  have hpausedEnter :
      UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨51⟩)
          ⟨255⟩ =
        ⟨0⟩ := by
    have hload :
        Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm) evm.executionEnv.codeOwner
            ⟨51⟩ =
          Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩ := by
      simpa [auctionSettleAuctionEnterState] using
        storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
          (readSlot := ⟨51⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
    have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
      simpa [auctionSettleAuctionEnterState] using
        storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
    simpa [henv, hload] using hpaused
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_pause_notPaused_true (auctionSettleAuctionEnterState evm) hpausedEnter)) ?_
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := auctionSettleAuctionEnterState evm) (name := "_settleAuction") (args := [])
    (retVar := "_s") (argVals := []) (callee := settleAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionSettleAuctionBodyReverts_notStarted (auctionSettleAuctionEnterState evm) (by
      have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
          evm.executionEnv.codeOwner ⟨209⟩ =
            Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ := by
        simpa [auctionSettleAuctionEnterState] using
          storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
            (readSlot := ⟨209⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
      have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
        simpa [auctionSettleAuctionEnterState] using
          storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
      simpa [henv, hstart] using hload)))

theorem auctionSettleAndCreateTransitionReverts_settleAlreadySettled (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ =
        ⟨0⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) ≠
        ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAndCreateTransition.body .reverted := by
  dsimp [settleAndCreateTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  have hpausedEnter :
      UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨51⟩)
          ⟨255⟩ =
        ⟨0⟩ := by
    have hload :
        Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm) evm.executionEnv.codeOwner
            ⟨51⟩ =
          Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩ := by
      simpa [auctionSettleAuctionEnterState] using
        storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
          (readSlot := ⟨51⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
    have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
      simpa [auctionSettleAuctionEnterState] using
        storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
    simpa [henv, hload] using hpaused
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_pause_notPaused_true (auctionSettleAuctionEnterState evm) hpausedEnter)) ?_
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := auctionSettleAuctionEnterState evm) (name := "_settleAuction") (args := [])
    (retVar := "_s") (argVals := []) (callee := settleAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionSettleAuctionBodyReverts_alreadySettled (auctionSettleAuctionEnterState evm)
      (by
        have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            evm.executionEnv.codeOwner ⟨209⟩ =
              Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ := by
          simpa [auctionSettleAuctionEnterState] using
            storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
              (readSlot := ⟨209⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
        have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
          simpa [auctionSettleAuctionEnterState] using
            storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
        simpa [henv] using hload.symm ▸ hstart)
      (by
        have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            evm.executionEnv.codeOwner ⟨211⟩ =
              Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩ := by
          simpa [auctionSettleAuctionEnterState] using
            storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
              (readSlot := ⟨211⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
        have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
          simpa [auctionSettleAuctionEnterState] using
            storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
        simpa [henv] using hload.symm ▸ hsettled)))

theorem auctionSettleAndCreateTransitionReverts_settleTimeNotReached (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ =
        ⟨0⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAndCreateTransition.body .reverted := by
  dsimp [settleAndCreateTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  have hpausedEnter :
      UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨51⟩)
          ⟨255⟩ =
        ⟨0⟩ := by
    have hload :
        Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm) evm.executionEnv.codeOwner
            ⟨51⟩ =
          Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩ := by
      simpa [auctionSettleAuctionEnterState] using
        storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
          (readSlot := ⟨51⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
    have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
      simpa [auctionSettleAuctionEnterState] using
        storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
    simpa [henv, hload] using hpaused
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_pause_notPaused_true (auctionSettleAuctionEnterState evm) hpausedEnter)) ?_
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := auctionSettleAuctionEnterState evm) (name := "_settleAuction") (args := [])
    (retVar := "_s") (argVals := []) (callee := settleAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionSettleAuctionBodyReverts_timeNotReached (auctionSettleAuctionEnterState evm)
      (by
        have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            evm.executionEnv.codeOwner ⟨209⟩ =
              Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ := by
          simpa [auctionSettleAuctionEnterState] using
            storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
              (readSlot := ⟨209⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
        have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
          simpa [auctionSettleAuctionEnterState] using
            storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
        simpa [henv] using hload.symm ▸ hstart)
      (by
        have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            evm.executionEnv.codeOwner ⟨211⟩ =
              Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩ := by
          simpa [auctionSettleAuctionEnterState] using
            storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
              (readSlot := ⟨211⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
        have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
          simpa [auctionSettleAuctionEnterState] using
            storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
        simpa [henv, hload] using hsettled)
      (by
        have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            evm.executionEnv.codeOwner ⟨210⟩ =
              Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩ := by
          simpa [auctionSettleAuctionEnterState] using
            storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
              (readSlot := ⟨210⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
        have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
          simpa [auctionSettleAuctionEnterState] using
            storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
        simpa [henv, hload] using htime)))

theorem auctionSettleAndCreateTransitionReverts_settleBurnNoCode (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ =
        ⟨0⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat =
        AccountAddress.ofNat 0)
    (hnounsNoCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool false)) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAndCreateTransition.body .reverted := by
  dsimp [settleAndCreateTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  have hpausedEnter :
      UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨51⟩)
          ⟨255⟩ =
        ⟨0⟩ := by
    have hload :
        Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm) evm.executionEnv.codeOwner
            ⟨51⟩ =
          Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩ := by
      simpa [auctionSettleAuctionEnterState] using
        storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
          (readSlot := ⟨51⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
    have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
      simpa [auctionSettleAuctionEnterState] using
        storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
    simpa [henv, hload] using hpaused
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_pause_notPaused_true (auctionSettleAuctionEnterState evm) hpausedEnter)) ?_
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := auctionSettleAuctionEnterState evm) (name := "_settleAuction") (args := [])
    (retVar := "_s") (argVals := []) (callee := settleAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionSettleAuctionBodyReverts_burnNoCode (auctionSettleAuctionEnterState evm)
      (by
        have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            evm.executionEnv.codeOwner ⟨209⟩ =
              Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ := by
          simpa [auctionSettleAuctionEnterState] using
            storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
              (readSlot := ⟨209⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
        have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
          simpa [auctionSettleAuctionEnterState] using
            storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
        simpa [henv] using hload.symm ▸ hstart)
      (by
        have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            evm.executionEnv.codeOwner ⟨211⟩ =
              Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩ := by
          simpa [auctionSettleAuctionEnterState] using
            storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
              (readSlot := ⟨211⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
        have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
          simpa [auctionSettleAuctionEnterState] using
            storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
        simpa [henv, hload] using hsettled)
      (by
        have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            evm.executionEnv.codeOwner ⟨210⟩ =
              Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩ := by
          simpa [auctionSettleAuctionEnterState] using
            storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
              (readSlot := ⟨210⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
        have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
          simpa [auctionSettleAuctionEnterState] using
            storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
        simpa [henv, hload] using htime)
      (by
        have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            evm.executionEnv.codeOwner ⟨211⟩ =
              Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩ := by
          simpa [auctionSettleAuctionEnterState] using
            storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
              (readSlot := ⟨211⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
        have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
          simpa [auctionSettleAuctionEnterState] using
            storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
        simpa [henv, hload] using hbidder)
      hnounsNoCode))

theorem auctionSettleAndCreateTransitionReverts_settleTransferFromNoCode
    (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ =
        ⟨0⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnounsNoCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool false)) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAndCreateTransition.body .reverted := by
  dsimp [settleAndCreateTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  have hpausedEnter :
      UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨51⟩)
          ⟨255⟩ =
        ⟨0⟩ := by
    have hload :
        Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm) evm.executionEnv.codeOwner
            ⟨51⟩ =
          Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩ := by
      simpa [auctionSettleAuctionEnterState] using
        storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
          (readSlot := ⟨51⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
    have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
      simpa [auctionSettleAuctionEnterState] using
        storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
    simpa [henv, hload] using hpaused
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_pause_notPaused_true (auctionSettleAuctionEnterState evm) hpausedEnter)) ?_
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := auctionSettleAuctionEnterState evm) (name := "_settleAuction") (args := [])
    (retVar := "_s") (argVals := []) (callee := settleAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionSettleAuctionBodyReverts_transferFromNoCode (auctionSettleAuctionEnterState evm)
      (by
        have hload :
            Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm) evm.executionEnv.codeOwner
                ⟨209⟩ =
              Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ := by
          simpa [auctionSettleAuctionEnterState] using
            storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
              (readSlot := ⟨209⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
        have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
          simpa [auctionSettleAuctionEnterState] using
            storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
        simpa [henv] using hload.symm ▸ hstart)
      (by
        have hload :
            Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm) evm.executionEnv.codeOwner
                ⟨211⟩ =
              Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩ := by
          simpa [auctionSettleAuctionEnterState] using
            storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
              (readSlot := ⟨211⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
        have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
          simpa [auctionSettleAuctionEnterState] using
            storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
        simpa [henv, hload] using hsettled)
      (by
        have hload :
            Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm) evm.executionEnv.codeOwner
                ⟨210⟩ =
              Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩ := by
          simpa [auctionSettleAuctionEnterState] using
            storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
              (readSlot := ⟨210⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
        have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
          simpa [auctionSettleAuctionEnterState] using
            storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
        simpa [henv, hload] using htime)
      (by
        have hload :
            Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm) evm.executionEnv.codeOwner
                ⟨211⟩ =
              Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩ := by
          simpa [auctionSettleAuctionEnterState] using
            storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
              (readSlot := ⟨211⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
        have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
          simpa [auctionSettleAuctionEnterState] using
            storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
        simpa [henv, hload] using hbidder)
      hnounsNoCode))

theorem auctionX_settleCurrentAndCreateNewAuction_revert_paused {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hpaused : auctionPausedWord σ I ≠ ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨901⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2607⟩ := auctionSettleCurrentAndCreateNewAuctionX_toStatusOpen
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hwv hstatus hreach
  have rd2612 := evm_run rd2607 with [jumpdest, push1 ⟨2⟩, push1 ⟨101⟩]
  obtain ⟨_, _, rd2613₀⟩ := rd2612.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd2613⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2613⟩
      [⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionSettleAuctionEnterMap σ I) k C := by
    exact ⟨_, _, by simpa [auctionSettleAuctionEnterMap] using rd2613₀⟩
  have rd2615₀ := evm_run rd2613 with [push1 ⟨51⟩]
  obtain ⟨_, _, rd2615₁⟩ := rd2615₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2616⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2616⟩
      (auctionSlotWord ⟨51⟩ (auctionSettleAuctionEnterMap σ I) I :: ⟨413⟩ ::
        auctionSelWord I :: [])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionSettleAuctionEnterMap σ I) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2615₁⟩
  have rd2619 := evm_run rd2616 with [push1 ⟨255⟩, and, iszero]
  have hmask :
      UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ (auctionSettleAuctionEnterMap σ I) I) =
        auctionPausedWord σ I := by
    have hslot :
        auctionSlotWord ⟨51⟩ (auctionSettleAuctionEnterMap σ I) I =
          auctionSlotWord ⟨51⟩ σ I := by
      simpa [auctionSettleAuctionEnterMap, auctionSlotWord] using
        sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨51⟩ ⟨101⟩ ⟨2⟩ (by decide)
    rw [hslot, auctionPausedWord, u256_land_comm]
  have hcond :
      UInt256.isZero
          (UInt256.land ⟨255⟩
            (auctionSlotWord ⟨51⟩ (auctionSettleAuctionEnterMap σ I) I)) =
        ⟨0⟩ := by
    exact isZero_eq_zero_of_ne (by simpa [hmask] using hpaused)
  have rd2624 := evm_run rd2619 with [push2 ⟨2682⟩, jumpiNT hcond]
  have rd2627 := evm_run rd2624 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov)]
  have rd2631 := rd2627.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd2650 := evm_run rd2631 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 6 (solcErrorStringMem0 solcFreePtrMem) (UInt256.ofNat 5)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (solcErrorStringMem1 solcFreePtrMem) (UInt256.ofNat 6)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨16⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 3 (solcErrorStringMem2 ⟨16⟩ solcFreePtrMem) (UInt256.ofNat 7)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd2667 := rd2650.pushConst auctionPausablePausedRawStringWord
    (width := 16) (op := .PUSH16) (by decide) (by decide) (by evm_ov)
  have rd2670₀ := evm_run rd2667 with [push1 ⟨130⟩, shl]
  have hword :
      UInt256.shiftLeft auctionPausablePausedRawStringWord ⟨130⟩ =
        auctionPausablePausedStringWord := by
    native_decide
  have rd2670 := rd2670₀
  rw [hword] at rd2670
  have rd2678₀ := evm_run rd2670 with [
    push1 ⟨68⟩, dup3, add,
    raw mstore 3
      (solcErrorStringMem3 ⟨16⟩ auctionPausablePausedStringWord solcFreePtrMem)
      (UInt256.ofNat 8) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨100⟩, add]
  have rd2678 := rd2678₀
  rw [show (⟨100⟩ : UInt256) + ⟨128⟩ = ⟨228⟩ by decide] at rd2678
  have rd994 := evm_run rd2678 with [push2 ⟨994⟩, jump (by jump_dest)]
  have rd1001₀ := evm_run rd994 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨16⟩ auctionPausablePausedStringWord
        solcFreePtrMem_size solcFreePtrMem_read64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd1001 := rd1001₀
  rw [show UInt256.sub (⟨228⟩ : UInt256) ⟨128⟩ = ⟨100⟩ by decide] at rd1001
  exact evm_run rd1001 with [raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem auctionSettleCurrentAndCreateNewAuctionX_toInternalSettleAuction
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hpaused : auctionPausedWord σ I = ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨901⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4086⟩
      [⟨2690⟩, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionSettleAuctionEnterMap σ I) k C := by
  obtain ⟨_, _, rd2607⟩ := auctionSettleCurrentAndCreateNewAuctionX_toStatusOpen
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hwv hstatus hreach
  have rd2612 := evm_run rd2607 with [jumpdest, push1 ⟨2⟩, push1 ⟨101⟩]
  obtain ⟨_, _, rd2613₀⟩ := rd2612.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd2613⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2613⟩
      [⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionSettleAuctionEnterMap σ I) k C := by
    exact ⟨_, _, by simpa [auctionSettleAuctionEnterMap] using rd2613₀⟩
  have rd2615₀ := evm_run rd2613 with [push1 ⟨51⟩]
  obtain ⟨_, _, rd2615₁⟩ := rd2615₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2616⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2616⟩
      (auctionSlotWord ⟨51⟩ (auctionSettleAuctionEnterMap σ I) I :: ⟨413⟩ ::
        auctionSelWord I :: [])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionSettleAuctionEnterMap σ I) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2615₁⟩
  have rd2619 := evm_run rd2616 with [push1 ⟨255⟩, and, iszero]
  have hmask :
      UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ (auctionSettleAuctionEnterMap σ I) I) =
        auctionPausedWord σ I := by
    have hslot :
        auctionSlotWord ⟨51⟩ (auctionSettleAuctionEnterMap σ I) I =
          auctionSlotWord ⟨51⟩ σ I := by
      simpa [auctionSettleAuctionEnterMap, auctionSlotWord] using
        sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨51⟩ ⟨101⟩ ⟨2⟩ (by decide)
    rw [hslot, auctionPausedWord, u256_land_comm]
  have hcond :
      UInt256.isZero
          (UInt256.land ⟨255⟩
            (auctionSlotWord ⟨51⟩ (auctionSettleAuctionEnterMap σ I) I)) ≠
        ⟨0⟩ := by
    rw [hmask, hpaused]
    decide
  have rd2682 := evm_run rd2619 with [push2 ⟨2682⟩, jumpiT hcond (by jump_dest)]
  exact ⟨_, _, evm_run rd2682 with [
    jumpdest, push2 ⟨2690⟩, push2 ⟨4086⟩, jump (by jump_dest)]⟩

theorem auctionInternalSettleAuction_toSnapshotCheck {cA gh bl σ σ₀ A I} {g : Sat256}
    {ret : UInt256}
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4086⟩ [ret, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionSettleAuctionEnterMap σ I) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4162⟩
      [⟨128⟩, auctionAuctionStartWord (auctionSettleAuctionEnterMap σ I) I, ret,
        ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem
        (auctionAuctionNounWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionStartWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionEndWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I))
        (auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I)))
      (UInt256.ofNat 10) ByteArray.empty (cA, auctionSettleAuctionEnterMap σ I) k C := by
  let σ1 := auctionSettleAuctionEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  obtain ⟨_, _, rd4086⟩ := hreach
  have rd4096 := evm_run rd4086 with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push1 ⟨192⟩, dup2, add, dup3,
    raw mstore 0 auctionSettleAuctionSnapshotFreeMem (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  obtain ⟨_, _, rd4100₀⟩ := (evm_run rd4096 with [push1 ⟨207⟩]).sload
    (by decide) (by evm_ov)
  obtain ⟨_, _, rd4100⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4100⟩
      (noun :: ⟨128⟩ :: ⟨64⟩ :: ret :: ⟨413⟩ :: auctionSelWord I :: [])
      auctionSettleAuctionSnapshotFreeMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ1) k C := by
    exact ⟨_, _, by simpa [noun, auctionAuctionNounWord, auctionSlotWord, σ1] using rd4100₀⟩
  have rd4102 := evm_run rd4100 with [
    dup2,
    raw mstore 6 (auctionSettleAuctionSnapshotNounMem noun) (UInt256.ofNat 5)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  obtain ⟨_, _, rd4105₀⟩ := (evm_run rd4102 with [push1 ⟨208⟩]).sload
    (by decide) (by evm_ov)
  obtain ⟨_, _, rd4105⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4105⟩
      (amount :: ⟨128⟩ :: ⟨64⟩ :: ret :: ⟨413⟩ :: auctionSelWord I :: [])
      (auctionSettleAuctionSnapshotNounMem noun) (UInt256.ofNat 5) ByteArray.empty
      (cA, σ1) k C := by
    exact ⟨_, _, by simpa [amount, auctionAuctionAmountWord, auctionSlotWord, σ1] using rd4105₀⟩
  have rd4109 := evm_run rd4105 with [
    push1 ⟨32⟩, dup3, add,
    raw mstore 3 (auctionSettleAuctionSnapshotAmountMem noun amount) (UInt256.ofNat 6)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  obtain ⟨_, _, rd4113₀⟩ := (evm_run rd4109 with [push1 ⟨209⟩]).sload
    (by decide) (by evm_ov)
  obtain ⟨_, _, rd4113⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4113⟩
      (start :: ⟨128⟩ :: ⟨64⟩ :: ret :: ⟨413⟩ :: auctionSelWord I :: [])
      (auctionSettleAuctionSnapshotAmountMem noun amount) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by simpa [start, auctionAuctionStartWord, auctionSlotWord, σ1] using rd4113₀⟩
  have rd4119 := evm_run rd4113 with [
    swap2, dup2, add, dup3, swap1,
    raw mstore 3 (auctionSettleAuctionSnapshotStartMem noun amount start)
      (UInt256.ofNat 7) (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  obtain ⟨_, _, rd4122₀⟩ := (evm_run rd4119 with [push1 ⟨210⟩]).sload
    (by decide) (by evm_ov)
  obtain ⟨_, _, rd4122⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4122⟩
      (finish :: ⟨128⟩ :: start :: ret :: ⟨413⟩ :: auctionSelWord I :: [])
      (auctionSettleAuctionSnapshotStartMem noun amount start) (UInt256.ofNat 7)
      ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by simpa [finish, auctionAuctionEndWord, auctionSlotWord, σ1] using rd4122₀⟩
  have rd4126 := evm_run rd4122 with [
    push1 ⟨96⟩, dup3, add,
    raw mstore 3 (auctionSettleAuctionSnapshotEndMem noun amount start finish)
      (UInt256.ofNat 8) (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  obtain ⟨_, _, rd4130₀⟩ := (evm_run rd4126 with [push1 ⟨211⟩]).sload
    (by decide) (by evm_ov)
  obtain ⟨_, _, rd4130⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4130⟩
      (packed :: ⟨128⟩ :: start :: ret :: ⟨413⟩ :: auctionSelWord I :: [])
      (auctionSettleAuctionSnapshotEndMem noun amount start finish) (UInt256.ofNat 8)
      ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by simpa [packed, auctionAuctionPackedWord, auctionSlotWord, σ1] using rd4130₀⟩
  have rd4144 := evm_run rd4130 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and,
    push1 ⟨128⟩, dup4, add]
  have rd4145 := evm_run rd4144 with [
    raw mstore 3 (auctionSettleAuctionSnapshotBidderMem noun amount start finish bidder)
      (UInt256.ofNat 9) (by decide) mem_cost
      (by
        dsimp [bidder, auctionPackedBidderWord]
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask by native_decide]
        rw [show ((⟨128⟩ : UInt256) + ⟨128⟩).toNat = 256 by decide]
        rfl)
      (by decide) (by evm_ov)]
  have rd4161 := evm_run rd4145 with [
    push1 ⟨1⟩, push1 ⟨160⟩, shl, swap1, div, push1 ⟨255⟩, and,
    iszero, iszero, push1 ⟨160⟩, dup3, add,
    raw mstore 3 (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) (by decide) mem_cost
      (by
        dsimp [settled, auctionPackedSettledEVMReturnWord, auctionPackedSettledEVMWord,
          auctionPackedSettledBaseWord]
        rfl)
      (by decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [σ1, noun, amount, start, finish, packed, bidder, settled] using rd4161⟩

theorem auctionInternalSettleAuction_revert_notStarted {cA gh bl σ σ₀ A I} {g : Sat256}
    {ret : UInt256}
    (hstart : auctionAuctionStartWord σ I = ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4086⟩ [ret, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionSettleAuctionEnterMap σ I) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σ1 := auctionSettleAuctionEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  have hstartEnter : start = ⟨0⟩ := by
    have hpres :
        auctionAuctionStartWord (auctionSettleAuctionEnterMap σ I) I =
          auctionAuctionStartWord σ I := by
      unfold auctionAuctionStartWord auctionSettleAuctionEnterMap auctionSlotWord
      simpa using
        sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨209⟩ ⟨101⟩ ⟨2⟩ (by decide)
    simpa [start, σ1] using hpres.trans hstart
  obtain ⟨_, _, rd4162⟩ := auctionInternalSettleAuction_toSnapshotCheck
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (ret := ret) hreach
  obtain ⟨_, _, rd4162'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4162⟩
      [⟨128⟩, start, ret, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled] using rd4162⟩
  have hcond : UInt256.sub (⟨0⟩ : UInt256) start = ⟨0⟩ := by
    rw [hstartEnter]
    decide
  have rd4169 := evm_run rd4162' with [
    swap1, push0, sub, push2 ⟨4231⟩, jumpiNT hcond]
  have rd4171 := evm_run rd4169 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov)]
  have rd4179 := rd4171.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd4194 := evm_run rd4179 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 3 (auctionAuctionHasntStartedMem0 noun amount start finish bidder settled)
      (UInt256.ofNat 11) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (auctionAuctionHasntStartedMem1 noun amount start finish bidder settled)
      (UInt256.ofNat 12) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨20⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 3 (auctionAuctionHasntStartedMem2 noun amount start finish bidder settled)
      (UInt256.ofNat 13) (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd4219 := rd4194.pushConst auctionAuctionHasntBegunRawStringWord
    (width := 20) (op := .PUSH20) (by decide) (by decide) (by evm_ov)
  have rd4219₀ := evm_run rd4219 with [push1 ⟨97⟩, shl]
  have hword :
      UInt256.shiftLeft auctionAuctionHasntBegunRawStringWord ⟨97⟩ =
        auctionAuctionHasntBegunStringWord := by
    native_decide
  have rd4219' := rd4219₀
  rw [hword] at rd4219'
  have rd4227₀ := evm_run rd4219' with [
    push1 ⟨68⟩, dup3, add,
    raw mstore 3 (auctionAuctionHasntStartedMem3 noun amount start finish bidder settled)
      (UInt256.ofNat 14) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨100⟩, add]
  have rd4227 := rd4227₀
  rw [show (⟨100⟩ : UInt256) + ⟨320⟩ = ⟨420⟩ by decide] at rd4227
  have rd994 := evm_run rd4227 with [push2 ⟨994⟩, jump (by jump_dest)]
  have rd1001₀ := evm_run rd994 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 14) (by decide)
      mem_cost
      (auctionAuctionHasntStartedMem3_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd1001 := rd1001₀
  rw [show UInt256.sub (⟨420⟩ : UInt256) ⟨320⟩ = ⟨100⟩ by decide] at rd1001
  exact evm_run rd1001 with [raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem auctionInternalSettleAuction_revert_alreadySettled {cA gh bl σ σ₀ A I}
    {g : Sat256} {ret : UInt256}
    (hstart : auctionAuctionStartWord σ I ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord (auctionAuctionPackedWord σ I) ≠ ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4086⟩ [ret, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionSettleAuctionEnterMap σ I) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σ1 := auctionSettleAuctionEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  have hstartPres : start = auctionAuctionStartWord σ I := by
    have hpres :
        auctionAuctionStartWord (auctionSettleAuctionEnterMap σ I) I =
          auctionAuctionStartWord σ I := by
      unfold auctionAuctionStartWord auctionSettleAuctionEnterMap auctionSlotWord
      simpa using
        sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨209⟩ ⟨101⟩ ⟨2⟩ (by decide)
    simpa [start, σ1] using hpres
  have hstartEnter : start ≠ ⟨0⟩ := by
    intro hzero
    exact hstart (hstartPres.symm.trans hzero)
  have hpackedPres : packed = auctionAuctionPackedWord σ I := by
    have hpres :
        auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I =
          auctionAuctionPackedWord σ I := by
      unfold auctionAuctionPackedWord auctionSettleAuctionEnterMap auctionSlotWord
      simpa using
        sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨211⟩ ⟨101⟩ ⟨2⟩ (by decide)
    simpa [packed, σ1] using hpres
  have hsettledEnter : auctionPackedSettledWord packed ≠ ⟨0⟩ := by
    intro hzero
    exact hsettled (by simpa [hpackedPres] using hzero)
  have hsettledEVM : auctionPackedSettledEVMWord packed ≠ ⟨0⟩ := by
    intro hzero
    have hzero' : auctionPackedSettledWord packed = ⟨0⟩ := by
      simpa [auctionPackedSettledEVMWord, auctionPackedSettledWord, u256_land_comm] using hzero
    exact hsettledEnter hzero'
  obtain ⟨_, _, rd4162⟩ := auctionInternalSettleAuction_toSnapshotCheck
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (ret := ret) hreach
  obtain ⟨_, _, rd4162'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4162⟩
      [⟨128⟩, start, ret, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled] using rd4162⟩
  have hstartCond : UInt256.sub (⟨0⟩ : UInt256) start ≠ ⟨0⟩ := by
    exact u256_sub_ne_zero_of_ne (by intro h; exact hstartEnter h.symm)
  have rd4231 := evm_run rd4162' with [
    swap1, push0, sub, push2 ⟨4231⟩, jumpiT hstartCond (by jump_dest)]
  have rd4237 := evm_run rd4231 with [
    jumpdest, dup1, push1 ⟨160⟩, add,
    raw mload 0 settled (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload288 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    iszero]
  have hsettledRet : settled = ⟨1⟩ := by
    dsimp [settled, auctionPackedSettledEVMReturnWord]
    rw [isZero_eq_zero_of_ne hsettledEVM]
    decide
  have hsettledCond : UInt256.isZero settled = ⟨0⟩ := by
    rw [hsettledRet]
    decide
  have rd4242 := evm_run rd4237 with [push2 ⟨4313⟩, jumpiNT hsettledCond]
  have rd4244 := evm_run rd4242 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov)]
  have rd4252 := rd4244.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd4267 := evm_run rd4252 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 3 (auctionAuctionHasntStartedMem0 noun amount start finish bidder settled)
      (UInt256.ofNat 11) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add, dup2, swap1,
    raw mstore 3 (auctionAuctionHasntStartedMem1 noun amount start finish bidder settled)
      (UInt256.ofNat 12) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, dup3, add,
    raw mstore 3 (auctionAuctionAlreadySettledMem2 noun amount start finish bidder settled)
      (UInt256.ofNat 13) (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd4301 := rd4267.pushConst auctionAuctionAlreadySettledStringWord
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd4309₀ := evm_run rd4301 with [
    push1 ⟨68⟩, dup3, add,
    raw mstore 3 (auctionAuctionAlreadySettledMem3 noun amount start finish bidder settled)
      (UInt256.ofNat 14) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨100⟩, add]
  have rd4309 := rd4309₀
  rw [show (⟨100⟩ : UInt256) + ⟨320⟩ = ⟨420⟩ by decide] at rd4309
  have rd994 := evm_run rd4309 with [push2 ⟨994⟩, jump (by jump_dest)]
  have rd1001₀ := evm_run rd994 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 14) (by decide)
      mem_cost
      (auctionAuctionAlreadySettledMem3_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd1001 := rd1001₀
  rw [show UInt256.sub (⟨420⟩ : UInt256) ⟨320⟩ = ⟨100⟩ by decide] at rd1001
  exact evm_run rd1001 with [raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem auctionInternalSettleAuction_revert_timeNotReached {cA gh bl σ σ₀ A I}
    {g : Sat256} {ret : UInt256}
    (hstart : auctionAuctionStartWord σ I ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord (auctionAuctionPackedWord σ I) = ⟨0⟩)
    (htime : (UInt256.ofNat I.header.timestamp).toNat < (auctionAuctionEndWord σ I).toNat)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4086⟩ [ret, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionSettleAuctionEnterMap σ I) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σ1 := auctionSettleAuctionEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  have hstartPres : start = auctionAuctionStartWord σ I := by
    have hpres :
        auctionAuctionStartWord (auctionSettleAuctionEnterMap σ I) I =
          auctionAuctionStartWord σ I := by
      unfold auctionAuctionStartWord auctionSettleAuctionEnterMap auctionSlotWord
      simpa using
        sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨209⟩ ⟨101⟩ ⟨2⟩ (by decide)
    simpa [start, σ1] using hpres
  have hstartEnter : start ≠ ⟨0⟩ := by
    intro hzero
    exact hstart (hstartPres.symm.trans hzero)
  have hfinishPres : finish = auctionAuctionEndWord σ I := by
    have hpres :
        auctionAuctionEndWord (auctionSettleAuctionEnterMap σ I) I =
          auctionAuctionEndWord σ I := by
      unfold auctionAuctionEndWord auctionSettleAuctionEnterMap auctionSlotWord
      simpa using
        sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨210⟩ ⟨101⟩ ⟨2⟩ (by decide)
    simpa [finish, σ1] using hpres
  have hpackedPres : packed = auctionAuctionPackedWord σ I := by
    have hpres :
        auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I =
          auctionAuctionPackedWord σ I := by
      unfold auctionAuctionPackedWord auctionSettleAuctionEnterMap auctionSlotWord
      simpa using
        sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨211⟩ ⟨101⟩ ⟨2⟩ (by decide)
    simpa [packed, σ1] using hpres
  have hsettledEnter : auctionPackedSettledWord packed = ⟨0⟩ := by
    simpa [hpackedPres] using hsettled
  have hsettledEVM : auctionPackedSettledEVMWord packed = ⟨0⟩ := by
    simpa [auctionPackedSettledEVMWord, auctionPackedSettledWord, u256_land_comm]
      using hsettledEnter
  obtain ⟨_, _, rd4162⟩ := auctionInternalSettleAuction_toSnapshotCheck
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (ret := ret) hreach
  obtain ⟨_, _, rd4162'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4162⟩
      [⟨128⟩, start, ret, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled] using rd4162⟩
  have hstartCond : UInt256.sub (⟨0⟩ : UInt256) start ≠ ⟨0⟩ := by
    exact u256_sub_ne_zero_of_ne (by intro h; exact hstartEnter h.symm)
  have rd4231 := evm_run rd4162' with [
    swap1, push0, sub, push2 ⟨4231⟩, jumpiT hstartCond (by jump_dest)]
  have rd4237 := evm_run rd4231 with [
    jumpdest, dup1, push1 ⟨160⟩, add,
    raw mload 0 settled (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload288 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    iszero]
  have hsettledRet : settled = ⟨0⟩ := by
    dsimp [settled, auctionPackedSettledEVMReturnWord]
    rw [hsettledEVM]
    decide
  have hsettledCond : UInt256.isZero settled ≠ ⟨0⟩ := by
    rw [hsettledRet]
    decide
  have rd4313 := evm_run rd4237 with [push2 ⟨4313⟩, jumpiT hsettledCond (by jump_dest)]
  have rd4321 := evm_run rd4313 with [
    jumpdest, dup1, push1 ⟨96⟩, add,
    raw mload 0 finish (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload224 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    timestamp, lt, iszero]
  have hlt : UInt256.lt (UInt256.ofNat I.header.timestamp) finish = ⟨1⟩ := by
    apply ult_one
    simpa [hfinishPres] using htime
  have htimeCond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat I.header.timestamp) finish) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rd4328 := evm_run rd4321 with [
    push2 ⟨4397⟩, jumpiNT htimeCond,
    push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov)]
  have rd4335 := rd4328.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd4351 := evm_run rd4335 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 3 (auctionAuctionHasntStartedMem0 noun amount start finish bidder settled)
      (UInt256.ofNat 11) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (auctionAuctionHasntStartedMem1 noun amount start finish bidder settled)
      (UInt256.ofNat 12) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨24⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 3 (auctionAuctionHasntCompletedMem2 noun amount start finish bidder settled)
      (UInt256.ofNat 13) (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd4385 := rd4351.pushConst auctionAuctionHasntCompletedStringWord
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd4393₀ := evm_run rd4385 with [
    push1 ⟨68⟩, dup3, add,
    raw mstore 3 (auctionAuctionHasntCompletedMem3 noun amount start finish bidder settled)
      (UInt256.ofNat 14) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨100⟩, add]
  have rd4393 := rd4393₀
  rw [show (⟨100⟩ : UInt256) + ⟨320⟩ = ⟨420⟩ by decide] at rd4393
  have rd994 := evm_run rd4393 with [push2 ⟨994⟩, jump (by jump_dest)]
  have rd1001₀ := evm_run rd994 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 14) (by decide)
      mem_cost
      (auctionAuctionHasntCompletedMem3_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd1001 := rd1001₀
  rw [show UInt256.sub (⟨420⟩ : UInt256) ⟨320⟩ = ⟨100⟩ by decide] at rd1001
  exact evm_run rd1001 with [raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem auctionInternalSettleAuction_toMarkSettled {cA gh bl σ σ₀ A I} {g : Sat256}
    {ret : UInt256}
    (hperm : I.perm = true)
    (hstart : auctionAuctionStartWord σ I ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord (auctionAuctionPackedWord σ I) = ⟨0⟩)
    (htime : ¬ (UInt256.ofNat I.header.timestamp).toNat < (auctionAuctionEndWord σ I).toNat)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4086⟩ [ret, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionSettleAuctionEnterMap σ I) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4417⟩
      [⟨128⟩, ret, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem
        (auctionAuctionNounWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionStartWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionEndWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I))
        (auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I)))
      (UInt256.ofNat 10) ByteArray.empty
      (cA, auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I) k C := by
  let σ1 := auctionSettleAuctionEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  have hstartPres : start = auctionAuctionStartWord σ I := by
    have hpres :
        auctionAuctionStartWord (auctionSettleAuctionEnterMap σ I) I =
          auctionAuctionStartWord σ I := by
      unfold auctionAuctionStartWord auctionSettleAuctionEnterMap auctionSlotWord
      simpa using
        sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨209⟩ ⟨101⟩ ⟨2⟩ (by decide)
    simpa [start, σ1] using hpres
  have hstartEnter : start ≠ ⟨0⟩ := by
    intro hzero
    exact hstart (hstartPres.symm.trans hzero)
  have hfinishPres : finish = auctionAuctionEndWord σ I := by
    have hpres :
        auctionAuctionEndWord (auctionSettleAuctionEnterMap σ I) I =
          auctionAuctionEndWord σ I := by
      unfold auctionAuctionEndWord auctionSettleAuctionEnterMap auctionSlotWord
      simpa using
        sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨210⟩ ⟨101⟩ ⟨2⟩ (by decide)
    simpa [finish, σ1] using hpres
  have hpackedPres : packed = auctionAuctionPackedWord σ I := by
    have hpres :
        auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I =
          auctionAuctionPackedWord σ I := by
      unfold auctionAuctionPackedWord auctionSettleAuctionEnterMap auctionSlotWord
      simpa using
        sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨211⟩ ⟨101⟩ ⟨2⟩ (by decide)
    simpa [packed, σ1] using hpres
  have hsettledEnter : auctionPackedSettledWord packed = ⟨0⟩ := by
    simpa [hpackedPres] using hsettled
  have hsettledEVM : auctionPackedSettledEVMWord packed = ⟨0⟩ := by
    simpa [auctionPackedSettledEVMWord, auctionPackedSettledWord, u256_land_comm]
      using hsettledEnter
  obtain ⟨_, _, rd4162⟩ := auctionInternalSettleAuction_toSnapshotCheck
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (ret := ret) hreach
  obtain ⟨_, _, rd4162'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4162⟩
      [⟨128⟩, start, ret, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled] using rd4162⟩
  have hstartCond : UInt256.sub (⟨0⟩ : UInt256) start ≠ ⟨0⟩ := by
    exact u256_sub_ne_zero_of_ne (by intro h; exact hstartEnter h.symm)
  have rd4231 := evm_run rd4162' with [
    swap1, push0, sub, push2 ⟨4231⟩, jumpiT hstartCond (by jump_dest)]
  have rd4237 := evm_run rd4231 with [
    jumpdest, dup1, push1 ⟨160⟩, add,
    raw mload 0 settled (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload288 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    iszero]
  have hsettledRet : settled = ⟨0⟩ := by
    dsimp [settled, auctionPackedSettledEVMReturnWord]
    rw [hsettledEVM]
    decide
  have hsettledCond : UInt256.isZero settled ≠ ⟨0⟩ := by
    rw [hsettledRet]
    decide
  have rd4313 := evm_run rd4237 with [push2 ⟨4313⟩, jumpiT hsettledCond (by jump_dest)]
  have rd4321 := evm_run rd4313 with [
    jumpdest, dup1, push1 ⟨96⟩, add,
    raw mload 0 finish (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload224 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    timestamp, lt, iszero]
  have htimeLe : finish.toNat ≤ (UInt256.ofNat I.header.timestamp).toNat := by
    apply Nat.le_of_not_gt
    simpa [hfinishPres] using htime
  have hlt : UInt256.lt (UInt256.ofNat I.header.timestamp) finish = ⟨0⟩ :=
    ult_zero htimeLe
  have htimeCond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat I.header.timestamp) finish) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rd4397 := evm_run rd4321 with [push2 ⟨4397⟩, jumpiT htimeCond (by jump_dest)]
  have rd4401₀ := evm_run rd4397 with [jumpdest, push1 ⟨211⟩, dup1]
  obtain ⟨_, _, rd4402₀⟩ := rd4401₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd4402⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4402⟩
      (packed :: ⟨211⟩ :: ⟨128⟩ :: ret :: ⟨413⟩ :: auctionSelWord I :: [])
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by simpa [packed, auctionAuctionPackedWord, auctionSlotWord, σ1]
      using rd4402₀⟩
  have rd4416₀ := evm_run rd4402 with [
    push1 ⟨255⟩, push1 ⟨160⟩, shl, not, and,
    push1 ⟨1⟩, push1 ⟨160⟩, shl, lor, swap1]
  have hpost :
      UInt256.lor (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)
          (UInt256.land (UInt256.lnot (UInt256.shiftLeft (⟨255⟩ : UInt256) ⟨160⟩))
            packed) =
        auctionSetBoolOffset20TrueWord packed :=
    auctionSetBoolOffset20TrueWord_eq_evm packed
  have rd4416 := rd4416₀
  rw [hpost] at rd4416
  obtain ⟨_, _, rd4417₀⟩ := rd4416.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [auctionSettleAuctionMarkSettledMap, packed, auctionAuctionPackedWord, auctionSlotWord,
      σ1, noun, amount, start, finish, bidder, settled] using rd4417₀⟩

theorem auctionInternalSettleAuction_markSettledToBurnPath {cA gh bl σ σ₀ A I}
    {g : Sat256} {ret : UInt256}
    (hbidderZero :
      auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I) =
        ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4417⟩
      [⟨128⟩, ret, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem
        (auctionAuctionNounWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionStartWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionEndWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I))
        (auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I)))
      (UInt256.ofNat 10) ByteArray.empty
      (cA, auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4435⟩
      [⟨128⟩, ret, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem
        (auctionAuctionNounWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionStartWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionEndWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I))
        (auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I)))
      (UInt256.ofNat 10) ByteArray.empty
      (cA, auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I) k C := by
  let σ1 := auctionSettleAuctionEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  let mem := auctionSettleAuctionSnapshotMem noun amount start finish bidder settled
  let σ2 := auctionSettleAuctionMarkSettledMap σ1 I
  obtain ⟨_, _, rd4417⟩ := hreach
  obtain ⟨_, _, rd4417'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4417⟩
      [⟨128⟩, ret, ⟨413⟩, auctionSelWord I] mem (UInt256.ofNat 10)
      ByteArray.empty (cA, σ2) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled, mem, σ2] using rd4417⟩
  have rd4434 := evm_run rd4417' with [
    push1 ⟨128⟩, dup2, add,
    raw mload 0 bidder (UInt256.ofNat 10) (by decide)
      mem_cost
      (by simpa [mem] using
        auctionSettleAuctionSnapshotMem_mload256 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    push2 ⟨4536⟩]
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hcond :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          bidder =
        ⟨0⟩ := by
    rw [hmask]
    simp [bidder, packed, σ1, hbidderZero]
    decide
  exact ⟨_, _, by simpa using evm_run rd4434 with [jumpiNT hcond]⟩

theorem auctionInternalSettleAuction_revert_burnNoCode {cA gh bl σ σ₀ A I}
    {g : Sat256} {ret : UInt256}
    (hbidderZero :
      auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I) =
        ⟨0⟩)
    (hnounsNoCode :
      Reasoning.Theory.uniswapExtCodeSizeWord
        (auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I)
        (UInt256.land
          (auctionSlotWord ⟨201⟩
            (auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I) I)
          solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4417⟩
      [⟨128⟩, ret, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem
        (auctionAuctionNounWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionStartWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionEndWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I))
        (auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I)))
      (UInt256.ofNat 10) ByteArray.empty
      (cA, auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σ1 := auctionSettleAuctionEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  let mem := auctionSettleAuctionSnapshotMem noun amount start finish bidder settled
  let σ2 := auctionSettleAuctionMarkSettledMap σ1 I
  let nounsWord := auctionSlotWord ⟨201⟩ σ2 I
  let target := UInt256.land nounsWord solcAddrMask
  obtain ⟨_, _, rd4435⟩ := auctionInternalSettleAuction_markSettledToBurnPath
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (ret := ret) hbidderZero hreach
  obtain ⟨_, _, rd4435'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4435⟩
      [⟨128⟩, ret, ⟨413⟩, auctionSelWord I] mem (UInt256.ofNat 10)
      ByteArray.empty (cA, σ2) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled, mem, σ2] using rd4435⟩
  have rd4437 := evm_run rd4435' with [push1 ⟨201⟩]
  obtain ⟨_, _, rd4438₀⟩ := rd4437.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd4438⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4438⟩
      (nounsWord :: [⟨128⟩, ret, ⟨413⟩, auctionSelWord I])
      mem (UInt256.ofNat 10) ByteArray.empty (cA, σ2) k C := by
    exact ⟨_, _, by simpa [nounsWord, auctionSlotWord] using rd4438₀⟩
  let memSel := auctionSettleAuctionBurnSelectorMem noun amount start finish bidder settled
  let memCall := auctionSettleAuctionBurnCallMem noun amount start finish bidder settled
  have rd4498 := evm_run rd4438 with [
    dup2,
    raw mload 0 noun (UInt256.ofNat 10) (by native_decide)
      mem_cost (by simpa [mem] using
        auctionSettleAuctionSnapshotMem_mload128 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 10) (by native_decide)
      mem_cost (by simpa [mem] using
        auctionSettleAuctionSnapshotMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push4 ⟨139644301⟩, push1 ⟨227⟩, shl, dup2,
    raw mstore 3 memSel (UInt256.ofNat 11) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap3, and, swap2,
    push4 ⟨1117154408⟩, swap2, push2 ⟨4486⟩, swap2, push1 ⟨4⟩, add, swap1, dup2,
    raw mstore 3 memCall (UInt256.ofNat 12) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, swap1, jump (by jump_dest),
    jumpdest, push0, push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 12) (by native_decide)
      mem_cost (by simpa [memCall] using
        auctionSettleAuctionBurnCallMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    dup1, dup4, sub, dup2, push0, dup8, dup1]
  exact auctionExtcodesizeGuardMissingPush0 (pc := ⟨4498⟩) (okPc := ⟨4509⟩)
    (by simpa [target, nounsWord, mem, memSel, memCall,
      auctionSettleAuctionBurnSelectorShifted, auctionSettleAuctionBurnSelectorMem,
      auctionSettleAuctionBurnCallMem, solcAddrMask] using rd4498)
    (by simpa [target, nounsWord, σ1, σ2] using hnounsNoCode)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem auctionInternalSettleAuction_markSettledToTransferFromPath
    {cA gh bl σ σ₀ A I} {g : Sat256} {ret : UInt256}
    (hbidderNZ :
      auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I) ≠
        ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4417⟩
      [⟨128⟩, ret, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem
        (auctionAuctionNounWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionStartWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionEndWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I))
        (auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I)))
      (UInt256.ofNat 10) ByteArray.empty
      (cA, auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4536⟩
      [⟨128⟩, ret, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem
        (auctionAuctionNounWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionStartWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionEndWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I))
        (auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I)))
      (UInt256.ofNat 10) ByteArray.empty
      (cA, auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I) k C := by
  let σ1 := auctionSettleAuctionEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  let mem := auctionSettleAuctionSnapshotMem noun amount start finish bidder settled
  let σ2 := auctionSettleAuctionMarkSettledMap σ1 I
  obtain ⟨_, _, rd4417⟩ := hreach
  obtain ⟨_, _, rd4417'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4417⟩
      [⟨128⟩, ret, ⟨413⟩, auctionSelWord I] mem (UInt256.ofNat 10)
      ByteArray.empty (cA, σ2) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled, mem, σ2] using rd4417⟩
  have rd4434 := evm_run rd4417' with [
    push1 ⟨128⟩, dup2, add,
    raw mload 0 bidder (UInt256.ofNat 10) (by decide)
      mem_cost
      (by simpa [mem] using
        auctionSettleAuctionSnapshotMem_mload256 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    push2 ⟨4536⟩]
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hbidderClean : UInt256.land solcAddrMask bidder = bidder := by
    dsimp [bidder, auctionPackedBidderWord]
    rw [u256_land_comm solcAddrMask (UInt256.land packed solcAddrMask)]
    exact solcAddrMask_clean (solcAddrMask_result_canonical packed)
  have hcond :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          bidder ≠
        ⟨0⟩ := by
    rw [hmask, hbidderClean]
    simpa [bidder, packed, σ1] using hbidderNZ
  exact ⟨_, _, by
    simpa [σ1, noun, amount, start, finish, packed, bidder, settled, mem, σ2]
      using evm_run rd4434 with [jumpiT hcond (by jump_dest)]⟩

theorem auctionInternalSettleAuction_revert_transferFromNoCode {cA gh bl σ σ₀ A I}
    {g : Sat256} {ret : UInt256}
    (hbidderNZ :
      auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I) ≠
        ⟨0⟩)
    (hnounsNoCode :
      Reasoning.Theory.uniswapExtCodeSizeWord
        (auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I)
        (UInt256.land
          (auctionSlotWord ⟨201⟩
            (auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I) I)
          solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4417⟩
      [⟨128⟩, ret, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem
        (auctionAuctionNounWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionStartWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionEndWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I))
        (auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I)))
      (UInt256.ofNat 10) ByteArray.empty
      (cA, auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σ1 := auctionSettleAuctionEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  let mem := auctionSettleAuctionSnapshotMem noun amount start finish bidder settled
  let σ2 := auctionSettleAuctionMarkSettledMap σ1 I
  let nounsWord := auctionSlotWord ⟨201⟩ σ2 I
  let target := UInt256.land nounsWord solcAddrMask
  let caller := UInt256.ofNat I.codeOwner.val
  let memSel :=
    (UInt256.toByteArray auctionSettleAuctionTransferFromSelectorShifted).write 0 mem 320 32
  let memCaller := (UInt256.toByteArray caller).write 0 memSel 324 32
  let memBidder :=
    (UInt256.toByteArray (UInt256.land solcAddrMask bidder)).write 0 memCaller 356 32
  let memCall := auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller
  obtain ⟨_, _, rd4536⟩ := auctionInternalSettleAuction_markSettledToTransferFromPath
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (ret := ret) hbidderNZ hreach
  obtain ⟨_, _, rd4536'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4536⟩
      [⟨128⟩, ret, ⟨413⟩, auctionSelWord I] mem (UInt256.ofNat 10)
      ByteArray.empty (cA, σ2) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled, mem, σ2] using rd4536⟩
  have rd4539 := evm_run rd4536' with [jumpdest, push1 ⟨201⟩]
  obtain ⟨_, _, rd4540₀⟩ := rd4539.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd4540⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4540⟩
      (nounsWord :: [⟨128⟩, ret, ⟨413⟩, auctionSelWord I])
      mem (UInt256.ofNat 10) ByteArray.empty (cA, σ2) k C := by
    exact ⟨_, _, by simpa [nounsWord, auctionSlotWord] using rd4540₀⟩
  have rd4613₀ := evm_run rd4540 with [
    push1 ⟨128⟩, dup3, add,
    raw mload 0 bidder (UInt256.ofNat 10) (by native_decide)
      mem_cost (by simpa [mem] using
        auctionSettleAuctionSnapshotMem_mload256 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    dup3,
    raw mload 0 noun (UInt256.ofNat 10) (by native_decide)
      mem_cost (by simpa [mem] using
        auctionSettleAuctionSnapshotMem_mload128 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 10) (by native_decide)
      mem_cost (by simpa [mem] using
        auctionSettleAuctionSnapshotMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push4 ⟨599290589⟩, push1 ⟨224⟩, shl, dup2,
    raw mstore 3 memSel (UInt256.ofNat 11) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    uniswapAddress, push1 ⟨4⟩, dup3, add,
    raw mstore 3 memCaller (UInt256.ofNat 12) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap3, dup4, and,
    push1 ⟨36⟩, dup3, add,
    raw mstore 3 memBidder (UInt256.ofNat 13) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨68⟩, dup2, add, swap2, swap1, swap2,
    raw mstore 3 memCall (UInt256.ofNat 14) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    swap2, and, swap1, push4 ⟨599290589⟩, swap1, push1 ⟨100⟩, add, push0,
    push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 14) (by native_decide)
      mem_cost (by simpa [memCall] using
        (auctionSettleAuctionTransferFromMem_mload64
          noun amount start finish bidder settled caller))
      (by decide) (by evm_ov),
    dup1, dup4, sub, dup2, push0, dup8, dup1]
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have hfree : (⟨100⟩ : UInt256) + ⟨320⟩ = ⟨420⟩ := by
    native_decide
  have hlen : UInt256.sub ((⟨100⟩ : UInt256) + ⟨320⟩) ⟨320⟩ = ⟨100⟩ := by
    native_decide
  have rd4613 := rd4613₀
  rw [hmaskConst, hlen, hfree] at rd4613
  exact auctionExtcodesizeGuardMissingPush0 (pc := ⟨4613⟩) (okPc := ⟨4624⟩)
    (by simpa [target, nounsWord, caller, mem, memSel, memCaller, memBidder, memCall,
      auctionSettleAuctionTransferFromMem, auctionSettleAuctionTransferFromSelectorShifted,
      solcAddrMask] using rd4613)
    (by simpa [target, nounsWord, σ1, σ2] using hnounsNoCode)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

end Auction
