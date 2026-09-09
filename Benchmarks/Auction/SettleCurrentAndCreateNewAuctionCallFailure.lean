import Benchmarks.Auction.SettleAuctionEvent
import Benchmarks.Auction.CreateAuctionCall
import Benchmarks.Auction.SettleCurrentAndCreateNewAuctionReverts
import Benchmarks.Auction.SettleAuctionWithMemorySource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem auctionSettleAndCreateTransitionReturns_afterSettleCreate
    (evm evmSettle evmCreate : EVM.State) {settleSolm createSolm : Frame} {free : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ =
        ⟨0⟩)
    (hsettle :
      ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ }
        (auctionSettleAuctionEnterState evm) settleAuctionWithMemoryFn.body
        (.returned settleSolm evmSettle (some [.int (Int.ofNat free.toNat)])))
    (hcreate :
      ExecFuncBody auctionConfig
        { contract := auctionContract,
          locals := (∅ : Store).insert "_freePtr" (.int (Int.ofNat free.toNat)) }
        evmSettle createAuctionWithMemoryFn.body (.returned createSolm evmCreate none)) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAndCreateTransition.body
      (.returned
        (resumeAfterInternalCall
          (resumeAfterInternalCall { contract := auctionContract, locals := ∅ } "_s" (some [.int (Int.ofNat free.toNat)]))
          "_c" none)
        (auctionSettleAuctionExitState evmCreate) none) := by
  let afterSettle := resumeAfterInternalCall { contract := auctionContract, locals := ∅ } "_s" (some [.int (Int.ofNat free.toNat)])
  let afterCreate := resumeAfterInternalCall afterSettle "_c" none
  dsimp [settleAndCreateTransition, nonpayable]
  refine ExecFuncBody.execBlockOK ?_
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
  refine ExecBlock.consNormal
    (internalCallFunctionReturn
      (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
      (evm := auctionSettleAuctionEnterState evm) (calleeEvm := evmSettle)
      (name := "_settleAuctionWithMemory") (args := []) (retVar := "_s") (argVals := [])
      (callee := settleAuctionWithMemoryFn) (locals := ∅) (calleeSolm := settleSolm)
      (value := (some [.int (Int.ofNat free.toNat)])) (by rfl) (by rfl) (by rfl) hsettle) ?_
  refine ExecBlock.consNormal
    (internalCallFunctionReturn
      (cfg := auctionConfig) (caller := afterSettle)
      (evm := evmSettle) (calleeEvm := evmCreate)
      (name := "_createAuctionWithMemory") (args := [.var "_s"]) (retVar := "_c") (argVals := [.int (Int.ofNat free.toNat)])
      (callee := createAuctionWithMemoryFn)
      (locals := (∅ : Store).insert "_freePtr" (.int (Int.ofNat free.toNat))) (calleeSolm := createSolm)
      (value := none)
      (evalExprs?_singleton (by
        simp [afterSettle, resumeAfterInternalCall, evalExpr?, EvalResult.ofOption,
          collapseReturns])) (by rfl) (by rfl)
      (by simpa [afterSettle] using hcreate)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_settleAuction_notEntered evmCreate afterCreate.locals)
      (auctionSettleAuctionAssignStatusNotEntered evmCreate afterCreate.locals
        (by simp [afterCreate, afterSettle, resumeAfterInternalCall]))) ExecBlock.nil

theorem auctionSettleAndCreateTransitionReverts_afterSettleCreate
    (evm evmSettle : EVM.State) {settleSolm : Frame} {free : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ =
        ⟨0⟩)
    (hsettle :
      ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ }
        (auctionSettleAuctionEnterState evm) settleAuctionWithMemoryFn.body
        (.returned settleSolm evmSettle (some [.int (Int.ofNat free.toNat)])))
    (hcreate :
      ExecFuncBody auctionConfig
        { contract := auctionContract,
          locals := (∅ : Store).insert "_freePtr" (.int (Int.ofNat free.toNat)) }
        evmSettle createAuctionWithMemoryFn.body .reverted) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAndCreateTransition.body .reverted := by
  let afterSettle := resumeAfterInternalCall { contract := auctionContract, locals := ∅ } "_s" (some [.int (Int.ofNat free.toNat)])
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
  refine ExecBlock.consNormal
    (internalCallFunctionReturn
      (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
      (evm := auctionSettleAuctionEnterState evm) (calleeEvm := evmSettle)
      (name := "_settleAuctionWithMemory") (args := []) (retVar := "_s") (argVals := [])
      (callee := settleAuctionWithMemoryFn) (locals := ∅) (calleeSolm := settleSolm)
      (value := (some [.int (Int.ofNat free.toNat)])) (by rfl) (by rfl) (by rfl) hsettle) ?_
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := afterSettle)
    (evm := evmSettle) (name := "_createAuctionWithMemory") (args := [.var "_s"])
    (retVar := "_c") (argVals := [.int (Int.ofNat free.toNat)]) (callee := createAuctionWithMemoryFn)
      (locals := (∅ : Store).insert "_freePtr" (.int (Int.ofNat free.toNat)))
    (evalExprs?_singleton (by
      simp [afterSettle, resumeAfterInternalCall, evalExpr?, EvalResult.ofOption,
        collapseReturns])) (by rfl) (by rfl) (by simpa [afterSettle] using hcreate))

theorem auctionSettleAndCreateAfterSettleReturn_toCreateAuction
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2690⟩
      [⟨413⟩, auctionSelWord I] mem aw o acc k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3000⟩
      [⟨2471⟩, ⟨413⟩, auctionSelWord I] mem aw o acc k' C' := by
  exact ⟨_, _, evm_run rd with [
    jumpdest, push2 ⟨2471⟩, push2 ⟨3000⟩, jump (by jump_dest)]⟩

theorem auctionSettleAndCreateStatusResetReturn {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2471⟩
      [⟨413⟩, auctionSelWord I] mem aw o (cA', σ') k C) :
    RDret auctionBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA', auctionSettleAuctionExitMap σ' I) ByteArray.empty := by
  have rd2477₀ := evm_run rd with [jumpdest, push1 ⟨1⟩, push1 ⟨101⟩]
  obtain ⟨_, _, rd2477⟩ : ∃ k' C', RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2477⟩
      [⟨413⟩, auctionSelWord I] mem aw o
      (cA', auctionSettleAuctionExitMap σ' I) k' C' := by
    obtain ⟨_, _, rd2477raw⟩ := rd2477₀.sstore hperm (by native_decide) (by evm_ov)
    exact ⟨_, _, by simpa [auctionSettleAuctionExitMap] using rd2477raw⟩
  have rd413 := evm_run rd2477 with [jump (by jump_dest), jumpdest]
  exact rd413.stop (by native_decide) (by evm_ov)


theorem auctionSettleAuctionBurnSuccessToNoPayoutEventAt {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {target noun amount start finish bidder settled ret : UInt256} {o : ByteArray} {k C : ℕ}
    (hamount : amount = ⟨0⟩)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4513⟩
      (⟨1⟩ :: ⟨356⟩ :: ⟨1117154408⟩ :: target ::
        ⟨128⟩ :: ret :: ⟨413⟩ :: auctionSelWord I :: [])
      (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) o acc k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4688⟩
      [⟨128⟩, ret, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) o acc k' C' := by
  obtain ⟨_, _, rd4529⟩ := auctionSettleAuctionBurnCallSuccess rd (by simp)
  have rd4647 := evm_run rd4529 with [pop, pop, pop, push2 ⟨4647⟩, jump (by jump_dest)]
  have rd4653 := evm_run rd4647 with [
    jumpdest, push1 ⟨32⟩, dup2, add,
    raw mload 0 amount (UInt256.ofNat 12) (by native_decide)
      mem_cost (auctionSettleAuctionBurnCallMem_mload160 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    iszero]
  have hcond : UInt256.isZero amount ≠ ⟨0⟩ := by
    rw [hamount]
    decide
  exact ⟨_, _, evm_run rd4653 with [push2 ⟨4688⟩, jumpiT hcond (by jump_dest)]⟩

theorem auctionSettleAuctionTransferFromSuccessToNoPayoutEventAt {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {target noun amount start finish bidder settled caller ret : UInt256} {o : ByteArray}
    {k C : ℕ}
    (hamount : amount = ⟨0⟩)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4628⟩
      (⟨1⟩ :: ⟨420⟩ :: ⟨599290589⟩ :: target ::
        ⟨128⟩ :: ret :: ⟨413⟩ :: auctionSelWord I :: [])
      (auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller)
      (UInt256.ofNat 14) o acc k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4688⟩
      [⟨128⟩, ret, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller)
      (UInt256.ofNat 14) o acc k' C' := by
  obtain ⟨_, _, rd4644⟩ := auctionSettleAuctionTransferFromCallSuccess rd (by simp)
  have rd4647 := evm_run rd4644 with [pop, pop, pop]
  have rd4653 := evm_run rd4647 with [
    jumpdest, push1 ⟨32⟩, dup2, add,
    raw mload 0 amount (UInt256.ofNat 14) (by native_decide)
      mem_cost
        (auctionSettleAuctionTransferFromMem_mload160
          noun amount start finish bidder settled caller)
      (by decide) (by evm_ov),
    iszero]
  have hcond : UInt256.isZero amount ≠ ⟨0⟩ := by
    rw [hamount]
    decide
  exact ⟨_, _, evm_run rd4653 with [push2 ⟨4688⟩, jumpiT hcond (by jump_dest)]⟩

theorem auctionSettleAuctionEventToRet {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {ptr ret aw : UInt256} {mem o : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4688⟩
      [ptr, ret, ⟨413⟩, auctionSelWord I] mem aw o (cA', σ') k C) :
    ∃ mem' aw' k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ret
      [⟨413⟩, auctionSelWord I] mem' aw' o (cA', σ') k' C' := by
  obtain ⟨k', C', hret⟩ := auctionSettleAuctionEventToRetExact (by simp) hperm hret rd
  exact ⟨_, _, k', C', hret⟩

theorem auctionSettleAndCreateBurnNoPayoutToCreateAuction {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {target noun amount start finish bidder settled : UInt256} {o : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hamount : amount = ⟨0⟩)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4513⟩
      (⟨1⟩ :: ⟨356⟩ :: ⟨1117154408⟩ :: target ::
        ⟨128⟩ :: ⟨2690⟩ :: ⟨413⟩ :: auctionSelWord I :: [])
      (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) o acc k C) :
    ∃ mem' aw' k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3000⟩
      [⟨2471⟩, ⟨413⟩, auctionSelWord I] mem' aw' o acc k' C' := by
  obtain ⟨_, _, rdEvent⟩ :=
    auctionSettleAuctionBurnSuccessToNoPayoutEventAt (ret := ⟨2690⟩) hamount rd
  obtain ⟨memRet, awRet, _, _, rdRet⟩ :=
    auctionSettleAuctionEventToRet hperm (by jump_dest) rdEvent
  obtain ⟨_, _, rd3000⟩ :=
    auctionSettleAndCreateAfterSettleReturn_toCreateAuction
      (mem := memRet) (aw := awRet) (rd := rdRet)
  exact ⟨memRet, awRet, _, _, rd3000⟩

theorem auctionSettleAndCreateTransferFromNoPayoutToCreateAuction {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {target noun amount start finish bidder settled caller : UInt256} {o : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hamount : amount = ⟨0⟩)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4628⟩
      (⟨1⟩ :: ⟨420⟩ :: ⟨599290589⟩ :: target ::
        ⟨128⟩ :: ⟨2690⟩ :: ⟨413⟩ :: auctionSelWord I :: [])
      (auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller)
      (UInt256.ofNat 14) o acc k C) :
    ∃ mem' aw' k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3000⟩
      [⟨2471⟩, ⟨413⟩, auctionSelWord I] mem' aw' o acc k' C' := by
  obtain ⟨_, _, rdEvent⟩ :=
    auctionSettleAuctionTransferFromSuccessToNoPayoutEventAt (ret := ⟨2690⟩) hamount rd
  obtain ⟨memRet, awRet, _, _, rdRet⟩ :=
    auctionSettleAuctionEventToRet hperm (by jump_dest) rdEvent
  obtain ⟨_, _, rd3000⟩ :=
    auctionSettleAndCreateAfterSettleReturn_toCreateAuction
      (mem := memRet) (aw := awRet) (rd := rdRet)
  exact ⟨memRet, awRet, _, _, rd3000⟩

theorem auctionSettleAndCreateTransitionReverts_settleBurnCallFailure
    (evm evmBurn : EVM.State) {out : ByteArray}
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
    (htime :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat =
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig
      (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "burn" 0
      [.int (Int.ofNat
        (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
          (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨207⟩).toNat)]
      (false, evmBurn, out) true) :
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
    (evm := auctionSettleAuctionEnterState evm) (name := "_settleAuctionWithMemory") (args := [])
    (retVar := "_s") (argVals := []) (callee := settleAuctionWithMemoryFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionSettleAuctionBodyReverts_burnCallFailure
      (payout := auctionSettleAuctionMemoryPayout) (tail := [.return [.intLit 320]]) (auctionSettleAuctionEnterState evm)
      evmBurn
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
        simpa [henv, hload] using hstart)
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
      hnounsCode hcall))

theorem auctionSettleAndCreateTransitionReverts_settleBurnDepthLimit
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
    (htime :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat =
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hdepth : evm.executionEnv.depth = 1024) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAndCreateTransition.body .reverted := by
  let evmEnter := auctionSettleAuctionEnterState evm
  let evmMark := auctionSettleAuctionMarkSettledState evmEnter
  let nounSolm := Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨207⟩
  let amountSolm := Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨208⟩
  let startSolm := Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨209⟩
  let finishSolm := Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨210⟩
  let packedSolm := Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨211⟩
  let bidderSolmWord := auctionPackedBidderWord packedSolm
  let settledSolmWord := auctionPackedSettledEVMReturnWord packedSolm
  let burnTargetSolm : EVM.Address := EVM.address (AccountAddress.ofNat
    ((UInt256.land
      (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨201⟩)
      solcAddrMask).toNat))
  let evmBurn :=
    { evmMark with
      substate := (evmMark.addAccessedAccount burnTargetSolm).substate }
  have hdepthMark : evmMark.executionEnv.depth = 1024 := by
    simpa [evmMark, evmEnter, auctionSettleAuctionMarkSettledState,
      auctionSettleAuctionEnterState, storageStore_executionEnv] using hdepth
  have hcallSolm :
      typedCallViaEVM auctionConfig evmMark burnTargetSolm "burn" 0
        [.int (Int.ofNat nounSolm.toNat)]
        (false, evmBurn, ByteArray.empty) true := by
    exact callNotMade_depthLimit
      (cfg := auctionConfig) (evm := evmMark) (tgt := burnTargetSolm)
      (name := "burn")
      (args := [.int (Int.ofNat nounSolm.toNat)])
      (calldata := (auctionSettleAuctionBurnCallMem nounSolm amountSolm
        startSolm finishSolm bidderSolmWord settledSolmWord)
        |>.readWithPadding 320 36)
      (callPerm := true)
      (auctionSettleAuctionBurnEncode_eq nounSolm amountSolm startSolm finishSolm
        bidderSolmWord settledSolmWord)
      hdepthMark
  exact auctionSettleAndCreateTransitionReverts_settleBurnCallFailure evm evmBurn
    hwv hstatus hpaused hstart hsettled htime hbidder hnounsCode
    (by simpa [evmBurn, evmMark, evmEnter, burnTargetSolm, nounSolm, amountSolm,
      startSolm, finishSolm, packedSolm, bidderSolmWord, settledSolmWord] using hcallSolm)

theorem auctionSettleAndCreateTransitionReverts_settleTransferFromCallFailure
    (evm evmTransfer : EVM.State) {out : ByteArray}
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
    (htime :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig
      (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "transferFrom" 0
      [.address (auctionSettleAuctionEnterState evm).executionEnv.codeOwner,
        .address (AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat),
        .int (Int.ofNat
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨207⟩).toNat)]
      (false, evmTransfer, out) true) :
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
    (evm := auctionSettleAuctionEnterState evm) (name := "_settleAuctionWithMemory") (args := [])
    (retVar := "_s") (argVals := []) (callee := settleAuctionWithMemoryFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionSettleAuctionBodyReverts_transferFromCallFailure
      (payout := auctionSettleAuctionMemoryPayout) (tail := [.return [.intLit 320]])
      (auctionSettleAuctionEnterState evm) evmTransfer
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
        simpa [henv, hload] using hstart)
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
      hnounsCode hcall))

theorem auctionSettleAndCreateTransitionReverts_settleTransferFromDepthLimit
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
    (htime :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hdepth : evm.executionEnv.depth = 1024) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAndCreateTransition.body .reverted := by
  let evmEnter := auctionSettleAuctionEnterState evm
  let evmMark := auctionSettleAuctionMarkSettledState evmEnter
  let nounSolm := Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨207⟩
  let amountSolm := Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨208⟩
  let startSolm := Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨209⟩
  let finishSolm := Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨210⟩
  let packedSolm := Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨211⟩
  let bidderSolmWord := auctionPackedBidderWord packedSolm
  let settledSolmWord := auctionPackedSettledEVMReturnWord packedSolm
  let callerSolm := UInt256.ofNat evmEnter.executionEnv.codeOwner.val
  let tfTargetSolm : EVM.Address := EVM.address (AccountAddress.ofNat
    ((UInt256.land
      (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨201⟩)
      solcAddrMask).toNat))
  let evmTf :=
    { evmMark with
      substate := (evmMark.addAccessedAccount tfTargetSolm).substate }
  have hdepthMark : evmMark.executionEnv.depth = 1024 := by
    simpa [evmMark, evmEnter, auctionSettleAuctionMarkSettledState,
      auctionSettleAuctionEnterState, storageStore_executionEnv] using hdepth
  have hbidderClean :
      UInt256.land solcAddrMask bidderSolmWord = bidderSolmWord := by
    dsimp [bidderSolmWord, auctionPackedBidderWord]
    rw [u256_land_comm solcAddrMask (UInt256.land packedSolm solcAddrMask)]
    exact solcAddrMask_clean (solcAddrMask_result_canonical packedSolm)
  have hbidderAddr :
      AccountAddress.ofNat bidderSolmWord.toNat =
        AccountAddress.ofUInt256 (UInt256.land solcAddrMask bidderSolmWord) := by
    rw [accountAddress_ofUInt256_eq_ofNat_toNat]
    rw [hbidderClean]
  have hencode :
      auctionConfig.externalABI.encode? "transferFrom"
          [.address evmEnter.executionEnv.codeOwner,
            .address (AccountAddress.ofNat bidderSolmWord.toNat),
            .int (Int.ofNat nounSolm.toNat)] =
        some ((auctionSettleAuctionTransferFromMem nounSolm amountSolm
          startSolm finishSolm bidderSolmWord settledSolmWord callerSolm)
          |>.readWithPadding 320 100) := by
    rw [hbidderAddr]
    simpa [callerSolm] using
      auctionSettleAuctionTransferFromEncode_eq nounSolm amountSolm
        startSolm finishSolm bidderSolmWord settledSolmWord
        evmEnter.executionEnv.codeOwner
  have hcallSolm :
      typedCallViaEVM auctionConfig evmMark tfTargetSolm "transferFrom" 0
        [.address evmEnter.executionEnv.codeOwner,
          .address (AccountAddress.ofNat bidderSolmWord.toNat),
          .int (Int.ofNat nounSolm.toNat)]
        (false, evmTf, ByteArray.empty) true := by
    exact callNotMade_depthLimit
      (cfg := auctionConfig) (evm := evmMark) (tgt := tfTargetSolm)
      (name := "transferFrom")
      (args := [.address evmEnter.executionEnv.codeOwner,
        .address (AccountAddress.ofNat bidderSolmWord.toNat),
        .int (Int.ofNat nounSolm.toNat)])
      (calldata := (auctionSettleAuctionTransferFromMem nounSolm amountSolm
        startSolm finishSolm bidderSolmWord settledSolmWord callerSolm)
        |>.readWithPadding 320 100)
      (callPerm := true) hencode hdepthMark
  exact auctionSettleAndCreateTransitionReverts_settleTransferFromCallFailure evm evmTf
    hwv hstatus hpaused hstart hsettled htime hbidder hnounsCode
    (by simpa [evmTf, evmMark, evmEnter, tfTargetSolm, nounSolm, amountSolm,
      startSolm, finishSolm, packedSolm, bidderSolmWord, settledSolmWord, callerSolm]
      using hcallSolm)

theorem auctionInternalSettleAuction_burnPostCall {cA gh bl σ σ₀ A I} {g : Sat256}
    {ret : UInt256}
    (hperm : I.perm = true)
    (hbidderZero :
      auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I) =
        ⟨0⟩)
    (hnounsCode :
      Reasoning.Theory.uniswapExtCodeSizeWord
        (auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I)
        (UInt256.land
          (auctionSlotWord ⟨201⟩
            (auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I) I)
          solcAddrMask) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
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
    let σ1 := auctionSettleAuctionEnterMap σ I
    let noun := auctionAuctionNounWord σ1 I
    let amount := auctionAuctionAmountWord σ1 I
    let start := auctionAuctionStartWord σ1 I
    let finish := auctionAuctionEndWord σ1 I
    let packed := auctionAuctionPackedWord σ1 I
    let bidder := auctionPackedBidderWord packed
    let settled := auctionPackedSettledEVMReturnWord packed
    let σ2 := auctionSettleAuctionMarkSettledMap σ1 I
    let nounsWord := auctionSlotWord ⟨201⟩ σ2 I
    let target := UInt256.land nounsWord solcAddrMask
    let memCall := auctionSettleAuctionBurnCallMem noun amount start finish bidder settled
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o : ByteArray) (A' : Substate) (k C : ℕ),
      RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4513⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨356⟩ :: ⟨1117154408⟩ :: target ::
          ⟨128⟩ :: ret :: ⟨413⟩ :: auctionSelWord I :: [])
        memCall (UInt256.ofNat 12) o (cA', σ') k C
    ∧ typedCallViaEVM auctionConfig
        { initState cA gh bl σ σ₀ g A I with accountMap := σ2 }
        (EVM.address (AccountAddress.ofNat target.toNat)) "burn" 0
        [.int (Int.ofNat noun.toNat)]
        (z,
          { { initState cA gh bl σ σ₀ g A I with accountMap := σ2 } with
              accountMap := σ', substate := A', createdAccounts := cA' },
          o) true
    ∧ o.size < UInt256.size := by
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
  obtain ⟨_, _, rd4438₀⟩ := rd4437.sload (by native_decide) (by evm_ov)
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
  obtain ⟨gasWord, k4512, C4512, rd4512⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨4498⟩) (okPc := ⟨4509⟩)
      (by simpa [target, nounsWord, mem, memSel, memCall,
        auctionSettleAuctionBurnSelectorShifted, auctionSettleAuctionBurnSelectorMem,
        auctionSettleAuctionBurnCallMem, solcAddrMask] using rd4498)
      (by simpa [target, nounsWord, σ1, σ2] using hnounsCode)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  have hinSize :
      ((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + (⟨320⟩ : UInt256))).sub ⟨320⟩ =
        ⟨36⟩ := by
    native_decide
  have houtEnd : (⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + (⟨320⟩ : UInt256)) = ⟨356⟩ := by
    native_decide
  obtain ⟨cA', σ', z, o, A_in, callGas, k4513, C4513, hΘpack, rd4513raw, hosz⟩ :=
    RD.call
      (by
        simpa [target, nounsWord, memCall, auctionSettleAuctionBurnCallMem,
          solcAddrMask, hinSize, houtEnd] using rd4512)
      (by native_decide) hdepth (by simp)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, o, A', k4513, C4513, ?_, ?_, hosz⟩
  · have hmin :
        (min (⟨0⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 0 := by
      change (if (⟨0⟩ : UInt256) ≤ UInt256.ofNat o.size then (⟨0⟩ : UInt256)
        else UInt256.ofNat o.size).toNat = 0
      by_cases h : (⟨0⟩ : UInt256) ≤ UInt256.ofNat o.size
      · simp [h]
      · exact False.elim (h (Fin.zero_le _))
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 12).toNat
          (⟨320⟩ : UInt256).toNat (⟨36⟩ : UInt256).toNat)
          (⟨320⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 12 := by
      native_decide
    simpa [target, nounsWord, memCall, hmin, byteArray_write_len_zero, haw] using rd4513raw
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := target) (mem := memCall)
      (inOff := (⟨320⟩ : UInt256)) (inSize := (⟨36⟩ : UInt256))
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      (auctionSettleAuctionTargetAddress_eq target)
      (auctionSettleAuctionBurnEncode_eq noun amount start finish bidder settled) ?_
    simpa [initState, target, nounsWord, σ1, σ2, memCall,
      auctionSettleAuctionBurnCallMem, solcAddrMask, hperm, hinSize] using hΘ

theorem auctionInternalSettleAuction_revert_burnDepthLimit {cA gh bl σ σ₀ A I}
    {g : Sat256} {ret : UInt256}
    (hbidderZero :
      auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I) =
        ⟨0⟩)
    (hnounsCode :
      Reasoning.Theory.uniswapExtCodeSizeWord
        (auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I)
        (UInt256.land
          (auctionSlotWord ⟨201⟩
            (auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I) I)
          solcAddrMask) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
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
  obtain ⟨_, _, rd4438₀⟩ := rd4437.sload (by native_decide) (by evm_ov)
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
  obtain ⟨gasWord, k4512, C4512, rd4512⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨4498⟩) (okPc := ⟨4509⟩)
      (by simpa [target, nounsWord, mem, memSel, memCall,
        auctionSettleAuctionBurnSelectorShifted, auctionSettleAuctionBurnSelectorMem,
        auctionSettleAuctionBurnCallMem, solcAddrMask] using rd4498)
      (by simpa [target, nounsWord, σ1, σ2] using hnounsCode)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  have hinSize :
      ((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + (⟨320⟩ : UInt256))).sub ⟨320⟩ =
        ⟨36⟩ := by
    native_decide
  have houtEnd : (⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + (⟨320⟩ : UInt256)) = ⟨356⟩ := by
    native_decide
  obtain ⟨_, _, rd4513⟩ := RD.callDepthLimit
    (by
      simpa [target, nounsWord, memCall, auctionSettleAuctionBurnCallMem,
        solcAddrMask, hinSize, houtEnd] using rd4512)
    (by native_decide) hdepth (by simp)
  exact auctionSettleAuctionBurnCallFailure rd4513 (by native_decide) (by simp)

theorem auctionInternalSettleAuction_transferFromPostCall {cA gh bl σ σ₀ A I}
    {g : Sat256} {ret : UInt256}
    (hperm : I.perm = true)
    (hbidderNZ :
      auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I) ≠
        ⟨0⟩)
    (hnounsCode :
      Reasoning.Theory.uniswapExtCodeSizeWord
        (auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I)
        (UInt256.land
          (auctionSlotWord ⟨201⟩
            (auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I) I)
          solcAddrMask) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
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
    let σ1 := auctionSettleAuctionEnterMap σ I
    let noun := auctionAuctionNounWord σ1 I
    let amount := auctionAuctionAmountWord σ1 I
    let start := auctionAuctionStartWord σ1 I
    let finish := auctionAuctionEndWord σ1 I
    let packed := auctionAuctionPackedWord σ1 I
    let bidder := auctionPackedBidderWord packed
    let settled := auctionPackedSettledEVMReturnWord packed
    let σ2 := auctionSettleAuctionMarkSettledMap σ1 I
    let nounsWord := auctionSlotWord ⟨201⟩ σ2 I
    let target := UInt256.land nounsWord solcAddrMask
    let caller := UInt256.ofNat I.codeOwner.val
    let memCall := auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o : ByteArray) (A' : Substate) (k C : ℕ),
      RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4628⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨420⟩ :: ⟨599290589⟩ :: target ::
          ⟨128⟩ :: ret :: ⟨413⟩ :: auctionSelWord I :: [])
        memCall (UInt256.ofNat 14) o (cA', σ') k C
    ∧ typedCallViaEVM auctionConfig
        { initState cA gh bl σ σ₀ g A I with accountMap := σ2 }
        (EVM.address (AccountAddress.ofNat target.toNat)) "transferFrom" 0
        [.address I.codeOwner, .address (AccountAddress.ofNat bidder.toNat),
          .int (Int.ofNat noun.toNat)]
        (z,
          { { initState cA gh bl σ σ₀ g A I with accountMap := σ2 } with
              accountMap := σ', substate := A', createdAccounts := cA' },
          o) true
    ∧ o.size < UInt256.size := by
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
  obtain ⟨_, _, rd4540₀⟩ := rd4539.sload (by native_decide) (by evm_ov)
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
  have htargetMask : UInt256.land solcAddrMask nounsWord = target := by
    dsimp [target]
    rw [u256_land_comm solcAddrMask nounsWord]
  have hcallerWord : UInt256.ofNat ↑I.codeOwner = caller := by
    rfl
  have hfree : (⟨100⟩ : UInt256) + ⟨320⟩ = ⟨420⟩ := by
    native_decide
  have hlen : UInt256.sub ((⟨100⟩ : UInt256) + ⟨320⟩) ⟨320⟩ = ⟨100⟩ := by
    native_decide
  have rd4613 := rd4613₀
  rw [hmaskConst, hlen, hfree] at rd4613
  obtain ⟨gasWord, k4627, C4627, rd4627⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨4613⟩) (okPc := ⟨4624⟩)
      (by simpa [target, nounsWord, caller, mem, memSel, memCaller, memBidder, memCall,
        auctionSettleAuctionTransferFromMem, auctionSettleAuctionTransferFromSelectorShifted,
        solcAddrMask] using rd4613)
      (by simpa [target, nounsWord, σ1, σ2] using hnounsCode)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  obtain ⟨cA', σ', z, o, A_in, callGas, k4628, C4628, hΘpack, rd4628raw, hosz⟩ :=
    RD.call
      (by
        simpa [target, nounsWord, caller, memCall, auctionSettleAuctionTransferFromMem,
          solcAddrMask] using rd4627)
      (by native_decide) hdepth (by simp)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, o, A', k4628, C4628, ?_, ?_, hosz⟩
  · have hmin :
        (min (⟨0⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 0 := by
      change (if (⟨0⟩ : UInt256) ≤ UInt256.ofNat o.size then (⟨0⟩ : UInt256)
        else UInt256.ofNat o.size).toNat = 0
      by_cases h : (⟨0⟩ : UInt256) ≤ UInt256.ofNat o.size
      · simp [h]
      · exact False.elim (h (Fin.zero_le _))
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 14).toNat
          (⟨320⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat)
          (⟨320⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 14 := by
      native_decide
    simpa [target, nounsWord, memCall, hmin, byteArray_write_len_zero, haw] using rd4628raw
  · have hbidderClean : UInt256.land solcAddrMask bidder = bidder := by
      dsimp [bidder, auctionPackedBidderWord]
      rw [u256_land_comm solcAddrMask (UInt256.land packed solcAddrMask)]
      exact solcAddrMask_clean (solcAddrMask_result_canonical packed)
    have hbidderAddr :
        AccountAddress.ofNat bidder.toNat =
          AccountAddress.ofUInt256 (UInt256.land solcAddrMask bidder) := by
      rw [accountAddress_ofUInt256_eq_ofNat_toNat]
      rw [hbidderClean]
    have hencode :
        auctionConfig.externalABI.encode? "transferFrom"
            [.address I.codeOwner, .address (AccountAddress.ofNat bidder.toNat),
              .int (Int.ofNat noun.toNat)] =
          some (memCall.readWithPadding 320 100) := by
      rw [hbidderAddr]
      exact auctionSettleAuctionTransferFromEncode_eq
        noun amount start finish bidder settled I.codeOwner
    refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := target) (mem := memCall)
      (inOff := (⟨320⟩ : UInt256)) (inSize := (⟨100⟩ : UInt256))
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      (auctionSettleAuctionTargetAddress_eq target)
      hencode ?_
    simpa [initState, target, nounsWord, σ1, σ2, caller, memCall,
      auctionSettleAuctionTransferFromMem, solcAddrMask, hperm] using hΘ

theorem auctionInternalSettleAuction_revert_transferFromDepthLimit
    {cA gh bl σ σ₀ A I} {g : Sat256} {ret : UInt256}
    (hbidderNZ :
      auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I) ≠
        ⟨0⟩)
    (hnounsCode :
      Reasoning.Theory.uniswapExtCodeSizeWord
        (auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I)
        (UInt256.land
          (auctionSlotWord ⟨201⟩
            (auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I) I)
          solcAddrMask) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
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
  obtain ⟨_, _, rd4540₀⟩ := rd4539.sload (by native_decide) (by evm_ov)
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
  obtain ⟨gasWord, k4627, C4627, rd4627⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨4613⟩) (okPc := ⟨4624⟩)
      (by simpa [target, nounsWord, caller, mem, memSel, memCaller, memBidder, memCall,
        auctionSettleAuctionTransferFromMem, auctionSettleAuctionTransferFromSelectorShifted,
        solcAddrMask] using rd4613)
      (by simpa [target, nounsWord, σ1, σ2] using hnounsCode)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  obtain ⟨_, _, rd4628⟩ := RD.callDepthLimit
    (by
      simpa [target, nounsWord, caller, memCall, auctionSettleAuctionTransferFromMem,
        solcAddrMask] using rd4627)
    (by native_decide) hdepth (by simp)
  exact auctionSettleAuctionTransferFromCallFailure rd4628 (by native_decide) (by simp)

end Auction
