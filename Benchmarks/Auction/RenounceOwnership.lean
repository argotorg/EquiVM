import Benchmarks.Auction.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

def auctionRenounceOwnershipPostWord (old : UInt256) : UInt256 :=
  auctionSetOwnerWord old ⟨0⟩

def auctionRenounceOwnershipPostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  auctionSetOwnerPostMap σ I ⟨0⟩

def auctionRenounceOwnershipPostState (evm : EVM.State) : EVM.State :=
  auctionSetOwnerPostState evm ⟨0⟩

theorem auctionDispatch_renounceOwnership {I : ExecutionEnv}
    (hsel : selIs I (auctionSelBytes 8)) :
    dispatchMsg auctionContract I.calldata = some renounceOwnershipTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [initializeTransition, createBidTransition, settleAndCreateTransition,
      settleAuctionTransition, pauseTransition, unpauseTransition, setTimeBufferTransition,
      setReservePriceTransition, setMinBidIncTransition, transferOwnershipTransition])
    (post := [ownerGetter, pausedGetter, nounsGetter, wethGetter, timeBufferGetter,
      reservePriceGetter, minBidIncGetter, durationGetter, auctionGetter])
    (ti := renounceOwnershipTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = auctionSelBytes 8 := (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, initializeSelectorBytes, createBidSelectorBytes,
        settleAndCreateSelectorBytes, settleAuctionSelectorBytes, pauseSelectorBytes,
        unpauseSelectorBytes, setTimeBufferSelectorBytes, setReservePriceSelectorBytes,
        setMinBidIncSelectorBytes, transferOwnershipSelectorBytes, hcd, auctionSelBytes]
      native_decide
  · rw [selectorOf, renounceOwnershipSelectorBytes]
    simpa [selIs, auctionSelBytes] using hsel

theorem auctionDecode_renounceOwnership {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (renounceOwnershipTransition.params.map Param.name)
        (transitionSignature renounceOwnershipTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode auctionConfig.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem evalExpr_renounceOwnership_owner (evm : EVM.State) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ }
        evm (.storage ownerRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := ∅ } evm ownerRef =
        .ok { base := "_owner", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, ownerRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_owner", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar (t := .address) (hbase := by simp)
    (her := her) (hty := hty) (hloc := by rfl)]
  exact congrArg EvalResult.ok (by
    simpa [auctionAddrLoc] using auctionStorageLocLoad_address_offset0 evm ⟨151⟩)

theorem evalExpr_renounceOwnership_sender (evm : EVM.State) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ }
      evm sender = .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_renounceOwnership_owner_eq_true (evm : EVM.State)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ }
      evm (.binary .eq sender (.storage ownerRef)) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_renounceOwnership_sender, evalExpr_renounceOwnership_owner,
    bind, EvalResult.bind, evalBinaryOp?]
  rw [auctionMaskedAddress_eq_source_of_word_eq (I := evm.executionEnv) howner]
  simp [BEq.beq]

theorem evalExpr_renounceOwnership_owner_eq_false (evm : EVM.State)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask ≠
        auctionSourceWord evm.executionEnv) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ }
      evm (.binary .eq sender (.storage ownerRef)) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_renounceOwnership_sender, evalExpr_renounceOwnership_owner,
    bind, EvalResult.bind, evalBinaryOp?]
  have haddr :
      evm.executionEnv.source ≠
        AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩)
            solcAddrMask).toNat := by
    intro haddr
    exact howner (auctionWord_eq_of_maskedAddress_eq_source haddr.symm)
  rw [show ((.address evm.executionEnv.source : Value) ==
          .address (AccountAddress.ofNat
            (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩)
              solcAddrMask).toNat)) = false by
    simp [BEq.beq, haddr]]

theorem evalExpr_renounceOwnership_zeroAddr (evm : EVM.State) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } evm zeroAddr =
      .ok (.address (AccountAddress.ofNat 0)) := by
  rw [zeroAddr, evalExpr?.eq_16, evalExpr?.eq_1]
  change (EvalResult.ok (Value.int 0)).bind
      (fun value => EvalResult.ofOption EvalError.typeError
        (castValue? value (.elem .address))) =
    EvalResult.ok (Value.address (AccountAddress.ofNat 0))
  rfl

theorem auctionRenounceOwnershipAssign (evm : EVM.State) :
    assignStorageRef? auctionConfig { contract := auctionContract, locals := ∅ } evm .storage
        ownerRef (.address (AccountAddress.ofNat 0)) =
      .ok ({ contract := auctionContract, locals := ∅ }, auctionRenounceOwnershipPostState evm) := by
  have her : evalStorageRef auctionConfig { contract := auctionContract, locals := ∅ } evm
      ownerRef = .ok { base := "_owner", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, ownerRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_owner", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
    decide
  have hstore :
      storageLocStore evm (auctionAddrLoc ⟨151⟩) (.address (AccountAddress.ofNat 0)) =
        some (auctionRenounceOwnershipPostState evm) := by
    have hcanon : (⟨0⟩ : UInt256).toNat < EVM.addressModulus := by decide
    change storageLocStore evm (addressOffset0Loc ⟨151⟩)
        (.address (AccountAddress.ofNat (⟨0⟩ : UInt256).toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨151⟩
        (setAddressOffset0Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) (⟨0⟩ : UInt256)))
    exact storageLocStore_address_offset0 evm ⟨151⟩ ⟨0⟩ hcanon
  exact assignStorageRef_storage_scalar_value (cfg := auctionConfig)
    (solm := { contract := auctionContract, locals := ∅ })
    (evm := evm) (slot := ownerRef) (er := { base := "_owner", steps := [] })
    (ty := .elem .address) (loc := auctionAddrLoc ⟨151⟩)
    (hbase := by simp) (her := her) (hty := hty) (hloc := by rfl) (by trivial) hstore

theorem auctionRenounceOwnershipBodyReturns (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ renounceOwnershipTransition.body
      (.returned { contract := auctionContract, locals := ∅ }
        (auctionRenounceOwnershipPostState evm) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_renounceOwnership_owner_eq_true evm howner)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_renounceOwnership_zeroAddr evm) (auctionRenounceOwnershipAssign evm))
    ExecBlock.nil

theorem auctionRenounceOwnershipBodyReverts_callvalue (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ renounceOwnershipTransition.body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalCallvalueEq_false hwv))

theorem auctionRenounceOwnershipBodyReverts_owner (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask ≠
        auctionSourceWord evm.executionEnv) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ renounceOwnershipTransition.body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_renounceOwnership_owner_eq_false evm howner))

theorem auctionReachRenounceOwnershipBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = auctionBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (auctionSelBytes 8)) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨550⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsel' : ((⟨#[0x71, 0x50, 0x18, 0xa6]⟩ : ByteArray) == I.calldata.extract 0 4) = true := by
    simpa [selIs, auctionSelBytes] using hsel
  have hword : auctionSelWord I = ⟨0x715018a6⟩ :=
    auctionSelWord_eq_of_beq I hsz 0x71 0x50 0x18 0xa6 ⟨0x715018a6⟩
      (by decide) hsel'
  obtain ⟨_, _, hsplit⟩ := auctionReachRootSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
  have hroot : UInt256.gt (armSelNat auctionBytecode auctionSplitPc) (auctionSelWord I) ≠
      ⟨0⟩ := by
    rw [hword]
    decide
  have h157 := RD.selectorSplitTakenAuto hsplit auctionSplitWellFormed hroot
    (by jump_dest) (by simp)
  have h158 := h157.jumpdest (by decide) (by simp)
  have hlower : UInt256.gt (armSelNat auctionBytecode auctionLowerSplitPc) (auctionSelWord I) =
      ⟨0⟩ := by
    rw [hword]
    decide
  have h169 := RD.selectorSplitNotTakenAuto h158 auctionLowerSplitWellFormed hlower (by simp)
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat auctionBytecode
        (nthArmPc auctionBytecode auctionLowerMidFirstArmPc j)) (auctionSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> decide
  have htake :
      UInt256.eq
        (armSelNat auctionBytecode (nthArmPc auctionBytecode auctionLowerMidFirstArmPc 3))
        (auctionSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide
  exact RD.dispatchTo (code := auctionBytecode) (ee := I) (g := g)
    (s0 := initState cA gh bl σ σ₀ g A I) (selWord := auctionSelWord I)
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (acc := (cA, σ)) ⟨550⟩ 3 h169
    (fun j hj => auctionLowerMidArmsWellFormed j (by omega)) heq0 htake
    (by jump_dest)
    (by native_decide)
    (by simp)

theorem auctionX_renounceOwnership_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨550⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd550⟩ := hreach
  exact evm_run rd550 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨561⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv),
    push0, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem auctionRenounceOwnershipX_toBody {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨550⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2029⟩
      [⟨413⟩, sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd550⟩ := hreach
  exact ⟨_, _, evm_run rd550 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨561⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push2 ⟨413⟩, push2 ⟨2029⟩, jump (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
theorem auctionX_renounceOwnership_success {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (auctionSlotWord ⟨151⟩ σ I) solcAddrMask = auctionSourceWord I)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨550⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret auctionBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, auctionRenounceOwnershipPostMap σ I) ByteArray.empty := by
  obtain ⟨_, _, rd2029⟩ := auctionRenounceOwnershipX_toBody (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := auctionSelWord I) hreach hwv
  have rd2032₀ := evm_run rd2029 with [jumpdest, push1 ⟨151⟩]
  obtain ⟨_, _, rd2033₀⟩ := rd2032₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2033⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2033⟩
      [auctionSlotWord ⟨151⟩ σ I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2033₀⟩
  have rd2044₁ := evm_run rd2033 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, caller, eq]
  have hmask :
      UInt256.land solcAddrMask (auctionSlotWord ⟨151⟩ σ I) = auctionSourceWord I := by
    rw [u256_land_comm, howner]
  have heq :
      UInt256.eq (UInt256.ofNat I.source.val)
        (UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (auctionSlotWord ⟨151⟩ σ I)) = ⟨1⟩ := by
    change UInt256.eq (auctionSourceWord I)
      (UInt256.land solcAddrMask (auctionSlotWord ⟨151⟩ σ I)) = ⟨1⟩
    rw [hmask, u256_eq_refl]
  have rd2044 := rd2044₁
  rw [heq] at rd2044
  have rd2071 := evm_run rd2044 with [
    push2 ⟨2071⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  have rd3574 := evm_run rd2071 with [
    push2 ⟨1163⟩, push0, push2 ⟨3574⟩, jump (by jump_dest)]
  have rd3578₀ := evm_run rd3574 with [jumpdest, push1 ⟨151⟩, dup1]
  obtain ⟨_, _, rd3579₀⟩ := rd3578₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd3579⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3579⟩
      [auctionSlotWord ⟨151⟩ σ I, ⟨151⟩, ⟨0⟩, ⟨1163⟩, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3579₀⟩
  have hpostComm :
      UInt256.lor (UInt256.land solcAddrMask (⟨0⟩ : UInt256))
          (UInt256.land (auctionSlotWord ⟨151⟩ σ I) (UInt256.lnot solcAddrMask)) =
        auctionRenounceOwnershipPostWord (auctionSlotWord ⟨151⟩ σ I) := by
    rw [u256_land_comm solcAddrMask (⟨0⟩ : UInt256)]
    unfold auctionRenounceOwnershipPostWord auctionSetOwnerWord setAddressOffset0Word
    rw [u256_lor_comm]
  have rd3605₀ := evm_run rd3579 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, dup2, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, dup4, and, dup2, lor,
    swap1, swap4]
  have hsolcMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  rw [hsolcMask] at rd3605₀
  rw [hpostComm] at rd3605₀
  obtain ⟨_, _, rd3606₀⟩ := rd3605₀.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd3606⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3606⟩
      [solcAddrMask, auctionSlotWord ⟨151⟩ σ I, UInt256.land (⟨0⟩ : UInt256) solcAddrMask,
        ⟨0⟩, ⟨1163⟩, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionRenounceOwnershipPostMap σ I) k C := by
    exact ⟨_, _, by simpa [auctionRenounceOwnershipPostMap] using rd3606₀⟩
  have rd3615 := evm_run rd3606 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    swap2, and, swap2, swap1, dup3, swap1]
  have rd3648 := rd3615.pushConst auctionOwnershipTransferredTopic
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd3652 := evm_run rd3648 with [swap1, push0, swap1]
  have rd3653 := RD.log3 0 (UInt256.ofNat 3) rd3652 (by decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by decide) (by evm_ov)
  have rd1163 := evm_run rd3653 with [
    pop, pop, jump (by jump_dest), jumpdest, jump (by jump_dest), jumpdest]
  exact rd1163.stop (by decide) (by evm_ov)

theorem auctionX_renounceOwnership_revert_owner {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (auctionSlotWord ⟨151⟩ σ I) solcAddrMask ≠ auctionSourceWord I)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨550⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2029⟩ := auctionRenounceOwnershipX_toBody (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := auctionSelWord I) hreach hwv
  have rd2032₀ := evm_run rd2029 with [jumpdest, push1 ⟨151⟩]
  obtain ⟨_, _, rd2033₀⟩ := rd2032₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2033⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2033⟩
      [auctionSlotWord ⟨151⟩ σ I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2033₀⟩
  have rd2044₁ := evm_run rd2033 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, caller, eq]
  have hmask :
      UInt256.land solcAddrMask (auctionSlotWord ⟨151⟩ σ I) ≠ auctionSourceWord I := by
    intro hmask
    exact howner (by
      rw [u256_land_comm] at hmask
      exact hmask)
  have hneq :
      UInt256.ofNat I.source.val ≠
        UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (auctionSlotWord ⟨151⟩ σ I) := by
    change auctionSourceWord I ≠ UInt256.land solcAddrMask (auctionSlotWord ⟨151⟩ σ I)
    exact fun h => hmask h.symm
  have heq :
      UInt256.eq (UInt256.ofNat I.source.val)
        (UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (auctionSlotWord ⟨151⟩ σ I)) = ⟨0⟩ := by
    exact u256_eq_of_ne hneq
  have rd2044 := rd2044₁
  rw [heq] at rd2044
  have rd2051 := evm_run rd2044 with [
    push2 ⟨2071⟩, jumpiNT (by decide),
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov)]
  have rd2055 := rd2051.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd5522 := evm_run rd2055 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 6 (solcReturnMem ⟨0x08c379a000000000000000000000000000000000000000000000000000000000⟩)
      (UInt256.ofNat 5) (by decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨4⟩, add, push2 ⟨994⟩, swap1, push2 ⟨5522⟩, jump (by jump_dest)]
  have rd5532 := evm_run rd5522 with [
    jumpdest, push1 ⟨32⟩, dup1, dup3,
    raw mstore 3 (solcErrorStringMem1 solcFreePtrMem) (UInt256.ofNat 6)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    dup2, dup2, add,
    raw mstore 3 (solcErrorStringMem2 ⟨32⟩ solcFreePtrMem) (UInt256.ofNat 7)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd5565 := rd5532.pushConst auctionOnlyOwnerStringWord
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd5574₀ := evm_run rd5565 with [
    push1 ⟨64⟩, dup3, add,
    raw mstore 3 (solcErrorStringMem3 ⟨32⟩ auctionOnlyOwnerStringWord solcFreePtrMem)
      (UInt256.ofNat 8) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨96⟩, add, swap1]
  have rd5574 := rd5574₀
  rw [show (⟨96⟩ : UInt256) + (⟨4⟩ + ⟨128⟩) = ⟨228⟩ by decide] at rd5574
  have rd994 := evm_run rd5574 with [jump (by jump_dest)]
  have rd1001₀ := evm_run rd994 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨32⟩ auctionOnlyOwnerStringWord
        solcFreePtrMem_size solcFreePtrMem_read64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd1001 := rd1001₀
  rw [show UInt256.sub (⟨228⟩ : UInt256) ⟨128⟩ = ⟨100⟩ by decide] at rd1001
  exact evm_run rd1001 with [raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem auctionRenounceOwnershipBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (_hcode : I.code = auctionBytecode)
    (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (_hsel : selIs I (auctionSelBytes 8))
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (auctionSelBytes 8) rfl _hsel
  have hdispatch := auctionDispatch_renounceOwnership _hsel
  have hdecode := auctionDecode_renounceOwnership (I := I) hsz4
  have hreach := auctionReachRenounceOwnershipBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    _hcode hsz4 _hsize _hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hownerWord :
        auctionSlotWord ⟨151⟩ σ_evm I = auctionSlotWord ⟨151⟩ σ_solm I :=
      accountMapEquiv_storage_findD _hAccounts I.codeOwner ⟨151⟩ ⟨0⟩
    by_cases howner :
        UInt256.land (auctionSlotWord ⟨151⟩ σ_evm I) solcAddrMask = auctionSourceWord I
    · have hownerSolm :
          UInt256.land (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨151⟩)
              solcAddrMask =
            auctionSourceWord evmS.executionEnv := by
        have hmap :
            UInt256.land (auctionSlotWord ⟨151⟩ σ_solm I) solcAddrMask =
              auctionSourceWord I := by
          simpa [hownerWord] using howner
        simpa [evmS, initState, auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
          auctionSourceWord] using hmap
      have hbody := auctionRenounceOwnershipBodyReturns evmS
        (by simp only [evmS, initState]; exact hwv) hownerSolm
      have hpostAccounts :
          accountMapEquiv (auctionRenounceOwnershipPostMap σ_evm I)
            (auctionRenounceOwnershipPostState evmS).accountMap := by
        have hpostWord :
            auctionSetOwnerWord (Option.option ⟨0⟩
                (fun self => self.lookupStorage ⟨151⟩)
                (Batteries.RBMap.find? σ_solm I.codeOwner)) ⟨0⟩ =
              auctionSetOwnerWord (auctionSlotWord ⟨151⟩ σ_evm I) ⟨0⟩ := by
          have h := congrArg (fun w => auctionSetOwnerWord w ⟨0⟩) hownerWord
          symm
          simpa [auctionSlotWord, Account.lookupStorage] using h
        have hstore := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨151⟩
          (auctionSetOwnerWord (auctionSlotWord ⟨151⟩ σ_evm I) ⟨0⟩) _hAccounts
        simpa [auctionRenounceOwnershipPostMap, auctionRenounceOwnershipPostState,
          auctionSetOwnerPostMap, auctionSetOwnerPostState, evmS, initState,
          storageStore_accountMap, auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
          hpostWord] using hstore
      exact (auctionX_renounceOwnership_success (g := Sat256.ofUInt256 g)
          _hperm hwv howner hreach)
        |>.reEquivExecutionGenAccountMapEquiv _hcode hdispatch hdecode hbody
          (by simp [auctionRenounceOwnershipPostState, auctionSetOwnerPostState, evmS, initState,
            storageStore_createdAccounts])
          hpostAccounts
          (returnEquiv.fallthrough rfl rfl (by native_decide))
    · have hownerSolm :
          UInt256.land (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨151⟩)
              solcAddrMask ≠
            auctionSourceWord evmS.executionEnv := by
        intro h
        apply howner
        have hmap :
            UInt256.land (auctionSlotWord ⟨151⟩ σ_solm I) solcAddrMask =
              auctionSourceWord I := by
          simpa [evmS, initState, auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
            auctionSourceWord] using h
        simpa [hownerWord] using hmap
      have hbody := auctionRenounceOwnershipBodyReverts_owner evmS
        (by simp only [evmS, initState]; exact hwv) hownerSolm
      exact (auctionX_renounceOwnership_revert_owner (g := Sat256.ofUInt256 g)
          hwv howner hreach)
        |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
  · have hbody := auctionRenounceOwnershipBodyReverts_callvalue
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (by simpa [initState] using hwv)
    exact (auctionX_renounceOwnership_callvalue_ne hreach hwv)
      |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody

end Auction
