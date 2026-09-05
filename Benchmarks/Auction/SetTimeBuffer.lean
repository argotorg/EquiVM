import Benchmarks.Auction.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

abbrev auctionSetTimeBufferArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

def auctionSetTimeBufferStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "_timeBuffer"
    (.int (Int.ofNat (auctionSetTimeBufferArgWord I).toNat))

def auctionSetTimeBufferPostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨203⟩ (auctionSetTimeBufferArgWord I)

def auctionSetTimeBufferPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨203⟩
    (auctionSetTimeBufferArgWord I)

theorem auctionSetTimeBufferStore_arg (I : ExecutionEnv) :
    (auctionSetTimeBufferStore I).get? "_timeBuffer" =
      some (.int (Int.ofNat (auctionSetTimeBufferArgWord I).toNat)) := by
  rw [auctionSetTimeBufferStore, store_get_self]

theorem auctionSetTimeBufferStore_owner (I : ExecutionEnv) :
    (auctionSetTimeBufferStore I).get? "_owner" = none := by
  rw [auctionSetTimeBufferStore, store_get_ne _ _ (by decide)]
  native_decide

theorem auctionSetTimeBufferStore_timeBuffer (I : ExecutionEnv) :
    (auctionSetTimeBufferStore I).get? "timeBuffer" = none := by
  rw [auctionSetTimeBufferStore, store_get_ne _ _ (by decide)]
  native_decide

theorem auctionDispatch_setTimeBuffer {I : ExecutionEnv}
    (hsel : selIs I (auctionSelBytes 7)) :
    dispatchMsg auctionContract I.calldata = some setTimeBufferTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [initializeTransition, createBidTransition, settleAndCreateTransition,
      settleAuctionTransition, pauseTransition, unpauseTransition])
    (post := [setReservePriceTransition, setMinBidIncTransition, transferOwnershipTransition,
      renounceOwnershipTransition, ownerGetter, pausedGetter, nounsGetter, wethGetter,
      timeBufferGetter, reservePriceGetter, minBidIncGetter, durationGetter, auctionGetter])
    (ti := setTimeBufferTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = auctionSelBytes 7 := (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, initializeSelectorBytes, createBidSelectorBytes,
        settleAndCreateSelectorBytes, settleAuctionSelectorBytes, pauseSelectorBytes,
        unpauseSelectorBytes, hcd, auctionSelBytes]
      native_decide
  · rw [selectorOf, setTimeBufferSelectorBytes]
    simpa [selIs, auctionSelBytes] using hsel

theorem auctionDecode_setTimeBuffer {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (setTimeBufferTransition.params.map Param.name)
        (transitionSignature setTimeBufferTransition).paramTypes I.calldata =
      some (auctionSetTimeBufferStore I) := by
  show decodeCalldata ["_timeBuffer"] [uint256] I.calldata =
    some (auctionSetTimeBufferStore I)
  simpa [auctionSetTimeBufferStore, auctionSetTimeBufferArgWord, uint256, abiUInt256,
    calldataWord] using
    decodeCalldata_uint256_ok (cd := I.calldata) (x := "_timeBuffer") hsz36 hbig

theorem auctionDecode_setTimeBuffer_none_short {I : ExecutionEnv}
    (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (setTimeBufferTransition.params.map Param.name)
        (transitionSignature setTimeBufferTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["_timeBuffer"] [uint256] I.calldata = none
  simpa [uint256, abiUInt256] using
    decodeCalldata_uint256_none_short (cd := I.calldata) (x := "_timeBuffer") hshort

theorem auctionDecode_setTimeBuffer_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (setTimeBufferTransition.params.map Param.name)
        (transitionSignature setTimeBufferTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["_timeBuffer"] [uint256] I.calldata = none
  simpa [uint256, abiUInt256] using
    decodeCalldata_uint256_none_huge (cd := I.calldata) (x := "_timeBuffer") hbig

theorem evalExpr_setTimeBuffer_owner (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionSetTimeBufferStore I }
        evm (.storage ownerRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := auctionSetTimeBufferStore I } evm ownerRef =
        .ok { base := "_owner", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, ownerRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_owner", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar (t := .address) (hbase := auctionSetTimeBufferStore_owner I)
    (her := her) (hty := hty) (hloc := by rfl)]
  exact congrArg EvalResult.ok (by
    simpa [auctionAddrLoc] using auctionStorageLocLoad_address_offset0 evm ⟨151⟩)

theorem evalExpr_setTimeBuffer_sender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionSetTimeBufferStore I }
      evm sender = .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_setTimeBuffer_owner_eq_true (evm : EVM.State) (I : ExecutionEnv)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionSetTimeBufferStore I }
      evm (.binary .eq sender (.storage ownerRef)) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_setTimeBuffer_sender, evalExpr_setTimeBuffer_owner,
    bind, EvalResult.bind, evalBinaryOp?]
  rw [auctionMaskedAddress_eq_source_of_word_eq (I := evm.executionEnv) howner]
  simp [BEq.beq]

theorem evalExpr_setTimeBuffer_owner_eq_false (evm : EVM.State) (I : ExecutionEnv)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask ≠
        auctionSourceWord evm.executionEnv) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionSetTimeBufferStore I }
      evm (.binary .eq sender (.storage ownerRef)) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_setTimeBuffer_sender, evalExpr_setTimeBuffer_owner,
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

theorem evalExpr_setTimeBuffer_arg (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionSetTimeBufferStore I }
      evm (.var "_timeBuffer") =
        .ok (.int (Int.ofNat (auctionSetTimeBufferArgWord I).toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [auctionSetTimeBufferStore_arg]

theorem auctionSetTimeBufferAssign (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? auctionConfig
        { contract := auctionContract, locals := auctionSetTimeBufferStore I } evm .storage
        timeBufferRef (.int (Int.ofNat (auctionSetTimeBufferArgWord I).toNat)) =
      .ok ({ contract := auctionContract, locals := auctionSetTimeBufferStore I },
        auctionSetTimeBufferPostState evm I) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := auctionSetTimeBufferStore I } evm
      timeBufferRef = .ok { base := "timeBuffer", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, timeBufferRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "timeBuffer", steps := [] } : EvaledStorageRef) =
      some (.elem (.int uint256Int)) := by
    decide
  exact assignStorageRef_storage_scalar (cfg := auctionConfig)
    (solm := { contract := auctionContract, locals := auctionSetTimeBufferStore I })
    (evm := evm) (slot := timeBufferRef) (er := { base := "timeBuffer", steps := [] })
    (ty := .elem (.int uint256Int)) (loc := auctionUint256Loc ⟨203⟩)
    (hbase := auctionSetTimeBufferStore_timeBuffer I) (her := her) (hty := hty)
    (hloc := by rfl) (auctionStorageLocStore_uint256 evm ⟨203⟩
      (auctionSetTimeBufferArgWord I))

theorem auctionSetTimeBufferBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionSetTimeBufferStore I)
      setTimeBufferTransition.body
      (.returned { contract := auctionContract, locals := auctionSetTimeBufferStore I }
        (auctionSetTimeBufferPostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_setTimeBuffer_owner_eq_true evm I howner)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_setTimeBuffer_arg evm I) (auctionSetTimeBufferAssign evm I))
    ExecBlock.nil

theorem auctionSetTimeBufferBodyReverts_callvalue (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionSetTimeBufferStore I)
      setTimeBufferTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalCallvalueEq_false hwv))

theorem auctionSetTimeBufferBodyReverts_owner (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask ≠
        auctionSourceWord evm.executionEnv) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionSetTimeBufferStore I)
      setTimeBufferTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_setTimeBuffer_owner_eq_false evm I howner))

theorem auctionReachSetTimeBufferBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = auctionBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (auctionSelBytes 7)) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨519⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsel' : ((⟨#[0x71, 0x20, 0x33, 0x4b]⟩ : ByteArray) == I.calldata.extract 0 4) = true := by
    simpa [selIs, auctionSelBytes] using hsel
  have hword : auctionSelWord I = ⟨0x7120334b⟩ :=
    auctionSelWord_eq_of_beq I hsz 0x71 0x20 0x33 0x4b ⟨0x7120334b⟩
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
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat auctionBytecode
        (nthArmPc auctionBytecode auctionLowerMidFirstArmPc j)) (auctionSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> decide
  have htake :
      UInt256.eq
        (armSelNat auctionBytecode (nthArmPc auctionBytecode auctionLowerMidFirstArmPc 2))
        (auctionSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide
  exact RD.dispatchTo (code := auctionBytecode) (ee := I) (g := g)
    (s0 := initState cA gh bl σ σ₀ g A I) (selWord := auctionSelWord I)
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (acc := (cA, σ)) ⟨519⟩ 2 h169
    (fun j hj => auctionLowerMidArmsWellFormed j (by omega)) heq0 htake
    (by jump_dest)
    (by native_decide)
    (by simp)

theorem auctionX_setTimeBuffer_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨519⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd519⟩ := hreach
  exact evm_run rd519 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨530⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv),
    push0, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem auctionSetTimeBufferX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨519⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5357⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨545⟩, ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd519⟩ := hreach
  exact ⟨_, _, evm_run rd519 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨530⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push2 ⟨413⟩, push2 ⟨545⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨5357⟩, jump (by jump_dest)]⟩

set_option maxHeartbeats 500000 in
theorem auctionDecodeUint256Ok5357 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5357⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨0⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD auctionBytecode ee g s0 ret (calldataWord ee.calldata 4 :: R)
      mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨5373⟩,
    jumpiT (by rw [hsltval]; decide) (by jump_dest),
    jumpdest, pop, calldataload, swap2, swap1, pop, jump hret]⟩

theorem auctionDecodeUint256LenRevert5357 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5357⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩)
    (hov : R.length + 10 ≤ 1024) :
    RDrev auctionBytecode g s0 :=
  evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨5373⟩,
    jumpiNT (by rw [hsltval]; decide),
    push0, dup1, raw rev 0 (by decide) (fun s _ hstk => memExpRevert0 s hstk) (by
      have hR : R.length ≤ 1024 - 10 := Nat.le_sub_of_add_le hov
      simp only [List.length_cons]
      omega)]

theorem auctionSetTimeBufferX_decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨519⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1934⟩
      [auctionSetTimeBufferArgWord I, ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  obtain ⟨_, _, rd5357⟩ := auctionSetTimeBufferX_toDecoder (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hreach hwv
  obtain ⟨_, _, rd545⟩ :=
    auctionDecodeUint256Ok5357 (R := [⟨413⟩, sel]) rd5357 hslt
      (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa [auctionSetTimeBufferArgWord, calldataWord] using
      evm_run rd545 with [jumpdest, push2 ⟨1934⟩, jump (by jump_dest)]⟩

theorem auctionSetTimeBufferX_decodeRevert_short {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨519⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  obtain ⟨_, _, rd5357⟩ := auctionSetTimeBufferX_toDecoder (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hreach hwv
  exact auctionDecodeUint256LenRevert5357 (R := [⟨413⟩, sel]) rd5357 hslt
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem auctionSetTimeBufferX_decodeRevert_huge {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨519⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  obtain ⟨_, _, rd5357⟩ := auctionSetTimeBufferX_toDecoder (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hreach hwv
  exact auctionDecodeUint256LenRevert5357 (R := [⟨413⟩, sel]) rd5357 hslt
    (by simp only [List.length_cons, List.length_nil]; omega)

def auctionTimeBufferUpdatedTopic : UInt256 :=
  ⟨0x1b55d9f7002bda4490f467e326f22a4a847629c0f2d1ed421607d318d25b410d⟩

set_option maxHeartbeats 1000000 in
theorem auctionX_setTimeBuffer_success {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (howner :
      UInt256.land (auctionSlotWord ⟨151⟩ σ I) solcAddrMask = auctionSourceWord I)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨519⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret auctionBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, auctionSetTimeBufferPostMap σ I) ByteArray.empty := by
  obtain ⟨_, _, rd1934⟩ := auctionSetTimeBufferX_decoded (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := auctionSelWord I) hwv hsz36 hsize hszhi hreach
  have rd1948₀ := evm_run rd1934 with [
    jumpdest, push1 ⟨151⟩]
  obtain ⟨_, _, rd1937₀⟩ := rd1948₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1938⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1938⟩
      [auctionSlotWord ⟨151⟩ σ I, auctionSetTimeBufferArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd1937₀⟩
  have rd1948₁ := evm_run rd1938 with [
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
  have rd1948 := rd1948₁
  rw [heq] at rd1948
  have rd1976 := evm_run rd1948 with [
    push2 ⟨1976⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  have rd1980 := evm_run rd1976 with [push1 ⟨203⟩, dup2, swap1]
  obtain ⟨_, _, rd1982₀⟩ := rd1980.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd1982⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1982⟩
      [auctionSetTimeBufferArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionSetTimeBufferPostMap σ I) k C := by
    exact ⟨_, _, by simpa [auctionSetTimeBufferPostMap] using rd1982₀⟩
  have rd1987 := evm_run rd1982 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    dup2, dup2,
    raw mstore 6 (solcReturnMem (auctionSetTimeBufferArgWord I)) (UInt256.ofNat 5)
      (by decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov)]
  have rd2021 := rd1987.pushConst auctionTimeBufferUpdatedTopic
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd1065 := evm_run rd2021 with [
    swap1, push1 ⟨32⟩, add, push2 ⟨1065⟩, jump (by jump_dest)]
  have rd1072₀ := evm_run rd1065 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost (solcReturnMem_mload64 (auctionSetTimeBufferArgWord I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd1072 := rd1072₀
  rw [show UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩ = ⟨32⟩ by decide] at rd1072
  have rd1074 := RD.log1 0 (UInt256.ofNat 5) rd1072 (by decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by decide) (by evm_ov)
  have rd413 := evm_run rd1074 with [pop, jump (by jump_dest), jumpdest]
  exact rd413.stop (by decide) (by evm_ov)

theorem auctionX_setTimeBuffer_revert_owner {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (howner :
      UInt256.land (auctionSlotWord ⟨151⟩ σ I) solcAddrMask ≠ auctionSourceWord I)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨519⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1934⟩ := auctionSetTimeBufferX_decoded (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := auctionSelWord I) hwv hsz36 hsize hszhi hreach
  have rd1948₀ := evm_run rd1934 with [
    jumpdest, push1 ⟨151⟩]
  obtain ⟨_, _, rd1937₀⟩ := rd1948₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1938⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1938⟩
      [auctionSlotWord ⟨151⟩ σ I, auctionSetTimeBufferArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd1937₀⟩
  have rd1948₁ := evm_run rd1938 with [
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
  have rd1948 := rd1948₁
  rw [heq] at rd1948
  have rd1956 := evm_run rd1948 with [
    push2 ⟨1976⟩, jumpiNT (by decide),
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov)]
  have rd1960 := rd1956.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd5522 := evm_run rd1960 with [
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

theorem auctionSetTimeBufferBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (_hcode : I.code = auctionBytecode)
    (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (_hsel : selIs I (auctionSelBytes 7))
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (auctionSelBytes 7) rfl _hsel
  have hdispatch := auctionDispatch_setTimeBuffer _hsel
  have hreach := auctionReachSetTimeBufferBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    _hcode hsz4 _hsize _hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz36 : 36 ≤ I.calldata.size
    · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
      · let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
        let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
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
          have hdecode := auctionDecode_setTimeBuffer (I := I) hsz36 hbig
          have hbody := auctionSetTimeBufferBodyReturns evmS I
            (by simp only [evmS, initState]; exact hwv) hownerSolm
          have hpostAccounts :
              accountMapEquiv (auctionSetTimeBufferPostMap σ_evm I)
                (auctionSetTimeBufferPostState evmS I).accountMap := by
            simpa [auctionSetTimeBufferPostMap, auctionSetTimeBufferPostState, evmS, initState,
              storageStore_accountMap] using
              accountMapEquiv_sstoreAccountMap I.codeOwner ⟨203⟩
                (auctionSetTimeBufferArgWord I) _hAccounts
          exact (auctionX_setTimeBuffer_success (g := Sat256.ofUInt256 g)
              _hperm hwv hsz36 _hsize hbig howner hreach)
            |>.reEquivExecutionGenAccountMapEquiv _hcode hdispatch hdecode hbody
              (by simp [auctionSetTimeBufferPostState, evmS, initState, storageStore_createdAccounts])
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
          have hdecode := auctionDecode_setTimeBuffer (I := I) hsz36 hbig
          have hbody := auctionSetTimeBufferBodyReverts_owner evmS I
            (by simp only [evmS, initState]; exact hwv) hownerSolm
          exact (auctionX_setTimeBuffer_revert_owner (g := Sat256.ofUInt256 g)
              hwv hsz36 _hsize hbig howner hreach)
            |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
      · have hbigLe : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
        exact (auctionSetTimeBufferX_decodeRevert_huge (g := Sat256.ofUInt256 g)
            hwv _hsize hbigLe hreach)
          |>.reEquivDecodingFailed _hcode hdispatch
            (auctionDecode_setTimeBuffer_none_huge (I := I) hbigLe)
    · have hshort : I.calldata.size < 36 := by omega
      exact (auctionSetTimeBufferX_decodeRevert_short (g := Sat256.ofUInt256 g)
          hwv hsz4 _hsize hshort hreach)
        |>.reEquivDecodingFailed _hcode hdispatch
          (auctionDecode_setTimeBuffer_none_short (I := I) hshort)
  · by_cases hsz36 : 36 ≤ I.calldata.size
    · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
      · have hdecode := auctionDecode_setTimeBuffer (I := I) hsz36 hbig
        have hbody := auctionSetTimeBufferBodyReverts_callvalue
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
          (by simpa [initState] using hwv)
        exact (auctionX_setTimeBuffer_callvalue_ne hreach hwv)
          |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
      · have hbigLe : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
        exact (auctionX_setTimeBuffer_callvalue_ne hreach hwv)
          |>.reEquivDecodingFailed _hcode hdispatch
            (auctionDecode_setTimeBuffer_none_huge (I := I) hbigLe)
    · have hshort : I.calldata.size < 36 := by omega
      exact (auctionX_setTimeBuffer_callvalue_ne hreach hwv)
        |>.reEquivDecodingFailed _hcode hdispatch
          (auctionDecode_setTimeBuffer_none_short (I := I) hshort)

end Auction
