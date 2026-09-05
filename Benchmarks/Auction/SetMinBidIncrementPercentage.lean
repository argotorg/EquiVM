import Benchmarks.Auction.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

abbrev auctionSetMinBidIncrementPercentageArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

def auctionSetMinBidIncrementPercentageStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "_minBidIncrementPercentage"
    (.int (Int.ofNat (auctionSetMinBidIncrementPercentageArgWord I).toNat))

def auctionSetMinBidIncrementPercentagePostMap (σ : AccountMap) (I : ExecutionEnv) :
    AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨205⟩
    (auctionSetUint8Offset0Word (auctionSlotWord ⟨205⟩ σ I)
      (auctionSetMinBidIncrementPercentageArgWord I))

def auctionSetMinBidIncrementPercentagePostState (evm : EVM.State) (I : ExecutionEnv) :
    EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨205⟩
    (auctionSetUint8Offset0Word
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨205⟩)
      (auctionSetMinBidIncrementPercentageArgWord I))

theorem auctionSetMinBidIncrementPercentageStore_arg (I : ExecutionEnv) :
    (auctionSetMinBidIncrementPercentageStore I).get? "_minBidIncrementPercentage" =
      some (.int (Int.ofNat (auctionSetMinBidIncrementPercentageArgWord I).toNat)) := by
  rw [auctionSetMinBidIncrementPercentageStore, store_get_self]

theorem auctionSetMinBidIncrementPercentageStore_owner (I : ExecutionEnv) :
    (auctionSetMinBidIncrementPercentageStore I).get? "_owner" = none := by
  rw [auctionSetMinBidIncrementPercentageStore, store_get_ne _ _ (by decide)]
  native_decide

theorem auctionSetMinBidIncrementPercentageStore_minBidIncrementPercentage (I : ExecutionEnv) :
    (auctionSetMinBidIncrementPercentageStore I).get? "minBidIncrementPercentage" = none := by
  rw [auctionSetMinBidIncrementPercentageStore, store_get_ne _ _ (by decide)]
  native_decide

theorem auctionDispatch_setMinBidIncrementPercentage {I : ExecutionEnv}
    (hsel : selIs I (auctionSelBytes 2)) :
    dispatchMsg auctionContract I.calldata = some setMinBidIncTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [initializeTransition, createBidTransition, settleAndCreateTransition,
      settleAuctionTransition, pauseTransition, unpauseTransition, setTimeBufferTransition,
      setReservePriceTransition])
    (post := [transferOwnershipTransition, renounceOwnershipTransition, ownerGetter, pausedGetter,
      nounsGetter, wethGetter, timeBufferGetter, reservePriceGetter, minBidIncGetter,
      durationGetter, auctionGetter])
    (ti := setMinBidIncTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = auctionSelBytes 2 := (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, initializeSelectorBytes, createBidSelectorBytes,
        settleAndCreateSelectorBytes, settleAuctionSelectorBytes, pauseSelectorBytes,
        unpauseSelectorBytes, setTimeBufferSelectorBytes, setReservePriceSelectorBytes, hcd,
        auctionSelBytes]
      native_decide
  · rw [selectorOf, setMinBidIncSelectorBytes]
    simpa [selIs, auctionSelBytes] using hsel

theorem auctionDecode_setMinBidIncrementPercentage {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (auctionSetMinBidIncrementPercentageArgWord I).toNat < EVM.twoPow 8) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (setMinBidIncTransition.params.map Param.name)
        (transitionSignature setMinBidIncTransition).paramTypes I.calldata =
      some (auctionSetMinBidIncrementPercentageStore I) := by
  show decodeCalldata ["_minBidIncrementPercentage"] [uint8] I.calldata =
    some (auctionSetMinBidIncrementPercentageStore I)
  simpa [auctionSetMinBidIncrementPercentageStore,
    auctionSetMinBidIncrementPercentageArgWord] using
    auctionDecodeCalldata_uint8_ok (cd := I.calldata) (x := "_minBidIncrementPercentage")
      hsz36 hbig hcanon

theorem auctionDecode_setMinBidIncrementPercentage_none_noncanon {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (auctionSetMinBidIncrementPercentageArgWord I).toNat < EVM.twoPow 8) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (setMinBidIncTransition.params.map Param.name)
        (transitionSignature setMinBidIncTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["_minBidIncrementPercentage"] [uint8] I.calldata = none
  simpa [auctionSetMinBidIncrementPercentageArgWord] using
    auctionDecodeCalldata_uint8_none_noncanon (cd := I.calldata)
      (x := "_minBidIncrementPercentage") hsz36 hbig hnc

theorem auctionDecode_setMinBidIncrementPercentage_none_short {I : ExecutionEnv}
    (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (setMinBidIncTransition.params.map Param.name)
        (transitionSignature setMinBidIncTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["_minBidIncrementPercentage"] [uint8] I.calldata = none
  simpa using auctionDecodeCalldata_uint8_none_short (cd := I.calldata)
    (x := "_minBidIncrementPercentage") hshort

theorem auctionDecode_setMinBidIncrementPercentage_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (setMinBidIncTransition.params.map Param.name)
        (transitionSignature setMinBidIncTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["_minBidIncrementPercentage"] [uint8] I.calldata = none
  simpa using auctionDecodeCalldata_uint8_none_huge (cd := I.calldata)
    (x := "_minBidIncrementPercentage") hbig

theorem evalExpr_setMinBidIncrementPercentage_owner (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSetMinBidIncrementPercentageStore I }
        evm (.storage ownerRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := auctionSetMinBidIncrementPercentageStore I }
      evm ownerRef = .ok { base := "_owner", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, ownerRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_owner", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar (t := .address)
    (hbase := auctionSetMinBidIncrementPercentageStore_owner I) (her := her) (hty := hty)
    (hloc := by rfl)]
  exact congrArg EvalResult.ok (by
    simpa [auctionAddrLoc] using auctionStorageLocLoad_address_offset0 evm ⟨151⟩)

theorem evalExpr_setMinBidIncrementPercentage_sender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? auctionConfig
      { contract := auctionContract, locals := auctionSetMinBidIncrementPercentageStore I }
      evm sender = .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_setMinBidIncrementPercentage_owner_eq_true (evm : EVM.State)
    (I : ExecutionEnv)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv) :
    evalExpr? auctionConfig
      { contract := auctionContract, locals := auctionSetMinBidIncrementPercentageStore I }
      evm (.binary .eq sender (.storage ownerRef)) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_setMinBidIncrementPercentage_sender,
    evalExpr_setMinBidIncrementPercentage_owner, bind, EvalResult.bind, evalBinaryOp?]
  rw [auctionMaskedAddress_eq_source_of_word_eq (I := evm.executionEnv) howner]
  simp [BEq.beq]

theorem evalExpr_setMinBidIncrementPercentage_owner_eq_false (evm : EVM.State)
    (I : ExecutionEnv)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask ≠
        auctionSourceWord evm.executionEnv) :
    evalExpr? auctionConfig
      { contract := auctionContract, locals := auctionSetMinBidIncrementPercentageStore I }
      evm (.binary .eq sender (.storage ownerRef)) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_setMinBidIncrementPercentage_sender,
    evalExpr_setMinBidIncrementPercentage_owner, bind, EvalResult.bind, evalBinaryOp?]
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

theorem evalExpr_setMinBidIncrementPercentage_arg (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? auctionConfig
      { contract := auctionContract, locals := auctionSetMinBidIncrementPercentageStore I }
      evm (.var "_minBidIncrementPercentage") =
        .ok (.int (Int.ofNat (auctionSetMinBidIncrementPercentageArgWord I).toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [auctionSetMinBidIncrementPercentageStore_arg]

theorem auctionSetMinBidIncrementPercentageAssign (evm : EVM.State) (I : ExecutionEnv)
    (hcanon : (auctionSetMinBidIncrementPercentageArgWord I).toNat < EVM.twoPow 8) :
    assignStorageRef? auctionConfig
        { contract := auctionContract, locals := auctionSetMinBidIncrementPercentageStore I }
        evm .storage minBidIncRef
        (.int (Int.ofNat (auctionSetMinBidIncrementPercentageArgWord I).toNat)) =
      .ok ({ contract := auctionContract, locals := auctionSetMinBidIncrementPercentageStore I },
        auctionSetMinBidIncrementPercentagePostState evm I) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := auctionSetMinBidIncrementPercentageStore I } evm
      minBidIncRef = .ok { base := "minBidIncrementPercentage", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, minBidIncRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "minBidIncrementPercentage", steps := [] } : EvaledStorageRef) =
      some (.elem (.int uint8Int)) := by
    decide
  exact assignStorageRef_storage_scalar (cfg := auctionConfig)
    (solm := { contract := auctionContract, locals := auctionSetMinBidIncrementPercentageStore I })
    (evm := evm) (slot := minBidIncRef)
    (er := { base := "minBidIncrementPercentage", steps := [] })
    (ty := .elem (.int uint8Int)) (loc := auctionUint8Loc ⟨205⟩)
    (hbase := auctionSetMinBidIncrementPercentageStore_minBidIncrementPercentage I)
    (her := her) (hty := hty) (hloc := by rfl)
    (auctionStorageLocStore_uint8_offset0 evm ⟨205⟩
      (auctionSetMinBidIncrementPercentageArgWord I) hcanon)

theorem auctionSetMinBidIncrementPercentageBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hcanon : (auctionSetMinBidIncrementPercentageArgWord I).toNat < EVM.twoPow 8)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionSetMinBidIncrementPercentageStore I)
      setMinBidIncTransition.body
      (.returned { contract := auctionContract, locals := auctionSetMinBidIncrementPercentageStore I }
        (auctionSetMinBidIncrementPercentagePostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_setMinBidIncrementPercentage_owner_eq_true evm I howner)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_setMinBidIncrementPercentage_arg evm I)
      (auctionSetMinBidIncrementPercentageAssign evm I hcanon))
    ExecBlock.nil

theorem auctionSetMinBidIncrementPercentageBodyReverts_callvalue (evm : EVM.State)
    (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionSetMinBidIncrementPercentageStore I)
      setMinBidIncTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalCallvalueEq_false hwv))

theorem auctionSetMinBidIncrementPercentageBodyReverts_owner (evm : EVM.State)
    (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask ≠
        auctionSourceWord evm.executionEnv) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionSetMinBidIncrementPercentageStore I)
      setMinBidIncTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_setMinBidIncrementPercentage_owner_eq_false evm I howner))

theorem auctionReachSetMinBidIncrementPercentageBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = auctionBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (auctionSelBytes 2)) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨382⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsel' : ((⟨#[0x36, 0xeb, 0xdb, 0x38]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs, auctionSelBytes] using hsel
  have hword : auctionSelWord I = ⟨0x36ebdb38⟩ :=
    auctionSelWord_eq_of_beq I hsz 0x36 0xeb 0xdb 0x38 ⟨0x36ebdb38⟩
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
  have hlower : UInt256.gt (armSelNat auctionBytecode auctionLowerSplitPc) (auctionSelWord I) ≠
      ⟨0⟩ := by
    rw [hword]
    decide
  have h227 := RD.selectorSplitTakenAuto h158 auctionLowerSplitWellFormed hlower
    (by jump_dest) (by simp)
  have h228 := h227.jumpdest (by decide) (by simp)
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat auctionBytecode
        (nthArmPc auctionBytecode auctionLowerLowFirstArmPc j)) (auctionSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> decide
  have htake :
      UInt256.eq
        (armSelNat auctionBytecode (nthArmPc auctionBytecode auctionLowerLowFirstArmPc 2))
        (auctionSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide
  exact RD.dispatchTo (code := auctionBytecode) (ee := I) (g := g)
    (s0 := initState cA gh bl σ σ₀ g A I) (selWord := auctionSelWord I)
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (acc := (cA, σ)) ⟨382⟩ 2 h228
    (fun j hj => auctionLowerLowArmsWellFormed j (by omega)) heq0 htake
    (by jump_dest)
    (by native_decide)
    (by simp)

theorem auctionX_setMinBidIncrementPercentage_callvalue_ne {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨382⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd382⟩ := hreach
  exact evm_run rd382 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨393⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv),
    push0, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem auctionSetMinBidIncrementPercentageX_toDecoder {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨382⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5325⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨408⟩, ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd382⟩ := hreach
  exact ⟨_, _, evm_run rd382 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨393⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push2 ⟨413⟩, push2 ⟨408⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨5325⟩, jump (by jump_dest)]⟩

set_option maxHeartbeats 500000 in
theorem auctionDecodeUint8Ok5325 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5325⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨0⟩)
    (hcanon : (calldataWord ee.calldata 4).toNat < EVM.twoPow 8)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD auctionBytecode ee g s0 ret (calldataWord ee.calldata 4 :: R)
      mem aw rdata acc k' C' := by
  have hclean : UInt256.land (calldataWord ee.calldata 4) ⟨255⟩ =
      calldataWord ee.calldata 4 :=
    auctionLand255_eq_self_of_uint8 (calldataWord ee.calldata 4) hcanon
  have heq : UInt256.eq (calldataWord ee.calldata 4)
      (UInt256.land (calldataWord ee.calldata 4) ⟨255⟩) = ⟨1⟩ := by
    rw [hclean, u256_eq_refl]
  exact ⟨_, _, evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨5341⟩,
    jumpiT (by rw [hsltval]; decide) (by jump_dest),
    jumpdest, push2 ⟨5350⟩, dup3, push2 ⟨5304⟩, jump (by jump_dest),
    jumpdest, dup1, calldataload, push1 ⟨255⟩, dup2, and, dup2, eq, push2 ⟨5320⟩,
    jumpiT (by
      change UInt256.eq (calldataWord ee.calldata 4)
        (UInt256.land (calldataWord ee.calldata 4) ⟨255⟩) ≠ ⟨0⟩
      rw [heq]
      decide) (by jump_dest),
    jumpdest, swap2, swap1, pop, jump (by jump_dest),
    jumpdest, swap4, swap3, pop, pop, pop, jump hret]⟩

theorem auctionDecodeUint8LenRevert5325 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5325⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩)
    (hov : R.length + 10 ≤ 1024) :
    RDrev auctionBytecode g s0 :=
  evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨5341⟩,
    jumpiNT (by rw [hsltval]; decide),
    push0, dup1, raw rev 0 (by decide) (fun s _ hstk => memExpRevert0 s hstk) (by
      have hR : R.length ≤ 1024 - 10 := Nat.le_sub_of_add_le hov
      simp only [List.length_cons]
      omega)]

set_option maxHeartbeats 500000 in
theorem auctionDecodeUint8NoncanonRevert5325 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5325⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨0⟩)
    (hnc : ¬ (calldataWord ee.calldata 4).toNat < EVM.twoPow 8)
    (hov : R.length + 10 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  have hne : calldataWord ee.calldata 4 ≠
      UInt256.land (calldataWord ee.calldata 4) ⟨255⟩ :=
    (auctionLand255_ne_self_of_not_uint8 (calldataWord ee.calldata 4) hnc).symm
  have heq : UInt256.eq (calldataWord ee.calldata 4)
      (UInt256.land (calldataWord ee.calldata 4) ⟨255⟩) = ⟨0⟩ :=
    u256_eq_of_ne hne
  exact evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨5341⟩,
    jumpiT (by rw [hsltval]; decide) (by jump_dest),
    jumpdest, push2 ⟨5350⟩, dup3, push2 ⟨5304⟩, jump (by jump_dest),
    jumpdest, dup1, calldataload, push1 ⟨255⟩, dup2, and, dup2, eq, push2 ⟨5320⟩,
    jumpiNT (by
      change UInt256.eq (calldataWord ee.calldata 4)
        (UInt256.land (calldataWord ee.calldata 4) ⟨255⟩) = ⟨0⟩
      exact heq),
    push0, dup1, raw rev 0 (by decide) (fun s _ hstk => memExpRevert0 s hstk) (by
      have hR : R.length ≤ 1024 - 10 := Nat.le_sub_of_add_le hov
      simp only [List.length_cons]
      omega)]

theorem auctionSetMinBidIncrementPercentageX_decoded {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (auctionSetMinBidIncrementPercentageArgWord I).toNat < EVM.twoPow 8)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨382⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨952⟩
      [auctionSetMinBidIncrementPercentageArgWord I, ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  obtain ⟨_, _, rd5325⟩ := auctionSetMinBidIncrementPercentageX_toDecoder (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hreach hwv
  obtain ⟨_, _, rd408⟩ :=
    auctionDecodeUint8Ok5325 (R := [⟨413⟩, sel]) rd5325 hslt hcanon
      (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa [auctionSetMinBidIncrementPercentageArgWord, calldataWord] using
      evm_run rd408 with [jumpdest, push2 ⟨952⟩, jump (by jump_dest)]⟩

theorem auctionSetMinBidIncrementPercentageX_decodeRevert_short {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨382⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  obtain ⟨_, _, rd5325⟩ := auctionSetMinBidIncrementPercentageX_toDecoder (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hreach hwv
  exact auctionDecodeUint8LenRevert5325 (R := [⟨413⟩, sel]) rd5325 hslt
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem auctionSetMinBidIncrementPercentageX_decodeRevert_huge {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨382⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  obtain ⟨_, _, rd5325⟩ := auctionSetMinBidIncrementPercentageX_toDecoder (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hreach hwv
  exact auctionDecodeUint8LenRevert5325 (R := [⟨413⟩, sel]) rd5325 hslt
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem auctionSetMinBidIncrementPercentageX_decodeRevert_noncanon {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (auctionSetMinBidIncrementPercentageArgWord I).toNat < EVM.twoPow 8)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨382⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  obtain ⟨_, _, rd5325⟩ := auctionSetMinBidIncrementPercentageX_toDecoder (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hreach hwv
  exact auctionDecodeUint8NoncanonRevert5325 (R := [⟨413⟩, sel]) rd5325 hslt
    (by simpa [auctionSetMinBidIncrementPercentageArgWord, calldataWord] using hnc)
    (by simp only [List.length_cons, List.length_nil]; omega)

def auctionMinBidIncrementPercentageUpdatedTopic : UInt256 :=
  ⟨0xec5ccd96cc77b6219e9d44143df916af68fc169339ea7de5008ff15eae13450d⟩

set_option maxHeartbeats 1000000 in
theorem auctionX_setMinBidIncrementPercentage_success {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (auctionSetMinBidIncrementPercentageArgWord I).toNat < EVM.twoPow 8)
    (howner :
      UInt256.land (auctionSlotWord ⟨151⟩ σ I) solcAddrMask = auctionSourceWord I)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨382⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret auctionBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, auctionSetMinBidIncrementPercentagePostMap σ I) ByteArray.empty := by
  obtain ⟨_, _, rd952⟩ := auctionSetMinBidIncrementPercentageX_decoded (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := auctionSelWord I) hwv hsz36 hsize hszhi hcanon hreach
  have rd956₀ := evm_run rd952 with [
    jumpdest, push1 ⟨151⟩]
  obtain ⟨_, _, rd955₀⟩ := rd956₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd956⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨956⟩
      [auctionSlotWord ⟨151⟩ σ I, auctionSetMinBidIncrementPercentageArgWord I, ⟨413⟩,
        auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd955₀⟩
  have rd967₁ := evm_run rd956 with [
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
  have rd967 := rd967₁
  rw [heq] at rd967
  have rd1003 := evm_run rd967 with [
    push2 ⟨1003⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  have rd1008₀ := evm_run rd1003 with [push1 ⟨205⟩, dup1]
  obtain ⟨_, _, rd1008₁⟩ := rd1008₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1008⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1008⟩
      [auctionSlotWord ⟨205⟩ σ I, ⟨205⟩, auctionSetMinBidIncrementPercentageArgWord I,
        ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd1008₁⟩
  have hclean : UInt256.land (auctionSetMinBidIncrementPercentageArgWord I) ⟨255⟩ =
      auctionSetMinBidIncrementPercentageArgWord I :=
    auctionLand255_eq_self_of_uint8 _ hcanon
  have hclearComm : UInt256.land (UInt256.lnot ⟨255⟩) (auctionSlotWord ⟨205⟩ σ I) =
      UInt256.land (auctionSlotWord ⟨205⟩ σ I) (UInt256.lnot ⟨255⟩) :=
    u256_land_comm (UInt256.lnot ⟨255⟩) (auctionSlotWord ⟨205⟩ σ I)
  have hpostComm :
      UInt256.lor (auctionSetMinBidIncrementPercentageArgWord I)
          (UInt256.land (auctionSlotWord ⟨205⟩ σ I) (UInt256.lnot ⟨255⟩)) =
        auctionSetUint8Offset0Word (auctionSlotWord ⟨205⟩ σ I)
          (auctionSetMinBidIncrementPercentageArgWord I) := by
    unfold auctionSetUint8Offset0Word
    rw [u256_lor_comm]
  have rd1022₀ := evm_run rd1008 with [
    push1 ⟨255⟩, not, and, push1 ⟨255⟩, dup4, and, swap1, dup2, lor, swap1, swap2]
  rw [hclearComm, hclean, hpostComm] at rd1022₀
  obtain ⟨_, _, rd1022₁⟩ := rd1022₀.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd1022⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1022⟩
      [auctionSetMinBidIncrementPercentageArgWord I, auctionSetMinBidIncrementPercentageArgWord I,
        ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionSetMinBidIncrementPercentagePostMap σ I) k C := by
    exact ⟨_, _, by simpa [auctionSetMinBidIncrementPercentagePostMap] using rd1022₁⟩
  have rd1028 := evm_run rd1022 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    swap1, dup2,
    raw mstore 6 (solcReturnMem (auctionSetMinBidIncrementPercentageArgWord I))
      (UInt256.ofNat 5) (by decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov)]
  have rd1061 := rd1028.pushConst auctionMinBidIncrementPercentageUpdatedTopic
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd1065 := evm_run rd1061 with [swap1, push1 ⟨32⟩, add]
  have rd1073₀ := evm_run rd1065 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost (solcReturnMem_mload64 (auctionSetMinBidIncrementPercentageArgWord I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd1073 := rd1073₀
  rw [show UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩ = ⟨32⟩ by decide] at rd1073
  have rd1074 := RD.log1 0 (UInt256.ofNat 5) rd1073 (by decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by decide) (by evm_ov)
  have rd413 := evm_run rd1074 with [pop, jump (by jump_dest), jumpdest]
  exact rd413.stop (by decide) (by evm_ov)

theorem auctionX_setMinBidIncrementPercentage_revert_owner {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (auctionSetMinBidIncrementPercentageArgWord I).toNat < EVM.twoPow 8)
    (howner :
      UInt256.land (auctionSlotWord ⟨151⟩ σ I) solcAddrMask ≠ auctionSourceWord I)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨382⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd952⟩ := auctionSetMinBidIncrementPercentageX_decoded (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := auctionSelWord I) hwv hsz36 hsize hszhi hcanon hreach
  have rd956₀ := evm_run rd952 with [
    jumpdest, push1 ⟨151⟩]
  obtain ⟨_, _, rd955₀⟩ := rd956₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd956⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨956⟩
      [auctionSlotWord ⟨151⟩ σ I, auctionSetMinBidIncrementPercentageArgWord I, ⟨413⟩,
        auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd955₀⟩
  have rd967₁ := evm_run rd956 with [
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
          (auctionSlotWord ⟨151⟩ σ I)) = ⟨0⟩ :=
    u256_eq_of_ne hneq
  have rd967 := rd967₁
  rw [heq] at rd967
  have rd971 := evm_run rd967 with [
    push2 ⟨1003⟩, jumpiNT (by decide),
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov)]
  have rd974 := rd971.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd5522 := evm_run rd974 with [
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

theorem auctionSetMinBidIncrementPercentageBodyCore {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (_hcode : I.code = auctionBytecode)
    (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (_hsel : selIs I (auctionSelBytes 2))
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (auctionSelBytes 2) rfl _hsel
  have hdispatch := auctionDispatch_setMinBidIncrementPercentage _hsel
  have hreach := auctionReachSetMinBidIncrementPercentageBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    _hcode hsz4 _hsize _hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz36 : 36 ≤ I.calldata.size
    · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
      · by_cases hcanon :
            (auctionSetMinBidIncrementPercentageArgWord I).toNat < EVM.twoPow 8
        · let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
          let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
          have hownerWord :
              auctionSlotWord ⟨151⟩ σ_evm I = auctionSlotWord ⟨151⟩ σ_solm I :=
            accountMapEquiv_storage_findD _hAccounts I.codeOwner ⟨151⟩ ⟨0⟩
          have hminBidWord :
              auctionSlotWord ⟨205⟩ σ_evm I = auctionSlotWord ⟨205⟩ σ_solm I :=
            accountMapEquiv_storage_findD _hAccounts I.codeOwner ⟨205⟩ ⟨0⟩
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
            have hdecode := auctionDecode_setMinBidIncrementPercentage (I := I)
              hsz36 hbig hcanon
            have hbody := auctionSetMinBidIncrementPercentageBodyReturns evmS I
              (by simp only [evmS, initState]; exact hwv) hcanon hownerSolm
            have hpostVal :
                auctionSetUint8Offset0Word (auctionSlotWord ⟨205⟩ σ_evm I)
                    (auctionSetMinBidIncrementPercentageArgWord I) =
                  auctionSetUint8Offset0Word (auctionSlotWord ⟨205⟩ σ_solm I)
                    (auctionSetMinBidIncrementPercentageArgWord I) := by
              rw [hminBidWord]
            have hpostAccounts :
                accountMapEquiv (auctionSetMinBidIncrementPercentagePostMap σ_evm I)
                  (auctionSetMinBidIncrementPercentagePostState evmS I).accountMap := by
              simpa [auctionSetMinBidIncrementPercentagePostMap,
                auctionSetMinBidIncrementPercentagePostState, evmS, initState,
                storageStore_accountMap, Solm.EVM.storageLoad, State.lookupAccount, hpostVal] using
                accountMapEquiv_sstoreAccountMap I.codeOwner ⟨205⟩
                  (auctionSetUint8Offset0Word (auctionSlotWord ⟨205⟩ σ_evm I)
                    (auctionSetMinBidIncrementPercentageArgWord I)) _hAccounts
            exact (auctionX_setMinBidIncrementPercentage_success (g := Sat256.ofUInt256 g)
                _hperm hwv hsz36 _hsize hbig hcanon howner hreach)
              |>.reEquivExecutionGenAccountMapEquiv _hcode hdispatch hdecode hbody
                (by simp [auctionSetMinBidIncrementPercentagePostState, evmS, initState,
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
            have hdecode := auctionDecode_setMinBidIncrementPercentage (I := I)
              hsz36 hbig hcanon
            have hbody := auctionSetMinBidIncrementPercentageBodyReverts_owner evmS I
              (by simp only [evmS, initState]; exact hwv) hownerSolm
            exact (auctionX_setMinBidIncrementPercentage_revert_owner (g := Sat256.ofUInt256 g)
                hwv hsz36 _hsize hbig hcanon howner hreach)
              |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
        · exact (auctionSetMinBidIncrementPercentageX_decodeRevert_noncanon
              (g := Sat256.ofUInt256 g) hwv hsz36 _hsize hbig hcanon hreach)
            |>.reEquivDecodingFailed _hcode hdispatch
              (auctionDecode_setMinBidIncrementPercentage_none_noncanon (I := I)
                hsz36 hbig hcanon)
      · have hbigLe : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
        exact (auctionSetMinBidIncrementPercentageX_decodeRevert_huge (g := Sat256.ofUInt256 g)
            hwv _hsize hbigLe hreach)
          |>.reEquivDecodingFailed _hcode hdispatch
            (auctionDecode_setMinBidIncrementPercentage_none_huge (I := I) hbigLe)
    · have hshort : I.calldata.size < 36 := by omega
      exact (auctionSetMinBidIncrementPercentageX_decodeRevert_short (g := Sat256.ofUInt256 g)
          hwv hsz4 _hsize hshort hreach)
        |>.reEquivDecodingFailed _hcode hdispatch
          (auctionDecode_setMinBidIncrementPercentage_none_short (I := I) hshort)
  · by_cases hsz36 : 36 ≤ I.calldata.size
    · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
      · by_cases hcanon :
            (auctionSetMinBidIncrementPercentageArgWord I).toNat < EVM.twoPow 8
        · have hdecode := auctionDecode_setMinBidIncrementPercentage (I := I)
            hsz36 hbig hcanon
          have hbody := auctionSetMinBidIncrementPercentageBodyReverts_callvalue
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (by simpa [initState] using hwv)
          exact (auctionX_setMinBidIncrementPercentage_callvalue_ne hreach hwv)
            |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
        · exact (auctionX_setMinBidIncrementPercentage_callvalue_ne hreach hwv)
            |>.reEquivDecodingFailed _hcode hdispatch
              (auctionDecode_setMinBidIncrementPercentage_none_noncanon (I := I)
                hsz36 hbig hcanon)
      · have hbigLe : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
        exact (auctionX_setMinBidIncrementPercentage_callvalue_ne hreach hwv)
          |>.reEquivDecodingFailed _hcode hdispatch
            (auctionDecode_setMinBidIncrementPercentage_none_huge (I := I) hbigLe)
    · have hshort : I.calldata.size < 36 := by omega
      exact (auctionX_setMinBidIncrementPercentage_callvalue_ne hreach hwv)
        |>.reEquivDecodingFailed _hcode hdispatch
          (auctionDecode_setMinBidIncrementPercentage_none_short (I := I) hshort)

end Auction
