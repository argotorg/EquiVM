import Benchmarks.Auction.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

abbrev auctionSetReservePriceArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

def auctionSetReservePriceStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "_reservePrice"
    (.int (Int.ofNat (auctionSetReservePriceArgWord I).toNat))

def auctionSetReservePricePostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨204⟩ (auctionSetReservePriceArgWord I)

def auctionSetReservePricePostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨204⟩
    (auctionSetReservePriceArgWord I)

theorem auctionSetReservePriceStore_arg (I : ExecutionEnv) :
    (auctionSetReservePriceStore I).get? "_reservePrice" =
      some (.int (Int.ofNat (auctionSetReservePriceArgWord I).toNat)) := by
  rw [auctionSetReservePriceStore, store_get_self]

theorem auctionSetReservePriceStore_owner (I : ExecutionEnv) :
    (auctionSetReservePriceStore I).get? "_owner" = none := by
  rw [auctionSetReservePriceStore, store_get_ne _ _ (by decide)]
  native_decide

theorem auctionSetReservePriceStore_reservePrice (I : ExecutionEnv) :
    (auctionSetReservePriceStore I).get? "reservePrice" = none := by
  rw [auctionSetReservePriceStore, store_get_ne _ _ (by decide)]
  native_decide

theorem auctionDispatch_setReservePrice {I : ExecutionEnv}
    (hsel : selIs I (auctionSelBytes 15)) :
    dispatchMsg auctionContract I.calldata = some setReservePriceTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [initializeTransition, createBidTransition, settleAndCreateTransition,
      settleAuctionTransition, pauseTransition, unpauseTransition, setTimeBufferTransition])
    (post := [setMinBidIncTransition, transferOwnershipTransition, renounceOwnershipTransition,
      ownerGetter, pausedGetter, nounsGetter, wethGetter, timeBufferGetter, reservePriceGetter,
      minBidIncGetter, durationGetter, auctionGetter])
    (ti := setReservePriceTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = auctionSelBytes 15 := (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, initializeSelectorBytes, createBidSelectorBytes,
        settleAndCreateSelectorBytes, settleAuctionSelectorBytes, pauseSelectorBytes,
        unpauseSelectorBytes, setTimeBufferSelectorBytes, hcd, auctionSelBytes]
      native_decide
  · rw [selectorOf, setReservePriceSelectorBytes]
    simpa [selIs, auctionSelBytes] using hsel

theorem auctionDecode_setReservePrice {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (setReservePriceTransition.params.map Param.name)
        (transitionSignature setReservePriceTransition).paramTypes I.calldata =
      some (auctionSetReservePriceStore I) := by
  show decodeCalldata ["_reservePrice"] [uint256] I.calldata =
    some (auctionSetReservePriceStore I)
  simpa [auctionSetReservePriceStore, auctionSetReservePriceArgWord, uint256, abiUInt256,
    calldataWord] using
    decodeCalldata_uint256_ok (cd := I.calldata) (x := "_reservePrice") hsz36 hbig

theorem auctionDecode_setReservePrice_none_short {I : ExecutionEnv}
    (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (setReservePriceTransition.params.map Param.name)
        (transitionSignature setReservePriceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["_reservePrice"] [uint256] I.calldata = none
  simpa [uint256, abiUInt256] using
    decodeCalldata_uint256_none_short (cd := I.calldata) (x := "_reservePrice") hshort

theorem auctionDecode_setReservePrice_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (setReservePriceTransition.params.map Param.name)
        (transitionSignature setReservePriceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["_reservePrice"] [uint256] I.calldata = none
  simpa [uint256, abiUInt256] using
    decodeCalldata_uint256_none_huge (cd := I.calldata) (x := "_reservePrice") hbig

theorem evalExpr_setReservePrice_owner (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionSetReservePriceStore I }
        evm (.storage ownerRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := auctionSetReservePriceStore I } evm ownerRef =
        .ok { base := "_owner", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, ownerRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_owner", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar (t := .address) (hbase := auctionSetReservePriceStore_owner I)
    (her := her) (hty := hty) (hloc := by rfl)]
  exact congrArg EvalResult.ok (by
    simpa [auctionAddrLoc] using auctionStorageLocLoad_address_offset0 evm ⟨151⟩)

theorem evalExpr_setReservePrice_sender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionSetReservePriceStore I }
      evm sender = .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_setReservePrice_owner_eq_true (evm : EVM.State) (I : ExecutionEnv)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionSetReservePriceStore I }
      evm (.binary .eq sender (.storage ownerRef)) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_setReservePrice_sender, evalExpr_setReservePrice_owner,
    bind, EvalResult.bind, evalBinaryOp?]
  rw [auctionMaskedAddress_eq_source_of_word_eq (I := evm.executionEnv) howner]
  simp [BEq.beq]

theorem evalExpr_setReservePrice_owner_eq_false (evm : EVM.State) (I : ExecutionEnv)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask ≠
        auctionSourceWord evm.executionEnv) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionSetReservePriceStore I }
      evm (.binary .eq sender (.storage ownerRef)) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_setReservePrice_sender, evalExpr_setReservePrice_owner,
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

theorem evalExpr_setReservePrice_arg (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionSetReservePriceStore I }
      evm (.var "_reservePrice") =
        .ok (.int (Int.ofNat (auctionSetReservePriceArgWord I).toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [auctionSetReservePriceStore_arg]

theorem auctionSetReservePriceAssign (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? auctionConfig
        { contract := auctionContract, locals := auctionSetReservePriceStore I } evm .storage
        reservePriceRef (.int (Int.ofNat (auctionSetReservePriceArgWord I).toNat)) =
      .ok ({ contract := auctionContract, locals := auctionSetReservePriceStore I },
        auctionSetReservePricePostState evm I) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := auctionSetReservePriceStore I } evm
      reservePriceRef = .ok { base := "reservePrice", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, reservePriceRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "reservePrice", steps := [] } : EvaledStorageRef) =
      some (.elem (.int uint256Int)) := by
    decide
  exact assignStorageRef_storage_scalar (cfg := auctionConfig)
    (solm := { contract := auctionContract, locals := auctionSetReservePriceStore I })
    (evm := evm) (slot := reservePriceRef) (er := { base := "reservePrice", steps := [] })
    (ty := .elem (.int uint256Int)) (loc := auctionUint256Loc ⟨204⟩)
    (hbase := auctionSetReservePriceStore_reservePrice I) (her := her) (hty := hty)
    (hloc := by rfl) (auctionStorageLocStore_uint256 evm ⟨204⟩
      (auctionSetReservePriceArgWord I))

theorem auctionSetReservePriceBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionSetReservePriceStore I)
      setReservePriceTransition.body
      (.returned { contract := auctionContract, locals := auctionSetReservePriceStore I }
        (auctionSetReservePricePostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_setReservePrice_owner_eq_true evm I howner)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_setReservePrice_arg evm I) (auctionSetReservePriceAssign evm I))
    ExecBlock.nil

theorem auctionSetReservePriceBodyReverts_callvalue (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionSetReservePriceStore I)
      setReservePriceTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalCallvalueEq_false hwv))

theorem auctionSetReservePriceBodyReverts_owner (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask ≠
        auctionSourceWord evm.executionEnv) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionSetReservePriceStore I)
      setReservePriceTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_setReservePrice_owner_eq_false evm I howner))

theorem auctionReachSetReservePriceBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = auctionBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (auctionSelBytes 15)) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨828⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsel' : ((⟨#[0xce, 0x9c, 0x7c, 0x0d]⟩ : ByteArray) == I.calldata.extract 0 4) = true := by
    simpa [selIs, auctionSelBytes] using hsel
  have hword : auctionSelWord I = ⟨0xce9c7c0d⟩ :=
    auctionSelWord_eq_of_beq I hsz 0xce 0x9c 0x7c 0x0d ⟨0xce9c7c0d⟩
      (by native_decide) hsel'
  obtain ⟨_, _, hsplit⟩ := auctionReachRootSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
  have hroot : UInt256.gt (armSelNat auctionBytecode auctionSplitPc) (auctionSelWord I) =
      ⟨0⟩ := by
    rw [hword]
    native_decide
  have h29 := auctionSelectorSplitNotTakenTo hsplit auctionSplitWellFormed hroot
      auctionRootSplitNextPc (by simp)
  have hupper : UInt256.gt (armSelNat auctionBytecode auctionUpperSplitPc) (auctionSelWord I) =
      ⟨0⟩ := by
    rw [hword]
    native_decide
  have h40 := auctionSelectorSplitNotTakenTo h29 auctionUpperSplitWellFormed hupper
      auctionUpperSplitNextPc (by simp)
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat auctionBytecode
        (nthArmPc auctionBytecode auctionUpperMidFirstArmPc j)) (auctionSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq
        (armSelNat auctionBytecode (nthArmPc auctionBytecode auctionUpperMidFirstArmPc 0))
        (auctionSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo (code := auctionBytecode) (ee := I) (g := g)
    (s0 := initState cA gh bl σ σ₀ g A I) (selWord := auctionSelWord I)
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (acc := (cA, σ)) ⟨828⟩ 0 h40
    (fun j hj => auctionUpperMidArmsWellFormed j (by omega)) heq0 htake
    (by jump_dest)
    (by native_decide)
    (by simp)

theorem auctionX_setReservePrice_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨828⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd519⟩ := hreach
  exact evm_run rd519 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨839⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv),
    push0, dup1, raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem auctionSetReservePriceX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨828⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5357⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨854⟩, ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd519⟩ := hreach
  exact ⟨_, _, evm_run rd519 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨839⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push2 ⟨413⟩, push2 ⟨854⟩, calldatasize, push1 ⟨4⟩,
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
    push0, dup1, raw rev 0 (by native_decide) (fun s _ hstk => memExpRevert0 s hstk) (by
      have hR : R.length ≤ 1024 - 10 := Nat.le_sub_of_add_le hov
      simp only [List.length_cons]
      omega)]

theorem auctionSetReservePriceX_decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨828⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2478⟩
      [auctionSetReservePriceArgWord I, ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  obtain ⟨_, _, rd5357⟩ := auctionSetReservePriceX_toDecoder (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hreach hwv
  obtain ⟨_, _, rd545⟩ :=
    auctionDecodeUint256Ok5357 (R := [⟨413⟩, sel]) rd5357 hslt
      (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa [auctionSetReservePriceArgWord, calldataWord] using
      evm_run rd545 with [jumpdest, push2 ⟨2478⟩, jump (by jump_dest)]⟩

theorem auctionSetReservePriceX_decodeRevert_short {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨828⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  obtain ⟨_, _, rd5357⟩ := auctionSetReservePriceX_toDecoder (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hreach hwv
  exact auctionDecodeUint256LenRevert5357 (R := [⟨413⟩, sel]) rd5357 hslt
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem auctionSetReservePriceX_decodeRevert_huge {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨828⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  obtain ⟨_, _, rd5357⟩ := auctionSetReservePriceX_toDecoder (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hreach hwv
  exact auctionDecodeUint256LenRevert5357 (R := [⟨413⟩, sel]) rd5357 hslt
    (by simp only [List.length_cons, List.length_nil]; omega)

def auctionReservePriceUpdatedTopic : UInt256 :=
  ⟨0x6ab2e127d7fdf53b8f304e59d3aab5bfe97979f52a85479691a6fab27a28a6b2⟩

set_option maxHeartbeats 1000000 in
theorem auctionX_setReservePrice_success {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (howner :
      UInt256.land (auctionSlotWord ⟨151⟩ σ I) solcAddrMask = auctionSourceWord I)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨828⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret auctionBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, auctionSetReservePricePostMap σ I) ByteArray.empty := by
  obtain ⟨_, _, rd2478⟩ := auctionSetReservePriceX_decoded (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := auctionSelWord I) hwv hsz36 hsize hszhi hreach
  have rd2492₀ := evm_run rd2478 with [
    jumpdest, push1 ⟨151⟩]
  obtain ⟨_, _, rd2481₀⟩ := rd2492₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2482⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2482⟩
      [auctionSlotWord ⟨151⟩ σ I, auctionSetReservePriceArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2481₀⟩
  have rd2492₁ := evm_run rd2482 with [
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
  have rd2492 := rd2492₁
  rw [heq] at rd2492
  have rd2520 := evm_run rd2492 with [
    push2 ⟨2520⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  have rd2524 := evm_run rd2520 with [push1 ⟨204⟩, dup2, swap1]
  obtain ⟨_, _, rd2526₀⟩ := rd2524.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2526⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2526⟩
      [auctionSetReservePriceArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionSetReservePricePostMap σ I) k C := by
    exact ⟨_, _, by simpa [auctionSetReservePricePostMap] using rd2526₀⟩
  have rd2531 := evm_run rd2526 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    dup2, dup2,
    raw mstore 6 (solcReturnMem (auctionSetReservePriceArgWord I)) (UInt256.ofNat 5)
      (by native_decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov)]
  have rd2565 := rd2531.pushConst auctionReservePriceUpdatedTopic
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd1065 := evm_run rd2565 with [
    swap1, push1 ⟨32⟩, add, push2 ⟨1065⟩, jump (by jump_dest)]
  have rd1072₀ := evm_run rd1065 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost (solcReturnMem_mload64 (auctionSetReservePriceArgWord I))
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
  exact rd413.stop (by native_decide) (by evm_ov)

theorem auctionX_setReservePrice_revert_owner {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (howner :
      UInt256.land (auctionSlotWord ⟨151⟩ σ I) solcAddrMask ≠ auctionSourceWord I)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨828⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2478⟩ := auctionSetReservePriceX_decoded (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := auctionSelWord I) hwv hsz36 hsize hszhi hreach
  have rd2492₀ := evm_run rd2478 with [
    jumpdest, push1 ⟨151⟩]
  obtain ⟨_, _, rd2481₀⟩ := rd2492₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2482⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2482⟩
      [auctionSlotWord ⟨151⟩ σ I, auctionSetReservePriceArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2481₀⟩
  have rd2492₁ := evm_run rd2482 with [
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
  have rd2492 := rd2492₁
  rw [heq] at rd2492
  have rd2500 := evm_run rd2492 with [
    push2 ⟨2520⟩, jumpiNT (by decide),
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov)]
  have rd2504 := rd2500.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by native_decide) (by evm_ov)
  have rd5522 := evm_run rd2504 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 6 (solcReturnMem ⟨0x08c379a000000000000000000000000000000000000000000000000000000000⟩)
      (UInt256.ofNat 5) (by native_decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨4⟩, add, push2 ⟨994⟩, swap1, push2 ⟨5522⟩, jump (by jump_dest)]
  have rd5532 := evm_run rd5522 with [
    jumpdest, push1 ⟨32⟩, dup1, dup3,
    raw mstore 3 (solcErrorStringMem1 solcFreePtrMem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    dup2, dup2, add,
    raw mstore 3 (solcErrorStringMem2 ⟨32⟩ solcFreePtrMem) (UInt256.ofNat 7)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd5565 := rd5532.pushConst auctionOnlyOwnerStringWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd5574₀ := evm_run rd5565 with [
    push1 ⟨64⟩, dup3, add,
    raw mstore 3 (solcErrorStringMem3 ⟨32⟩ auctionOnlyOwnerStringWord solcFreePtrMem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨96⟩, add, swap1]
  have rd5574 := rd5574₀
  rw [show (⟨96⟩ : UInt256) + (⟨4⟩ + ⟨128⟩) = ⟨228⟩ by decide] at rd5574
  have rd994 := evm_run rd5574 with [jump (by jump_dest)]
  have rd1001₀ := evm_run rd994 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨32⟩ auctionOnlyOwnerStringWord
        solcFreePtrMem_size solcFreePtrMem_read64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd1001 := rd1001₀
  rw [show UInt256.sub (⟨228⟩ : UInt256) ⟨128⟩ = ⟨100⟩ by decide] at rd1001
  exact evm_run rd1001 with [raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem auctionSetReservePriceBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (_hcode : I.code = auctionBytecode)
    (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (_hsel : selIs I (auctionSelBytes 15))
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (auctionSelBytes 15) rfl _hsel
  have hdispatch := auctionDispatch_setReservePrice _hsel
  have hreach := auctionReachSetReservePriceBody (cA := cA) (gh := gh) (bl := bl)
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
          have hdecode := auctionDecode_setReservePrice (I := I) hsz36 hbig
          have hbody := auctionSetReservePriceBodyReturns evmS I
            (by simp only [evmS, initState]; exact hwv) hownerSolm
          have hpostAccounts :
              accountMapEquiv (auctionSetReservePricePostMap σ_evm I)
                (auctionSetReservePricePostState evmS I).accountMap := by
            simpa [auctionSetReservePricePostMap, auctionSetReservePricePostState, evmS, initState,
              storageStore_accountMap] using
              accountMapEquiv_sstoreAccountMap I.codeOwner ⟨204⟩
                (auctionSetReservePriceArgWord I) _hAccounts
          exact (auctionX_setReservePrice_success (g := Sat256.ofUInt256 g)
              _hperm hwv hsz36 _hsize hbig howner hreach)
            |>.reEquivExecutionGenAccountMapEquiv _hcode hdispatch hdecode hbody
              (by simp [auctionSetReservePricePostState, evmS, initState, storageStore_createdAccounts])
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
          have hdecode := auctionDecode_setReservePrice (I := I) hsz36 hbig
          have hbody := auctionSetReservePriceBodyReverts_owner evmS I
            (by simp only [evmS, initState]; exact hwv) hownerSolm
          exact (auctionX_setReservePrice_revert_owner (g := Sat256.ofUInt256 g)
              hwv hsz36 _hsize hbig howner hreach)
            |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
      · have hbigLe : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
        exact (auctionSetReservePriceX_decodeRevert_huge (g := Sat256.ofUInt256 g)
            hwv _hsize hbigLe hreach)
          |>.reEquivDecodingFailed _hcode hdispatch
            (auctionDecode_setReservePrice_none_huge (I := I) hbigLe)
    · have hshort : I.calldata.size < 36 := by omega
      exact (auctionSetReservePriceX_decodeRevert_short (g := Sat256.ofUInt256 g)
          hwv hsz4 _hsize hshort hreach)
        |>.reEquivDecodingFailed _hcode hdispatch
          (auctionDecode_setReservePrice_none_short (I := I) hshort)
  · by_cases hsz36 : 36 ≤ I.calldata.size
    · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
      · have hdecode := auctionDecode_setReservePrice (I := I) hsz36 hbig
        have hbody := auctionSetReservePriceBodyReverts_callvalue
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
          (by simpa only [initState] using hwv)
        exact (auctionX_setReservePrice_callvalue_ne hreach hwv)
          |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
      · have hbigLe : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
        exact (auctionX_setReservePrice_callvalue_ne hreach hwv)
          |>.reEquivDecodingFailed _hcode hdispatch
            (auctionDecode_setReservePrice_none_huge (I := I) hbigLe)
    · have hshort : I.calldata.size < 36 := by omega
      exact (auctionX_setReservePrice_callvalue_ne hreach hwv)
        |>.reEquivDecodingFailed _hcode hdispatch
          (auctionDecode_setReservePrice_none_short (I := I) hshort)

end Auction
