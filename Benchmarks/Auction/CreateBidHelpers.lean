import Benchmarks.Auction.SettleAuction

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

abbrev auctionCreateBidArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

def auctionCreateBidStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "nounId" (.int (Int.ofNat (auctionCreateBidArgWord I).toNat))

theorem auctionDispatch_createBid {I : ExecutionEnv} (hsel : selIs I (auctionSelBytes 6)) :
    dispatchMsg auctionContract I.calldata = some createBidTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [initializeTransition])
    (post := [settleAndCreateTransition, settleAuctionTransition, pauseTransition,
      unpauseTransition, setTimeBufferTransition, setReservePriceTransition,
      setMinBidIncTransition, transferOwnershipTransition, renounceOwnershipTransition,
      ownerGetter, pausedGetter, nounsGetter, wethGetter, timeBufferGetter, reservePriceGetter,
      minBidIncGetter, durationGetter, auctionGetter])
    (ti := createBidTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = auctionSelBytes 6 := (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl
    simp [selectorOf, initializeSelectorBytes, hcd, auctionSelBytes]
    native_decide
  · rw [selectorOf, createBidSelectorBytes]
    simpa [selIs, auctionSelBytes] using hsel

theorem auctionDecode_createBid {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (createBidTransition.params.map Param.name)
        (transitionSignature createBidTransition).paramTypes I.calldata =
      some (auctionCreateBidStore I) := by
  show decodeCalldata ["nounId"] [uint256] I.calldata =
    some (auctionCreateBidStore I)
  simpa [auctionCreateBidStore, auctionCreateBidArgWord, uint256, abiUInt256, calldataWord] using
    decodeCalldata_uint256_ok (cd := I.calldata) (x := "nounId") hsz36 hbig

theorem auctionDecode_createBid_none_short {I : ExecutionEnv}
    (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (createBidTransition.params.map Param.name)
        (transitionSignature createBidTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["nounId"] [uint256] I.calldata = none
  simpa [uint256, abiUInt256] using
    decodeCalldata_uint256_none_short (cd := I.calldata) (x := "nounId") hshort

theorem auctionDecode_createBid_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (createBidTransition.params.map Param.name)
        (transitionSignature createBidTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["nounId"] [uint256] I.calldata = none
  simpa [uint256, abiUInt256] using
    decodeCalldata_uint256_none_huge (cd := I.calldata) (x := "nounId") hbig

theorem auctionReachCreateBidBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = auctionBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (auctionSelBytes 6)) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨500⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsel' : ((⟨#[0x65, 0x9d, 0xd2, 0xb4]⟩ : ByteArray) ==
      I.calldata.extract 0 4) = true := by
    simpa [selIs, auctionSelBytes] using hsel
  have hword : auctionSelWord I = ⟨0x659dd2b4⟩ :=
    auctionSelWord_eq_of_beq I hsz 0x65 0x9d 0xd2 0xb4 ⟨0x659dd2b4⟩
      (by decide) hsel'
  obtain ⟨_, _, hsplit⟩ := auctionReachRootSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
  have hroot :
      UInt256.gt (armSelNat auctionBytecode auctionSplitPc) (auctionSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide
  have h157 := RD.selectorSplitTakenAuto hsplit auctionSplitWellFormed hroot
    (by jump_dest) (by simp)
  have h158 := h157.jumpdest (by decide) (by simp)
  have hlower :
      UInt256.gt (armSelNat auctionBytecode auctionLowerSplitPc) (auctionSelWord I) =
        ⟨0⟩ := by
    rw [hword]
    decide
  have h169 := RD.selectorSplitNotTakenAuto h158 auctionLowerSplitWellFormed hlower (by simp)
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat auctionBytecode
        (nthArmPc auctionBytecode auctionLowerMidFirstArmPc j)) (auctionSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    rw [hword]
    decide
  have htake :
      UInt256.eq
          (armSelNat auctionBytecode (nthArmPc auctionBytecode auctionLowerMidFirstArmPc 1))
          (auctionSelWord I) ≠
        ⟨0⟩ := by
    rw [hword]
    decide
  exact RD.dispatchTo (code := auctionBytecode) (ee := I) (g := g)
    (s0 := initState cA gh bl σ σ₀ g A I) (selWord := auctionSelWord I)
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (acc := (cA, σ)) ⟨500⟩ 1 h169
    (fun j hj => auctionLowerMidArmsWellFormed j (by omega)) heq0 htake
    (by jump_dest)
    (by native_decide)
    (by simp)

theorem auctionCreateBidX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨500⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5357⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨514⟩, ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd500⟩ := hreach
  exact ⟨_, _, evm_run rd500 with [
    jumpdest, push2 ⟨413⟩, push2 ⟨514⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨5357⟩, jump (by jump_dest)]⟩

theorem auctionCreateBidDecodeUint256Ok5357 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5357⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hsltval :
      UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨32⟩ =
        ⟨0⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD auctionBytecode ee g s0 ret (calldataWord ee.calldata 4 :: R)
      mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨5373⟩,
    jumpiT (by rw [hsltval]; decide) (by jump_dest),
    jumpdest, pop, calldataload, swap2, swap1, pop, jump hret]⟩

theorem auctionCreateBidDecodeUint256LenRevert5357 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5357⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hsltval :
      UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨32⟩ =
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

theorem auctionCreateBidX_decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨500⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1165⟩
      [auctionCreateBidArgWord I, ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
        ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  obtain ⟨_, _, rd5357⟩ := auctionCreateBidX_toDecoder (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hreach
  obtain ⟨_, _, rd514⟩ :=
    auctionCreateBidDecodeUint256Ok5357 (R := [⟨413⟩, sel]) rd5357 hslt
      (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa [auctionCreateBidArgWord, calldataWord] using
      evm_run rd514 with [jumpdest, push2 ⟨1165⟩, jump (by jump_dest)]⟩

theorem auctionCreateBidX_decodeRevert_short {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨500⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
        ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  obtain ⟨_, _, rd5357⟩ := auctionCreateBidX_toDecoder (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hreach
  exact auctionCreateBidDecodeUint256LenRevert5357 (R := [⟨413⟩, sel]) rd5357 hslt
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem auctionCreateBidX_decodeRevert_huge {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨500⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
        ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  obtain ⟨_, _, rd5357⟩ := auctionCreateBidX_toDecoder (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hreach
  exact auctionCreateBidDecodeUint256LenRevert5357 (R := [⟨413⟩, sel]) rd5357 hslt
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem evalExpr_createBid_entered (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionCreateBidStore I }
      evm entered =
      .ok (.int 2) := by
  simp [entered, evalExpr?, pure]

theorem auctionCreateBidStore_status_get? (I : ExecutionEnv) :
    (auctionCreateBidStore I).get? statusRef.base = none := by
  rw [auctionCreateBidStore, statusRef]
  change ((∅ : Store).insert "nounId"
      (.int (Int.ofNat (auctionCreateBidArgWord I).toNat)))[("_status" : String)]? = none
  rw [Std.HashMap.getElem?_insert]
  simp

theorem evalExpr_createBid_status (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionCreateBidStore I } evm
      (.storage statusRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩).toNat)) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := auctionCreateBidStore I }
      evm statusRef = .ok { base := "_status", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, statusRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_status", steps := [] } : EvaledStorageRef) =
        some (.elem (.int uint256Int)) := by
    decide
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := auctionCreateBidStore_status_get? I) (her := her) (hty := hty) (hloc := by rfl)]
  exact congrArg EvalResult.ok (by simpa using auctionStorageLocLoad_uint256 evm ⟨101⟩)

theorem evalExpr_createBid_status_ne_entered_false (evm : EVM.State) (I : ExecutionEnv)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ = ⟨2⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionCreateBidStore I } evm
      (.binary .ne (.storage statusRef) entered) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_createBid_status, evalExpr_createBid_entered,
    EvalResult.bind, bind, evalBinaryOp?]
  rw [hstatus]
  rfl

theorem evalExpr_createBid_status_ne_entered_true (evm : EVM.State) (I : ExecutionEnv)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionCreateBidStore I } evm
      (.binary .ne (.storage statusRef) entered) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_createBid_status, evalExpr_createBid_entered,
    EvalResult.bind, bind, evalBinaryOp?]
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩).toNat) ==
        Value.int 2) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    rw [Value.int.injEq] at h
    apply hstatus
    apply u256_inj
    change (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩).toNat =
      (⟨2⟩ : UInt256).toNat
    have hnat :
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩).toNat = 2 :=
      Int.ofNat.inj h
    simpa using hnat
  rw [hbeq]
  rfl

theorem auctionCreateBidTransitionReverts_statusEntered (evm : EVM.State) (I : ExecutionEnv)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ = ⟨2⟩) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionCreateBidStore I)
      createBidTransition.body .reverted := by
  dsimp [createBidTransition]
  refine ExecFuncBody.execBlockRevert ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_createBid_status_ne_entered_false evm I hstatus))

def auctionCreateBidReentrancyGuardReentrantStringWord : UInt256 :=
  ⟨0x5265656e7472616e637947756172643a207265656e7472616e742063616c6c00⟩

def auctionCreateBidEnterMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨101⟩ ⟨2⟩

def auctionCreateBidEnterState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩

theorem auctionCreateBidAssignStatusEntered (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidStore I } evm .storage
        statusRef (.int 2) =
      .ok ({ contract := auctionContract, locals := auctionCreateBidStore I },
        auctionCreateBidEnterState evm) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := auctionCreateBidStore I } evm
      statusRef = .ok { base := "_status", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, statusRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_status", steps := [] } : EvaledStorageRef) = some (.elem (.int uint256Int)) := by
    decide
  exact assignStorageRef_storage_scalar (cfg := auctionConfig)
    (solm := { contract := auctionContract, locals := auctionCreateBidStore I }) (evm := evm)
    (evm' := auctionCreateBidEnterState evm) (slot := statusRef)
    (er := { base := "_status", steps := [] }) (ty := .elem (.int uint256Int))
    (loc := auctionUint256Loc ⟨101⟩) (n := 2) (auctionCreateBidStore_status_get? I) her hty
    (by rfl)
    (by simpa [auctionCreateBidEnterState] using
      auctionStorageLocStore_uint256 evm ⟨101⟩ ⟨2⟩)

def auctionCreateBidSnapshotStore (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (auctionCreateBidStore I).insert "_auction" (auctionSettleAuctionSnapshotValue evm)

theorem auctionCreateBidSnapshotStore_nounId (evm : EVM.State) (I : ExecutionEnv) :
    (auctionCreateBidSnapshotStore evm I).get? "nounId" =
      some (.int (Int.ofNat (auctionCreateBidArgWord I).toNat)) := by
  rw [auctionCreateBidSnapshotStore]
  rw [store_get_ne _ _ (by decide)]
  rw [auctionCreateBidStore]
  exact store_get_self _ _ _

theorem evalExpr_createBid_snapshot (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionCreateBidStore I }
        evm (.storage auctionRef) =
      .ok (auctionSettleAuctionSnapshotValue evm) := by
  have hloadNoun : storageLocLoad evm (auctionUint256Loc ⟨207⟩) =
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩).toNat) := by
    simpa using auctionStorageLocLoad_uint256 evm ⟨207⟩
  have hloadAmount : storageLocLoad evm (auctionUint256Loc ⟨208⟩) =
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat) := by
    simpa using auctionStorageLocLoad_uint256 evm ⟨208⟩
  have hloadStart : storageLocLoad evm (auctionUint256Loc ⟨209⟩) =
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩).toNat) := by
    simpa using auctionStorageLocLoad_uint256 evm ⟨209⟩
  have hloadEnd : storageLocLoad evm (auctionUint256Loc ⟨210⟩) =
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat) := by
    simpa using auctionStorageLocLoad_uint256 evm ⟨210⟩
  have hloadBidder : storageLocLoad evm (auctionAddrLoc ⟨211⟩) =
      .address (AccountAddress.ofNat
        (auctionPackedBidderWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat) := by
    simpa [auctionPackedBidderWord] using
      auctionStorageLocLoad_address_offset0 evm ⟨211⟩
  have hloadSettled : storageLocLoad evm (auctionBoolLocAt ⟨211⟩ 20) =
      wordToElem .bool
        (auctionPackedSettledWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)) := by
    simpa [auctionPackedSettledWord, auctionPackedSettledBaseWord] using
      auctionStorageLocLoad_bool_offset evm ⟨211⟩ ⟨20, by decide⟩
  simp [evalExpr?, evalStorageRef, evalStorageRefSteps, auctionRef, auctionCreateBidStore,
    auctionConfig, resolveStorageRef?, storageTypeAt?, auctionContract, storageDecls,
    auctionStructTy, uint256St, addrSt, boolSt, readStorage?, readFields?,
    EvalResult.ofOption, EvalResult.bind, bind, pure, auctionSettleAuctionSnapshotValue,
    auctionSettleAuctionSnapshotFields, auctionStorageLayout, hloadNoun, hloadAmount,
    hloadStart, hloadEnd, hloadBidder, hloadSettled]

theorem evalExpr_createBid_snapshot_nounId (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidSnapshotStore evm I }
        evm (.var "nounId") =
      .ok (.int (Int.ofNat (auctionCreateBidArgWord I).toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [auctionCreateBidSnapshotStore_nounId]

theorem evalExpr_createBid_mem_nounId (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidSnapshotStore evm I }
        evm (auctionMemField "nounId") =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩).toNat)) := by
  simp [auctionMemField, auctionCreateBidSnapshotStore, auctionSettleAuctionSnapshotValue,
    auctionSettleAuctionSnapshotFields, evalExpr?, EvalResult.ofOption, lookupField?,
    lookupAssoc, EvalResult.bind, bind]

theorem evalExpr_createBid_mem_endTime (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidSnapshotStore evm I }
        evm (auctionMemField "endTime") =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat)) := by
  simp [auctionMemField, auctionCreateBidSnapshotStore, auctionSettleAuctionSnapshotValue,
    auctionSettleAuctionSnapshotFields, evalExpr?, EvalResult.ofOption, lookupField?,
    lookupAssoc, EvalResult.bind, bind]

theorem evalExpr_createBid_noun_eq_false (evm : EVM.State) (I : ExecutionEnv)
    (hnoun : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩ ≠
      auctionCreateBidArgWord I) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidSnapshotStore evm I }
        evm (.binary .eq (auctionMemField "nounId") (.var "nounId")) =
      .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_createBid_mem_nounId, evalExpr_createBid_snapshot_nounId,
    EvalResult.bind, bind, evalBinaryOp?]
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩).toNat) ==
        Value.int (Int.ofNat (auctionCreateBidArgWord I).toNat)) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    rw [Value.int.injEq] at h
    apply hnoun
    apply u256_inj
    exact Int.ofNat.inj h
  rw [hbeq]

theorem evalExpr_createBid_noun_eq_true (evm : EVM.State) (I : ExecutionEnv)
    (hnoun : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩ =
      auctionCreateBidArgWord I) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidSnapshotStore evm I }
        evm (.binary .eq (auctionMemField "nounId") (.var "nounId")) =
      .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_createBid_mem_nounId, evalExpr_createBid_snapshot_nounId,
    EvalResult.bind, bind, evalBinaryOp?]
  rw [hnoun]
  simp [BEq.beq]

theorem evalExpr_createBid_time_lt_false (evm : EVM.State) (I : ExecutionEnv)
    (htime : ¬ (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidSnapshotStore evm I }
        evm (.binary .lt now (auctionMemField "endTime")) =
      .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_settleAuction_now, evalExpr_createBid_mem_endTime,
    EvalResult.bind, bind, evalBinaryOp?]
  norm_num
  exact Nat.le_of_not_gt htime

theorem evalExpr_createBid_time_lt_true (evm : EVM.State) (I : ExecutionEnv)
    (htime : (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidSnapshotStore evm I }
        evm (.binary .lt now (auctionMemField "endTime")) =
      .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_settleAuction_now, evalExpr_createBid_mem_endTime,
    EvalResult.bind, bind, evalBinaryOp?]
  norm_num
  exact htime

theorem auctionCreateBidSnapshotStore_reservePrice_get? (evm : EVM.State) (I : ExecutionEnv) :
    (auctionCreateBidSnapshotStore evm I).get? reservePriceRef.base = none := by
  rw [auctionCreateBidSnapshotStore, auctionCreateBidStore, reservePriceRef]
  change ((((∅ : Store).insert "nounId"
          (.int (Int.ofNat (auctionCreateBidArgWord I).toNat))).insert "_auction"
        (auctionSettleAuctionSnapshotValue evm))[("reservePrice" : String)]?) = none
  rw [Std.HashMap.getElem?_insert]
  simp

theorem evalExpr_createBid_callvalue (evm : EVM.State) (locals : Store) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
        (.env .callvalue) =
      .ok (.int (Int.ofNat evm.executionEnv.weiValue.toNat)) := by
  simp [evalExpr?, envValue, pure, UInt256.toNat]

theorem evalExpr_createBid_reservePrice (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidSnapshotStore evm I }
        evm (.storage reservePriceRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨204⟩).toNat)) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := auctionCreateBidSnapshotStore evm I }
      evm reservePriceRef = .ok { base := "reservePrice", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, reservePriceRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "reservePrice", steps := [] } : EvaledStorageRef) =
        some (.elem (.int uint256Int)) := by
    decide
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := auctionCreateBidSnapshotStore_reservePrice_get? evm I) (her := her)
    (hty := hty) (hloc := by rfl)]
  exact congrArg EvalResult.ok (by simpa using auctionStorageLocLoad_uint256 evm ⟨204⟩)

theorem evalExpr_createBid_reserve_ge_false (evm : EVM.State) (I : ExecutionEnv)
    (hreserve : evm.executionEnv.weiValue.toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨204⟩).toNat) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidSnapshotStore evm I }
        evm (.binary .ge (.env .callvalue) (.storage reservePriceRef)) =
      .ok (.bool false) := by
  simp [evalExpr?, evalExpr_createBid_callvalue, evalExpr_createBid_reservePrice,
    EvalResult.bind, bind, evalBinaryOp?]
  exact_mod_cast hreserve

theorem evalExpr_createBid_reserve_ge_true (evm : EVM.State) (I : ExecutionEnv)
    (hreserve : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨204⟩).toNat ≤
      evm.executionEnv.weiValue.toNat) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidSnapshotStore evm I }
        evm (.binary .ge (.env .callvalue) (.storage reservePriceRef)) =
      .ok (.bool true) := by
  simp [evalExpr?, evalExpr_createBid_callvalue, evalExpr_createBid_reservePrice,
    EvalResult.bind, bind, evalBinaryOp?]
  exact_mod_cast hreserve

theorem auctionCreateBidSnapshotStore_minBid_get? (evm : EVM.State) (I : ExecutionEnv) :
    (auctionCreateBidSnapshotStore evm I).get? minBidIncRef.base = none := by
  rw [auctionCreateBidSnapshotStore, auctionCreateBidStore, minBidIncRef]
  change ((((∅ : Store).insert "nounId"
          (.int (Int.ofNat (auctionCreateBidArgWord I).toNat))).insert "_auction"
        (auctionSettleAuctionSnapshotValue evm))[("minBidIncrementPercentage" : String)]?) = none
  rw [Std.HashMap.getElem?_insert]
  simp

theorem evalExpr_createBid_mem_amount (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidSnapshotStore evm I }
        evm (auctionMemField "amount") =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat)) := by
  simp [auctionMemField, auctionCreateBidSnapshotStore, auctionSettleAuctionSnapshotValue,
    auctionSettleAuctionSnapshotFields, evalExpr?, EvalResult.ofOption, lookupField?,
    lookupAssoc, EvalResult.bind, bind]

theorem evalExpr_createBid_minBid (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidSnapshotStore evm I }
        evm (.storage minBidIncRef) =
      .ok (.int (Int.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨205⟩)
          ⟨255⟩).toNat)) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := auctionCreateBidSnapshotStore evm I }
      evm minBidIncRef =
        .ok { base := "minBidIncrementPercentage", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, minBidIncRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "minBidIncrementPercentage", steps := [] } : EvaledStorageRef) =
        some (.elem (.int uint8Int)) := by
    decide
  rw [evalExpr_storage_scalar (t := .int uint8Int)
    (hbase := auctionCreateBidSnapshotStore_minBid_get? evm I) (her := her)
    (hty := hty) (hloc := by rfl)]
  exact congrArg EvalResult.ok (by
    simpa [auctionUint8LocAt, auctionUint8Loc] using auctionStorageLocLoad_uint8 evm ⟨205⟩)

theorem evalExpr_createBid_minBidMul_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat *
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨205⟩)
          ⟨255⟩).toNat) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidSnapshotStore evm I }
        evm (u256 (.binary .mul (auctionMemField "amount") (.storage minBidIncRef))) =
      .revert := by
  simp only [u256, evalExpr?, evalExpr_createBid_mem_amount, evalExpr_createBid_minBid,
    EvalResult.bind, bind, evalBinaryOp?]
  simp [uint256Int]
  intro _
  exact Int.ofNat_le.mpr (by simpa [UInt256.size] using hover)

theorem evalExpr_createBid_minBidRhs_revert_mulOverflow (evm : EVM.State)
    (I : ExecutionEnv)
    (hover : UInt256.size ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat *
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨205⟩)
          ⟨255⟩).toNat) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidSnapshotStore evm I }
        evm
        (u256 (.binary .add (auctionMemField "amount")
          (.binary .div (u256 (.binary .mul (auctionMemField "amount")
            (.storage minBidIncRef))) (.intLit 100)))) =
      .revert := by
  simp only [u256, evalExpr?, evalExpr_createBid_mem_amount, evalExpr_createBid_minBid,
    EvalResult.bind, bind, evalBinaryOp?]
  simp [uint256Int]
  rw [if_pos (by
    right
    exact Int.ofNat_le.mpr (by simpa [UInt256.size] using hover))]

theorem evalExpr_createBid_minBidGuard_revert_mulOverflow (evm : EVM.State)
    (I : ExecutionEnv)
    (hover : UInt256.size ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat *
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨205⟩)
          ⟨255⟩).toNat) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidSnapshotStore evm I }
        evm
        (.binary .ge (.env .callvalue)
          (u256 (.binary .add (auctionMemField "amount")
            (.binary .div (u256 (.binary .mul (auctionMemField "amount")
              (.storage minBidIncRef))) (.intLit 100))))) =
      .revert := by
  simp only [evalExpr?, evalExpr_createBid_callvalue,
    evalExpr_createBid_minBidRhs_revert_mulOverflow evm I hover, EvalResult.bind, bind]

theorem auctionCreateBidTransitionReverts_nounMismatch (evm : EVM.State) (I : ExecutionEnv)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hnoun :
      Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨207⟩ ≠
        auctionCreateBidArgWord I) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionCreateBidStore I)
      createBidTransition.body .reverted := by
  dsimp [createBidTransition]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_status_ne_entered_true evm I hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_entered evm I)
      (auctionCreateBidAssignStatusEntered evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_snapshot (auctionCreateBidEnterState evm) I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (evalExpr_createBid_noun_eq_false (auctionCreateBidEnterState evm) I hnoun))

theorem auctionCreateBidTransitionReverts_expired (evm : EVM.State) (I : ExecutionEnv)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hnoun :
      Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨207⟩ =
        auctionCreateBidArgWord I)
    (htime : ¬ (UInt256.ofNat (auctionCreateBidEnterState evm).executionEnv.header.timestamp).toNat <
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩).toNat) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionCreateBidStore I)
      createBidTransition.body .reverted := by
  dsimp [createBidTransition]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_status_ne_entered_true evm I hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_entered evm I)
      (auctionCreateBidAssignStatusEntered evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_snapshot (auctionCreateBidEnterState evm) I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_createBid_noun_eq_true (auctionCreateBidEnterState evm) I hnoun)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (evalExpr_createBid_time_lt_false (auctionCreateBidEnterState evm) I htime))

theorem auctionCreateBidTransitionReverts_belowReserve (evm : EVM.State) (I : ExecutionEnv)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hnoun :
      Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨207⟩ =
        auctionCreateBidArgWord I)
    (htime : (UInt256.ofNat
        (auctionCreateBidEnterState evm).executionEnv.header.timestamp).toNat <
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩).toNat)
    (hreserve : (auctionCreateBidEnterState evm).executionEnv.weiValue.toNat <
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨204⟩).toNat) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionCreateBidStore I)
      createBidTransition.body .reverted := by
  dsimp [createBidTransition]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_status_ne_entered_true evm I hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_entered evm I)
      (auctionCreateBidAssignStatusEntered evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_snapshot (auctionCreateBidEnterState evm) I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_createBid_noun_eq_true (auctionCreateBidEnterState evm) I hnoun)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_createBid_time_lt_true (auctionCreateBidEnterState evm) I htime)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (evalExpr_createBid_reserve_ge_false (auctionCreateBidEnterState evm) I hreserve))

theorem auctionCreateBidTransitionReverts_minBidMulOverflow (evm : EVM.State)
    (I : ExecutionEnv)
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
    (hover : UInt256.size ≤
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
        (UInt256.land
          (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
          ⟨255⟩).toNat) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionCreateBidStore I)
      createBidTransition.body .reverted := by
  dsimp [createBidTransition]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_status_ne_entered_true evm I hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_entered evm I)
      (auctionCreateBidAssignStatusEntered evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_snapshot (auctionCreateBidEnterState evm) I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_createBid_noun_eq_true (auctionCreateBidEnterState evm) I hnoun)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_createBid_time_lt_true (auctionCreateBidEnterState evm) I htime)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_createBid_reserve_ge_true (auctionCreateBidEnterState evm) I hreserve)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireRevert
      (evalExpr_createBid_minBidGuard_revert_mulOverflow
        (auctionCreateBidEnterState evm) I hover))

theorem auctionCreateBidX_revert_statusEntered {cA gh bl σ σ₀ A I} {g : Sat256}
    (hstatus : auctionSlotWord ⟨101⟩ σ I = ⟨2⟩)
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1165⟩
      [auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1165⟩ := hreach
  have rd1170₀ := evm_run rd1165 with [jumpdest, push1 ⟨2⟩, push1 ⟨101⟩]
  obtain ⟨_, _, rd1170₁⟩ := rd1170₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1171⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1171⟩
      (auctionSlotWord ⟨101⟩ σ I :: ⟨2⟩ :: auctionCreateBidArgWord I :: ⟨413⟩ ::
        auctionSelWord I :: [])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd1170₁⟩
  have rd1172 := evm_run rd1171 with [sub]
  have hcond : UInt256.sub (auctionSlotWord ⟨101⟩ σ I) ⟨2⟩ = ⟨0⟩ := by
    rw [hstatus]
    decide
  have rd1179 := evm_run rd1172 with [
    push2 ⟨1199⟩, jumpiNT hcond,
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov)]
  have rd1183 := rd1179.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd1191 := evm_run rd1183 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 6 (solcErrorStringMem0 solcFreePtrMem) (UInt256.ofNat 5)
      (by decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨4⟩, add]
  obtain ⟨_, _, rd1191'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1191⟩
      [((⟨4⟩ : UInt256) + ⟨128⟩), auctionCreateBidArgWord I, ⟨413⟩,
        auctionSelWord I]
      (solcErrorStringMem0 solcFreePtrMem) (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C := by
    exact ⟨_, _, by simpa using rd1191⟩
  have rd5575 := evm_run rd1191' with [
    push2 ⟨994⟩, swap1, push2 ⟨5575⟩, jump (by jump_dest)]
  have rd5587 := evm_run rd5575 with [
    jumpdest, push1 ⟨32⟩, dup1, dup3,
    raw mstore 3 (solcErrorStringMem1 solcFreePtrMem) (UInt256.ofNat 6)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨31⟩, swap1, dup3, add,
    raw mstore 3 (solcErrorStringMem2 ⟨31⟩ solcFreePtrMem) (UInt256.ofNat 7)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd5620 := rd5587.pushConst auctionCreateBidReentrancyGuardReentrantStringWord
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd5629₀ := evm_run rd5620 with [
    push1 ⟨64⟩, dup3, add,
    raw mstore 3
      (solcErrorStringMem3 ⟨31⟩ auctionCreateBidReentrancyGuardReentrantStringWord
        solcFreePtrMem)
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
      (solcErrorStringMem3_mload64 ⟨31⟩ auctionCreateBidReentrancyGuardReentrantStringWord
        solcFreePtrMem_size solcFreePtrMem_read64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd1001 := rd1001₀
  rw [show UInt256.sub (⟨228⟩ : UInt256) ⟨128⟩ = ⟨100⟩ by decide] at rd1001
  exact evm_run rd1001 with [raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem auctionCreateBidX_toStatusOpen {cA gh bl σ σ₀ A I} {g : Sat256}
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1165⟩
      [auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1199⟩
      [auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1165⟩ := hreach
  have rd1170₀ := evm_run rd1165 with [jumpdest, push1 ⟨2⟩, push1 ⟨101⟩]
  obtain ⟨_, _, rd1170₁⟩ := rd1170₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1171⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1171⟩
      (auctionSlotWord ⟨101⟩ σ I :: ⟨2⟩ :: auctionCreateBidArgWord I :: ⟨413⟩ ::
        auctionSelWord I :: [])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd1170₁⟩
  have rd1172 := evm_run rd1171 with [sub]
  have hcond : UInt256.sub (auctionSlotWord ⟨101⟩ σ I) ⟨2⟩ ≠ ⟨0⟩ :=
    u256_sub_ne_zero_of_ne hstatus
  exact ⟨_, _, evm_run rd1172 with [push2 ⟨1199⟩, jumpiT hcond (by jump_dest)]⟩

theorem auctionCreateBidX_toEntered {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1165⟩
      [auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1205⟩
      [auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionCreateBidEnterMap σ I) k C := by
  obtain ⟨_, _, rd1199⟩ := auctionCreateBidX_toStatusOpen hstatus hreach
  have rd1204 := evm_run rd1199 with [jumpdest, push1 ⟨2⟩, push1 ⟨101⟩]
  obtain ⟨_, _, rd1205₀⟩ := rd1204.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, by simpa [auctionCreateBidEnterMap] using rd1205₀⟩

theorem auctionCreateBidX_toSnapshotCheck {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1165⟩
      [auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1282⟩
      [⟨128⟩, auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I,
        auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem
        (auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionStartWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I)
        (auctionPackedBidderWord (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I))
        (auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I)))
      (UInt256.ofNat 10) ByteArray.empty (cA, auctionCreateBidEnterMap σ I) k C := by
  let σ1 := auctionCreateBidEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  obtain ⟨_, _, rd1205⟩ := auctionCreateBidX_toEntered
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm hstatus hreach
  have rd1215 := evm_run rd1205 with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push1 ⟨192⟩, dup2, add, dup3,
    raw mstore 0 auctionSettleAuctionSnapshotFreeMem (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  obtain ⟨_, _, rd1218₀⟩ := (evm_run rd1215 with [push1 ⟨207⟩]).sload
    (by decide) (by evm_ov)
  obtain ⟨_, _, rd1218⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1218⟩
      (noun :: ⟨128⟩ :: ⟨64⟩ :: auctionCreateBidArgWord I :: ⟨413⟩ ::
        auctionSelWord I :: [])
      auctionSettleAuctionSnapshotFreeMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ1) k C := by
    exact ⟨_, _, by simpa [noun, auctionAuctionNounWord, auctionSlotWord, σ1] using rd1218₀⟩
  have rd1221 := evm_run rd1218 with [
    dup1, dup3,
    raw mstore 6 (auctionSettleAuctionSnapshotNounMem noun) (UInt256.ofNat 5)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  obtain ⟨_, _, rd1224₀⟩ := (evm_run rd1221 with [push1 ⟨208⟩]).sload
    (by decide) (by evm_ov)
  obtain ⟨_, _, rd1224⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1224⟩
      (amount :: noun :: ⟨128⟩ :: ⟨64⟩ :: auctionCreateBidArgWord I :: ⟨413⟩ ::
        auctionSelWord I :: [])
      (auctionSettleAuctionSnapshotNounMem noun) (UInt256.ofNat 5) ByteArray.empty
      (cA, σ1) k C := by
    exact ⟨_, _, by simpa [amount, auctionAuctionAmountWord, auctionSlotWord, σ1] using rd1224₀⟩
  have rd1229 := evm_run rd1224 with [
    push1 ⟨32⟩, dup4, add,
    raw mstore 3 (auctionSettleAuctionSnapshotAmountMem noun amount) (UInt256.ofNat 6)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  obtain ⟨_, _, rd1232₀⟩ := (evm_run rd1229 with [push1 ⟨209⟩]).sload
    (by decide) (by evm_ov)
  obtain ⟨_, _, rd1232⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1232⟩
      (start :: noun :: ⟨128⟩ :: ⟨64⟩ :: auctionCreateBidArgWord I :: ⟨413⟩ ::
        auctionSelWord I :: [])
      (auctionSettleAuctionSnapshotAmountMem noun amount) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by simpa [start, auctionAuctionStartWord, auctionSlotWord, σ1] using rd1232₀⟩
  have rd1239 := evm_run rd1232 with [
    swap3, dup3, add, swap3, swap1, swap3,
    raw mstore 3 (auctionSettleAuctionSnapshotStartMem noun amount start)
      (UInt256.ofNat 7) (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  obtain ⟨_, _, rd1242₀⟩ := (evm_run rd1239 with [push1 ⟨210⟩]).sload
    (by decide) (by evm_ov)
  obtain ⟨_, _, rd1242⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1242⟩
      (finish :: ⟨128⟩ :: noun :: auctionCreateBidArgWord I :: ⟨413⟩ ::
        auctionSelWord I :: [])
      (auctionSettleAuctionSnapshotStartMem noun amount start) (UInt256.ofNat 7)
      ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by simpa [finish, auctionAuctionEndWord, auctionSlotWord, σ1] using rd1242₀⟩
  have rd1247 := evm_run rd1242 with [
    push1 ⟨96⟩, dup3, add,
    raw mstore 3 (auctionSettleAuctionSnapshotEndMem noun amount start finish)
      (UInt256.ofNat 8) (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  obtain ⟨_, _, rd1250₀⟩ := (evm_run rd1247 with [push1 ⟨211⟩]).sload
    (by decide) (by evm_ov)
  obtain ⟨_, _, rd1250⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1250⟩
      (packed :: ⟨128⟩ :: noun :: auctionCreateBidArgWord I :: ⟨413⟩ ::
        auctionSelWord I :: [])
      (auctionSettleAuctionSnapshotEndMem noun amount start finish) (UInt256.ofNat 8)
      ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by simpa [packed, auctionAuctionPackedWord, auctionSlotWord, σ1] using rd1250₀⟩
  have rd1264 := evm_run rd1250 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and,
    push1 ⟨128⟩, dup4, add]
  have rd1265 := evm_run rd1264 with [
    raw mstore 3 (auctionSettleAuctionSnapshotBidderMem noun amount start finish bidder)
      (UInt256.ofNat 9) (by decide) mem_cost
      (by
        dsimp [bidder, auctionPackedBidderWord]
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask by native_decide]
        rw [show ((⟨128⟩ : UInt256) + ⟨128⟩).toNat = 256 by decide]
        rfl)
      (by decide) (by evm_ov)]
  have rd1282 := evm_run rd1265 with [
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
    simpa [σ1, noun, amount, start, finish, packed, bidder, settled] using rd1282⟩

def auctionCreateBidNounNotUpStringWord : UInt256 :=
  ⟨0x4e6f756e206e6f7420757020666f722061756374696f6e000000000000000000⟩

noncomputable def auctionCreateBidNounNotUpMem2
    (noun amount start finish bidder settled : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨23⟩ : UInt256)).write 0
    (auctionAuctionHasntStartedMem1 noun amount start finish bidder settled) 356 32

noncomputable def auctionCreateBidNounNotUpMem3
    (noun amount start finish bidder settled : UInt256) : ByteArray :=
  (UInt256.toByteArray auctionCreateBidNounNotUpStringWord).write 0
    (auctionCreateBidNounNotUpMem2 noun amount start finish bidder settled) 388 32

theorem auctionCreateBidNounNotUpMem2_size
    (noun amount start finish bidder settled : UInt256) :
    (auctionCreateBidNounNotUpMem2 noun amount start finish bidder settled).size = 388 := by
  unfold auctionCreateBidNounNotUpMem2
  exact toByteArray_write32_size_of_ge
    (auctionAuctionHasntStartedMem1 noun amount start finish bidder settled)
    (⟨23⟩ : UInt256) 356 356 388
    (auctionAuctionHasntStartedMem1_size noun amount start finish bidder settled)
    (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionCreateBidNounNotUpMem3_size
    (noun amount start finish bidder settled : UInt256) :
    (auctionCreateBidNounNotUpMem3 noun amount start finish bidder settled).size = 420 := by
  unfold auctionCreateBidNounNotUpMem3
  exact toByteArray_write32_size_of_ge
    (auctionCreateBidNounNotUpMem2 noun amount start finish bidder settled)
    auctionCreateBidNounNotUpStringWord 388 388 420
    (auctionCreateBidNounNotUpMem2_size noun amount start finish bidder settled)
    (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionCreateBidNounNotUpMem3_read64
    (noun amount start finish bidder settled : UInt256) :
    (auctionCreateBidNounNotUpMem3 noun amount start finish bidder settled).readWithPadding
        64 32 =
      UInt256.toByteArray (⟨320⟩ : UInt256) := by
  unfold auctionCreateBidNounNotUpMem3
  rw [toByteArray_write_read_below_of_gap auctionCreateBidNounNotUpStringWord _ 388 64
    (by rw [auctionCreateBidNounNotUpMem2_size]; omega) (by omega)
    (by rw [auctionCreateBidNounNotUpMem2_size]; exact lt_usize _ (by norm_num))]
  unfold auctionCreateBidNounNotUpMem2
  rw [toByteArray_write_read_below_of_gap (⟨23⟩ : UInt256) _ 356 64
    (by rw [auctionAuctionHasntStartedMem1_size]; omega) (by omega)
    (by rw [auctionAuctionHasntStartedMem1_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionHasntStartedMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 324 64
    (by rw [auctionAuctionHasntStartedMem0_size]; omega) (by omega)
    (by rw [auctionAuctionHasntStartedMem0_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionHasntStartedMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 320 64
    (by rw [auctionSettleAuctionSnapshotMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotMem_size]; exact lt_usize _ (by norm_num))]
  exact auctionSettleAuctionSnapshotMem_read64 noun amount start finish bidder settled

theorem auctionCreateBidNounNotUpMem3_mload64
    (noun amount start finish bidder settled : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (auctionCreateBidNounNotUpMem3 noun amount start finish bidder settled).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 14 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionCreateBidNounNotUpMem3 noun amount start finish bidder settled)
            |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨320⟩ :=
  mload64_of_readWithPadding_of_aw
    (by rw [auctionCreateBidNounNotUpMem3_size]; decide)
    (auctionCreateBidNounNotUpMem3_read64 noun amount start finish bidder settled)
    (by decide) (by decide)

def auctionCreateBidAuctionExpiredRawStringWord : UInt256 :=
  ⟨0x105d58dd1a5bdb88195e1c1a5c9959⟩

def auctionCreateBidAuctionExpiredStringWord : UInt256 :=
  ⟨0x41756374696f6e20657870697265640000000000000000000000000000000000⟩

noncomputable def auctionCreateBidAuctionExpiredMem2
    (noun amount start finish bidder settled : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨15⟩ : UInt256)).write 0
    (auctionAuctionHasntStartedMem1 noun amount start finish bidder settled) 356 32

noncomputable def auctionCreateBidAuctionExpiredMem3
    (noun amount start finish bidder settled : UInt256) : ByteArray :=
  (UInt256.toByteArray auctionCreateBidAuctionExpiredStringWord).write 0
    (auctionCreateBidAuctionExpiredMem2 noun amount start finish bidder settled) 388 32

theorem auctionCreateBidAuctionExpiredMem2_size
    (noun amount start finish bidder settled : UInt256) :
    (auctionCreateBidAuctionExpiredMem2 noun amount start finish bidder settled).size = 388 := by
  unfold auctionCreateBidAuctionExpiredMem2
  exact toByteArray_write32_size_of_ge
    (auctionAuctionHasntStartedMem1 noun amount start finish bidder settled)
    (⟨15⟩ : UInt256) 356 356 388
    (auctionAuctionHasntStartedMem1_size noun amount start finish bidder settled)
    (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionCreateBidAuctionExpiredMem3_size
    (noun amount start finish bidder settled : UInt256) :
    (auctionCreateBidAuctionExpiredMem3 noun amount start finish bidder settled).size = 420 := by
  unfold auctionCreateBidAuctionExpiredMem3
  exact toByteArray_write32_size_of_ge
    (auctionCreateBidAuctionExpiredMem2 noun amount start finish bidder settled)
    auctionCreateBidAuctionExpiredStringWord 388 388 420
    (auctionCreateBidAuctionExpiredMem2_size noun amount start finish bidder settled)
    (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionCreateBidAuctionExpiredMem3_read64
    (noun amount start finish bidder settled : UInt256) :
    (auctionCreateBidAuctionExpiredMem3 noun amount start finish bidder settled).readWithPadding
        64 32 =
      UInt256.toByteArray (⟨320⟩ : UInt256) := by
  unfold auctionCreateBidAuctionExpiredMem3
  rw [toByteArray_write_read_below_of_gap auctionCreateBidAuctionExpiredStringWord _ 388 64
    (by rw [auctionCreateBidAuctionExpiredMem2_size]; omega) (by omega)
    (by rw [auctionCreateBidAuctionExpiredMem2_size]; exact lt_usize _ (by norm_num))]
  unfold auctionCreateBidAuctionExpiredMem2
  rw [toByteArray_write_read_below_of_gap (⟨15⟩ : UInt256) _ 356 64
    (by rw [auctionAuctionHasntStartedMem1_size]; omega) (by omega)
    (by rw [auctionAuctionHasntStartedMem1_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionHasntStartedMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 324 64
    (by rw [auctionAuctionHasntStartedMem0_size]; omega) (by omega)
    (by rw [auctionAuctionHasntStartedMem0_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionHasntStartedMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 320 64
    (by rw [auctionSettleAuctionSnapshotMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotMem_size]; exact lt_usize _ (by norm_num))]
  exact auctionSettleAuctionSnapshotMem_read64 noun amount start finish bidder settled

theorem auctionCreateBidAuctionExpiredMem3_mload64
    (noun amount start finish bidder settled : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (auctionCreateBidAuctionExpiredMem3 noun amount start finish bidder settled).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 14 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionCreateBidAuctionExpiredMem3 noun amount start finish bidder settled)
            |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨320⟩ :=
  mload64_of_readWithPadding_of_aw
    (by rw [auctionCreateBidAuctionExpiredMem3_size]; decide)
    (auctionCreateBidAuctionExpiredMem3_read64 noun amount start finish bidder settled)
    (by decide) (by decide)

def auctionCreateBidReservePriceStringWord : UInt256 :=
  ⟨0x4d7573742073656e64206174206c656173742072657365727665507269636500⟩

noncomputable def auctionCreateBidReservePriceMem2
    (noun amount start finish bidder settled : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨31⟩ : UInt256)).write 0
    (auctionAuctionHasntStartedMem1 noun amount start finish bidder settled) 356 32

noncomputable def auctionCreateBidReservePriceMem3
    (noun amount start finish bidder settled : UInt256) : ByteArray :=
  (UInt256.toByteArray auctionCreateBidReservePriceStringWord).write 0
    (auctionCreateBidReservePriceMem2 noun amount start finish bidder settled) 388 32

theorem auctionCreateBidReservePriceMem2_size
    (noun amount start finish bidder settled : UInt256) :
    (auctionCreateBidReservePriceMem2 noun amount start finish bidder settled).size = 388 := by
  unfold auctionCreateBidReservePriceMem2
  exact toByteArray_write32_size_of_ge
    (auctionAuctionHasntStartedMem1 noun amount start finish bidder settled)
    (⟨31⟩ : UInt256) 356 356 388
    (auctionAuctionHasntStartedMem1_size noun amount start finish bidder settled)
    (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionCreateBidReservePriceMem3_size
    (noun amount start finish bidder settled : UInt256) :
    (auctionCreateBidReservePriceMem3 noun amount start finish bidder settled).size = 420 := by
  unfold auctionCreateBidReservePriceMem3
  exact toByteArray_write32_size_of_ge
    (auctionCreateBidReservePriceMem2 noun amount start finish bidder settled)
    auctionCreateBidReservePriceStringWord 388 388 420
    (auctionCreateBidReservePriceMem2_size noun amount start finish bidder settled)
    (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionCreateBidReservePriceMem3_read64
    (noun amount start finish bidder settled : UInt256) :
    (auctionCreateBidReservePriceMem3 noun amount start finish bidder settled).readWithPadding
        64 32 =
      UInt256.toByteArray (⟨320⟩ : UInt256) := by
  unfold auctionCreateBidReservePriceMem3
  rw [toByteArray_write_read_below_of_gap auctionCreateBidReservePriceStringWord _ 388 64
    (by rw [auctionCreateBidReservePriceMem2_size]; omega) (by omega)
    (by rw [auctionCreateBidReservePriceMem2_size]; exact lt_usize _ (by norm_num))]
  unfold auctionCreateBidReservePriceMem2
  rw [toByteArray_write_read_below_of_gap (⟨31⟩ : UInt256) _ 356 64
    (by rw [auctionAuctionHasntStartedMem1_size]; omega) (by omega)
    (by rw [auctionAuctionHasntStartedMem1_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionHasntStartedMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 324 64
    (by rw [auctionAuctionHasntStartedMem0_size]; omega) (by omega)
    (by rw [auctionAuctionHasntStartedMem0_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionHasntStartedMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 320 64
    (by rw [auctionSettleAuctionSnapshotMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotMem_size]; exact lt_usize _ (by norm_num))]
  exact auctionSettleAuctionSnapshotMem_read64 noun amount start finish bidder settled

theorem auctionCreateBidReservePriceMem3_mload64
    (noun amount start finish bidder settled : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (auctionCreateBidReservePriceMem3 noun amount start finish bidder settled).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 14 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionCreateBidReservePriceMem3 noun amount start finish bidder settled)
            |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨320⟩ :=
  mload64_of_readWithPadding_of_aw
    (by rw [auctionCreateBidReservePriceMem3_size]; decide)
    (auctionCreateBidReservePriceMem3_read64 noun amount start finish bidder settled)
    (by decide) (by decide)

theorem auctionSettleAuctionSnapshotMem_read160_word
    (noun amount start finish bidder settled : UInt256) :
    (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled).readWithPadding
        160 32 =
      UInt256.toByteArray amount := by
  unfold auctionSettleAuctionSnapshotMem
  rw [toByteArray_write_read_below_of_gap settled _ 288 160
    (by rw [auctionSettleAuctionSnapshotBidderMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotBidderMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionSettleAuctionSnapshotBidderMem
  rw [toByteArray_write_read_below_of_gap bidder _ 256 160
    (by rw [auctionSettleAuctionSnapshotEndMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotEndMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionSettleAuctionSnapshotEndMem
  rw [toByteArray_write_read_below_of_gap finish _ 224 160
    (by rw [auctionSettleAuctionSnapshotStartMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotStartMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionSettleAuctionSnapshotStartMem
  rw [toByteArray_write_read_below_of_gap start _ 192 160
    (by rw [auctionSettleAuctionSnapshotAmountMem_size]) (by omega)
    (by rw [auctionSettleAuctionSnapshotAmountMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionSettleAuctionSnapshotAmountMem
  exact toByteArray_write_read_back_of_gap amount
    (auctionSettleAuctionSnapshotNounMem noun) 160
    (by rw [auctionSettleAuctionSnapshotNounMem_size]; exact lt_usize _ (by norm_num))

theorem auctionSettleAuctionSnapshotMem_mload160
    (noun amount start finish bidder settled : UInt256) :
    (if (⟨160⟩ : UInt256).toNat ≥
          (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled).size
        ∨ (⟨160⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
            |>.readWithPadding (⟨160⟩ : UInt256).toNat 32))) =
      amount :=
  mloadWordValue_of_readWithPadding
    (by rw [auctionSettleAuctionSnapshotMem_size]; decide)
    (by decide)
    (auctionSettleAuctionSnapshotMem_read160_word noun amount start finish bidder settled)

-- LIBRARY CANDIDATE: checked-multiplication overflow implies the solc mul/div check fails.
theorem auctionCreateBid_mul_div_overflow_ne (x y : UInt256)
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    UInt256.div (UInt256.mul y x) y ≠ x := by
  intro hEq
  have hyNatNe : y.toNat ≠ 0 := by
    intro hy0
    have hprod0 : x.toNat * y.toNat = 0 := by simp [hy0]
    have hsizePos : 0 < UInt256.size := by norm_num [UInt256.size]
    omega
  have hnat := congrArg UInt256.toNat hEq
  rw [udiv_toNat, u256_mul_toNat] at hnat
  have hremLt : y.toNat * x.toNat % UInt256.size < y.toNat * x.toNat := by
    have hmodLt : y.toNat * x.toNat % UInt256.size < UInt256.size :=
      Nat.mod_lt _ (by norm_num [UInt256.size])
    have hover' : UInt256.size ≤ y.toNat * x.toNat := by
      simpa [Nat.mul_comm] using hover
    omega
  have hle0 := Nat.mul_div_le (y.toNat * x.toNat % UInt256.size) y.toNat
  rw [hnat] at hle0
  have hle : y.toNat * x.toNat ≤ y.toNat * x.toNat % UInt256.size := by
    simpa [Nat.mul_comm] using hle0
  omega

theorem auctionCreateBid_mul_div_noOverflow_eq_of_ne (a b : UInt256)
    (hfit : a.toNat * b.toNat < UInt256.size) (ha : a ≠ ⟨0⟩) :
    UInt256.div (UInt256.mul b a) a = b := by
  apply u256_inj
  have haNat : a.toNat ≠ 0 := by
    intro hzero
    apply ha
    apply u256_inj
    simp [hzero]
  have hmulNat : (UInt256.mul b a).toNat = b.toNat * a.toNat := by
    rw [u256_mul_toNat, Nat.mod_eq_of_lt]
    simpa [Nat.mul_comm] using hfit
  rw [udiv_toNat, hmulNat]
  simpa [Nat.mul_comm] using Nat.mul_div_right b.toNat (Nat.pos_of_ne_zero haNat)

theorem auctionCreateBid_lor_one_ne_zero (x : UInt256) :
    UInt256.lor (⟨1⟩ : UInt256) x ≠ ⟨0⟩ := by
  intro h
  have hmod := congrArg (fun w : UInt256 => w.toNat % 2) h
  change (UInt256.lor (⟨1⟩ : UInt256) x).toNat % 2 =
    (⟨0⟩ : UInt256).toNat % 2 at hmod
  rw [u256_lor_toNat] at hmod
  have htwo : 2 ∣ UInt256.size := by
    norm_num [UInt256.size]
  rw [Nat.mod_mod_of_dvd _ htwo] at hmod
  change (Nat.lor 1 x.toNat) % 2 = 0 at hmod
  have hlor : (Nat.lor 1 x.toNat) % 2 = 1 := by
    rw [Nat.mod_two_of_bodd]
    have hbit : Nat.testBit (Nat.lor 1 x.toNat) 0 = true := by
      change Nat.testBit (1 ||| x.toNat) 0 = true
      simp
    simpa [Nat.testBit, Nat.shiftRight_zero, Nat.bodd_eq_one_and_ne_zero] using hbit
  omega

set_option maxHeartbeats 1000000 in
theorem auctionCreateBidPanicOverflowRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5630⟩ R mem (UInt256.ofNat 10) rdata acc k C)
    (hov : R.length + 2 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  have hsel : UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
      ⟨35408467139433450592217433187231851964531694900788300625387963629091585785856⟩ := by
    decide
  have rd5639₀ := evm_run h with [
    jumpdest, push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0]
  have rd5639 := rd5639₀
  rw [hsel] at rd5639
  have rd5643 := evm_run rd5639 with [
    raw mstore 0
      ((UInt256.toByteArray
        (⟨35408467139433450592217433187231851964531694900788300625387963629091585785856⟩ :
          UInt256)).write 0 mem 0 32)
      (UInt256.ofNat 10) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨17⟩, push1 ⟨4⟩]
  have rd5648 := evm_run rd5643 with [
    raw mstore 0
      ((UInt256.toByteArray (⟨17⟩ : UInt256)).write 0
        ((UInt256.toByteArray
          (⟨35408467139433450592217433187231851964531694900788300625387963629091585785856⟩ :
            UInt256)).write 0 mem 0 32) 4 32)
      (UInt256.ofNat 10) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, push0]
  exact rd5648.rev 0 (by decide) mem_cost (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem auctionCreateBidCheckedMulOverflow {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5650⟩ (a :: b :: ret :: R) mem (UInt256.ofNat 10)
      rdata acc k C)
    (hover : UInt256.size ≤ a.toNat * b.toNat) (hov : R.length + 9 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  have haNe : a ≠ ⟨0⟩ := by
    intro ha
    have hprod : a.toNat * b.toNat = 0 := by simp [ha]
    have hsizePos : 0 < UInt256.size := by norm_num [UInt256.size]
    omega
  have hdivNeBase : UInt256.div (UInt256.mul a b) a ≠ b :=
    auctionCreateBid_mul_div_overflow_ne b a (by simpa [Nat.mul_comm] using hover)
  have hdivNe : UInt256.div (UInt256.mul b a) a ≠ b := by
    simpa [u256_mul_comm b a] using hdivNeBase
  have hzero : UInt256.isZero a = ⟨0⟩ := isZero_eq_zero_of_ne haNe
  have heq : UInt256.eq b (UInt256.div (UInt256.mul b a) a) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hEq; exact hdivNe hEq.symm)
  have rd5662₀ := evm_run h with [
    jumpdest, dup1, dup3, mul, dup2, iszero, dup3, dup3, div, dup5, eq, lor]
  have rd5662 := rd5662₀
  rw [hzero, heq] at rd5662
  have hcond : UInt256.lor (⟨0⟩ : UInt256) ⟨0⟩ = ⟨0⟩ := by decide
  rw [hcond] at rd5662
  have rd5666 := evm_run rd5662 with [push2 ⟨4886⟩, jumpiNT (by decide)]
  have rd5630 := evm_run rd5666 with [push2 ⟨4886⟩, push2 ⟨5630⟩, jump (by jump_dest)]
  exact auctionCreateBidPanicOverflowRevert rd5630 (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem auctionCreateBidCheckedMulOk {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5650⟩ (a :: b :: ret :: R) mem (UInt256.ofNat 10)
      rdata acc k C)
    (hfit : a.toNat * b.toNat < UInt256.size)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD auctionBytecode ee g s0 ret (UInt256.mul b a :: R) mem (UInt256.ofNat 10)
      rdata acc k' C' := by
  have hcond :
      UInt256.lor (UInt256.eq b (UInt256.div (UInt256.mul b a) a))
          (UInt256.isZero a) ≠ ⟨0⟩ := by
    by_cases ha : a = ⟨0⟩
    · rw [show UInt256.isZero a = ⟨1⟩ by rw [ha]; decide]
      rw [u256_lor_comm]
      exact auctionCreateBid_lor_one_ne_zero _
    · have hdiv := auctionCreateBid_mul_div_noOverflow_eq_of_ne a b hfit ha
      have heq : UInt256.eq b (UInt256.div (UInt256.mul b a) a) = ⟨1⟩ := by
        rw [hdiv, u256_eq_refl]
      rw [isZero_eq_zero_of_ne ha, heq]
      decide
  have rd5662 := evm_run h with [
    jumpdest, dup1, dup3, mul, dup2, iszero, dup3, dup3, div, dup5, eq, lor]
  have rd4886 := evm_run rd5662 with [push2 ⟨4886⟩, jumpiT hcond (by jump_dest)]
  exact ⟨_, _, evm_run rd4886 with [jumpdest, swap3, swap2, pop, pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem auctionCreateBidCheckedDiv100Ok {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {x ret : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5673⟩ (x :: ⟨100⟩ :: ret :: R) mem aw rdata acc k C)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD auctionBytecode ee g s0 ret (UInt256.div x ⟨100⟩ :: R) mem aw rdata acc
      k' C' := by
  have rd5699 := evm_run h with [
    jumpdest, push0, dup3, push2 ⟨5699⟩, jumpiT (by decide) (by jump_dest)]
  exact ⟨_, _, evm_run rd5699 with [jumpdest, pop, div, swap1, jump hret]⟩

theorem auctionCreateBidX_revert_nounMismatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hnoun :
      auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I ≠ auctionCreateBidArgWord I)
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1165⟩
      [auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σ1 := auctionCreateBidEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  have hnoun' : noun ≠ auctionCreateBidArgWord I := by
    simpa [noun, σ1] using hnoun
  obtain ⟨_, _, rd1282⟩ := auctionCreateBidX_toSnapshotCheck
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm hstatus hreach
  obtain ⟨_, _, rd1282'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1282⟩
      [⟨128⟩, noun, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled] using rd1282⟩
  have hcond : UInt256.eq (auctionCreateBidArgWord I) noun = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro h; exact hnoun' h.symm)
  have rd1289 := evm_run rd1282' with [
    swap1, dup3, eq, push2 ⟨1360⟩, jumpiNT hcond]
  have rd1292 := evm_run rd1289 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov)]
  have rd1300 := rd1292.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd1315 := evm_run rd1300 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 3 (auctionAuctionHasntStartedMem0 noun amount start finish bidder settled)
      (UInt256.ofNat 11) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (auctionAuctionHasntStartedMem1 noun amount start finish bidder settled)
      (UInt256.ofNat 12) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨23⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 3 (auctionCreateBidNounNotUpMem2 noun amount start finish bidder settled)
      (UInt256.ofNat 13) (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1348 := rd1315.pushConst auctionCreateBidNounNotUpStringWord
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd1356₀ := evm_run rd1348 with [
    push1 ⟨68⟩, dup3, add,
    raw mstore 3 (auctionCreateBidNounNotUpMem3 noun amount start finish bidder settled)
      (UInt256.ofNat 14) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨100⟩, add]
  have rd1356 := rd1356₀
  rw [show (⟨100⟩ : UInt256) + ⟨320⟩ = ⟨420⟩ by decide] at rd1356
  have rd994 := evm_run rd1356 with [push2 ⟨994⟩, jump (by jump_dest)]
  have rd1001₀ := evm_run rd994 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 14) (by decide)
      mem_cost
      (auctionCreateBidNounNotUpMem3_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd1001 := rd1001₀
  rw [show UInt256.sub (⟨420⟩ : UInt256) ⟨320⟩ = ⟨100⟩ by decide] at rd1001
  exact evm_run rd1001 with [raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem auctionCreateBidX_revert_expired {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hnoun :
      auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I = auctionCreateBidArgWord I)
    (htime : ¬ (UInt256.ofNat I.header.timestamp).toNat <
      (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I).toNat)
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1165⟩
      [auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σ1 := auctionCreateBidEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  have hnoun' : noun = auctionCreateBidArgWord I := by
    simpa [noun, σ1] using hnoun
  obtain ⟨_, _, rd1282⟩ := auctionCreateBidX_toSnapshotCheck
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm hstatus hreach
  obtain ⟨_, _, rd1282'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1282⟩
      [⟨128⟩, noun, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled] using rd1282⟩
  have hnounCond : UInt256.eq (auctionCreateBidArgWord I) noun ≠ ⟨0⟩ := by
    rw [hnoun']
    rw [u256_eq_refl]
    decide
  have rd1360 := evm_run rd1282' with [
    swap1, dup3, eq, push2 ⟨1360⟩, jumpiT hnounCond (by jump_dest)]
  have rd1368 := evm_run rd1360 with [
    jumpdest, dup1, push1 ⟨96⟩, add,
    raw mload 0 finish (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload224 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    timestamp, lt]
  have htimeLe : finish.toNat ≤ (UInt256.ofNat I.header.timestamp).toNat := by
    apply Nat.le_of_not_gt
    simpa [finish, σ1] using htime
  have hlt : UInt256.lt (UInt256.ofNat I.header.timestamp) finish = ⟨0⟩ :=
    ult_zero htimeLe
  have rd1372 := evm_run rd1368 with [push2 ⟨1429⟩, jumpiNT hlt]
  have rd1375 := evm_run rd1372 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov)]
  have rd1383 := rd1375.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd1398 := evm_run rd1383 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 3 (auctionAuctionHasntStartedMem0 noun amount start finish bidder settled)
      (UInt256.ofNat 11) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (auctionAuctionHasntStartedMem1 noun amount start finish bidder settled)
      (UInt256.ofNat 12) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨15⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 3 (auctionCreateBidAuctionExpiredMem2 noun amount start finish bidder settled)
      (UInt256.ofNat 13) (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1414 := rd1398.pushConst auctionCreateBidAuctionExpiredRawStringWord
    (width := 15) (op := .PUSH15) (by decide) (by decide) (by evm_ov)
  have rd1417₀ := evm_run rd1414 with [push1 ⟨138⟩, shl]
  have hword :
      UInt256.shiftLeft auctionCreateBidAuctionExpiredRawStringWord ⟨138⟩ =
        auctionCreateBidAuctionExpiredStringWord := by
    native_decide
  have rd1417 := rd1417₀
  rw [hword] at rd1417
  have rd1425₀ := evm_run rd1417 with [
    push1 ⟨68⟩, dup3, add,
    raw mstore 3 (auctionCreateBidAuctionExpiredMem3 noun amount start finish bidder settled)
      (UInt256.ofNat 14) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨100⟩, add]
  have rd1425 := rd1425₀
  rw [show (⟨100⟩ : UInt256) + ⟨320⟩ = ⟨420⟩ by decide] at rd1425
  have rd994 := evm_run rd1425 with [push2 ⟨994⟩, jump (by jump_dest)]
  have rd1001₀ := evm_run rd994 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 14) (by decide)
      mem_cost
      (auctionCreateBidAuctionExpiredMem3_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd1001 := rd1001₀
  rw [show UInt256.sub (⟨420⟩ : UInt256) ⟨320⟩ = ⟨100⟩ by decide] at rd1001
  exact evm_run rd1001 with [raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem auctionCreateBidX_toReserveCheck {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hnoun :
      auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I = auctionCreateBidArgWord I)
    (htime : (UInt256.ofNat I.header.timestamp).toNat <
      (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I).toNat)
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1165⟩
      [auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1429⟩
      [⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem
        (auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionStartWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I)
        (auctionPackedBidderWord (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I))
        (auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I)))
      (UInt256.ofNat 10) ByteArray.empty (cA, auctionCreateBidEnterMap σ I) k C := by
  let σ1 := auctionCreateBidEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  have hnoun' : noun = auctionCreateBidArgWord I := by
    simpa [noun, σ1] using hnoun
  obtain ⟨_, _, rd1282⟩ := auctionCreateBidX_toSnapshotCheck
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm hstatus hreach
  obtain ⟨_, _, rd1282'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1282⟩
      [⟨128⟩, noun, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled] using rd1282⟩
  have hnounCond : UInt256.eq (auctionCreateBidArgWord I) noun ≠ ⟨0⟩ := by
    rw [hnoun']
    rw [u256_eq_refl]
    decide
  have rd1360 := evm_run rd1282' with [
    swap1, dup3, eq, push2 ⟨1360⟩, jumpiT hnounCond (by jump_dest)]
  have rd1368 := evm_run rd1360 with [
    jumpdest, dup1, push1 ⟨96⟩, add,
    raw mload 0 finish (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload224 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    timestamp, lt]
  have hlt : UInt256.lt (UInt256.ofNat I.header.timestamp) finish = ⟨1⟩ := by
    apply ult_one
    simpa [finish, σ1] using htime
  have hcond : UInt256.lt (UInt256.ofNat I.header.timestamp) finish ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rd1429 := evm_run rd1368 with [push2 ⟨1429⟩, jumpiT hcond (by jump_dest)]
  exact ⟨_, _, by
    simpa [σ1, noun, amount, start, finish, packed, bidder, settled, hnoun'] using rd1429⟩

theorem auctionCreateBidX_revert_belowReserve {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hnoun :
      auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I = auctionCreateBidArgWord I)
    (htime : (UInt256.ofNat I.header.timestamp).toNat <
      (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I).toNat)
    (hreserve : I.weiValue.toNat <
      (auctionSlotWord ⟨204⟩ (auctionCreateBidEnterMap σ I) I).toNat)
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1165⟩
      [auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σ1 := auctionCreateBidEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  let reserve := auctionSlotWord ⟨204⟩ σ1 I
  obtain ⟨_, _, rd1429⟩ := auctionCreateBidX_toReserveCheck
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm hstatus hnoun htime hreach
  obtain ⟨_, _, rd1429'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1429⟩
      [⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled] using rd1429⟩
  obtain ⟨_, _, rd1433₀⟩ := (evm_run rd1429' with [jumpdest, push1 ⟨204⟩]).sload
    (by decide) (by evm_ov)
  obtain ⟨_, _, rd1433⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1433⟩
      [reserve, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by simpa [reserve, auctionSlotWord, σ1] using rd1433₀⟩
  have rd1436 := evm_run rd1433 with [callvalue, lt, iszero]
  have hlt : UInt256.lt I.weiValue reserve = ⟨1⟩ := by
    apply ult_one
    simpa [reserve, σ1] using hreserve
  have hcond : UInt256.isZero (UInt256.lt I.weiValue reserve) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rd1440 := evm_run rd1436 with [push2 ⟨1511⟩, jumpiNT hcond]
  have rd1443 := evm_run rd1440 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov)]
  have rd1447 := rd1443.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd1466 := evm_run rd1447 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 3 (auctionAuctionHasntStartedMem0 noun amount start finish bidder settled)
      (UInt256.ofNat 11) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (auctionAuctionHasntStartedMem1 noun amount start finish bidder settled)
      (UInt256.ofNat 12) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨31⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 3 (auctionCreateBidReservePriceMem2 noun amount start finish bidder settled)
      (UInt256.ofNat 13) (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1499 := rd1466.pushConst auctionCreateBidReservePriceStringWord
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd1507₀ := evm_run rd1499 with [
    push1 ⟨68⟩, dup3, add,
    raw mstore 3 (auctionCreateBidReservePriceMem3 noun amount start finish bidder settled)
      (UInt256.ofNat 14) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨100⟩, add]
  have rd1507 := rd1507₀
  rw [show (⟨100⟩ : UInt256) + ⟨320⟩ = ⟨420⟩ by decide] at rd1507
  have rd994 := evm_run rd1507 with [push2 ⟨994⟩, jump (by jump_dest)]
  have rd1001₀ := evm_run rd994 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 14) (by decide)
      mem_cost
      (auctionCreateBidReservePriceMem3_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd1001 := rd1001₀
  rw [show UInt256.sub (⟨420⟩ : UInt256) ⟨320⟩ = ⟨100⟩ by decide] at rd1001
  exact evm_run rd1001 with [raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem auctionCreateBidX_toMinBidCheck {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hnoun :
      auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I = auctionCreateBidArgWord I)
    (htime : (UInt256.ofNat I.header.timestamp).toNat <
      (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I).toNat)
    (hreserve : (auctionSlotWord ⟨204⟩ (auctionCreateBidEnterMap σ I) I).toNat ≤
      I.weiValue.toNat)
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1165⟩
      [auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1511⟩
      [⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem
        (auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionStartWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I)
        (auctionPackedBidderWord (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I))
        (auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I)))
      (UInt256.ofNat 10) ByteArray.empty (cA, auctionCreateBidEnterMap σ I) k C := by
  let σ1 := auctionCreateBidEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  let reserve := auctionSlotWord ⟨204⟩ σ1 I
  obtain ⟨_, _, rd1429⟩ := auctionCreateBidX_toReserveCheck
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm hstatus hnoun htime hreach
  obtain ⟨_, _, rd1429'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1429⟩
      [⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled] using rd1429⟩
  obtain ⟨_, _, rd1433₀⟩ := (evm_run rd1429' with [jumpdest, push1 ⟨204⟩]).sload
    (by decide) (by evm_ov)
  obtain ⟨_, _, rd1433⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1433⟩
      [reserve, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by simpa [reserve, auctionSlotWord, σ1] using rd1433₀⟩
  have rd1436 := evm_run rd1433 with [callvalue, lt, iszero]
  have hlt : UInt256.lt I.weiValue reserve = ⟨0⟩ := by
    apply ult_zero
    simpa [reserve, σ1] using hreserve
  have hcond : UInt256.isZero (UInt256.lt I.weiValue reserve) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rd1511 := evm_run rd1436 with [push2 ⟨1511⟩, jumpiT hcond (by jump_dest)]
  exact ⟨_, _, by
    simpa [σ1, noun, amount, start, finish, packed, bidder, settled] using rd1511⟩

theorem auctionCreateBidX_revert_minBidMulOverflow {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hnoun :
      auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I = auctionCreateBidArgWord I)
    (htime : (UInt256.ofNat I.header.timestamp).toNat <
      (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I).toNat)
    (hreserve : (auctionSlotWord ⟨204⟩ (auctionCreateBidEnterMap σ I) I).toNat ≤
      I.weiValue.toNat)
    (hmulOverflow : UInt256.size ≤
      (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat *
        (UInt256.land (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ I) I)
          ⟨255⟩).toNat)
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1165⟩
      [auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σ1 := auctionCreateBidEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  let minBidRaw := auctionSlotWord ⟨205⟩ σ1 I
  let minBid := UInt256.land minBidRaw ⟨255⟩
  obtain ⟨_, _, rd1511⟩ := auctionCreateBidX_toMinBidCheck
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm hstatus hnoun htime hreserve hreach
  obtain ⟨_, _, rd1511'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1511⟩
      [⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled] using rd1511⟩
  obtain ⟨_, _, rd1515₀⟩ := (evm_run rd1511' with [jumpdest, push1 ⟨205⟩]).sload
    (by decide) (by evm_ov)
  obtain ⟨_, _, rd1515⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1515⟩
      [minBidRaw, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by simpa [minBidRaw, auctionSlotWord, σ1] using rd1515₀⟩
  have rd1520 := evm_run rd1515 with [
    push1 ⟨32⟩, dup3, add,
    raw mload 0 amount (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload160 noun amount start finish bidder settled)
      (by decide) (by evm_ov)]
  have rd5650 := evm_run rd1520 with [
    push1 ⟨100⟩, swap2, push2 ⟨1537⟩, swap2, push1 ⟨255⟩, swap1, swap2, and,
    swap1, push2 ⟨5650⟩, jump (by jump_dest)]
  exact auctionCreateBidCheckedMulOverflow
    (a := amount) (b := minBid) (ret := ⟨1537⟩)
    (R := [⟨100⟩, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I])
    rd5650 (by simpa [amount, minBid, minBidRaw, σ1] using hmulOverflow) (by simp)

theorem auctionCreateBidX_toMinBidAddCheck {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hnoun :
      auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I = auctionCreateBidArgWord I)
    (htime : (UInt256.ofNat I.header.timestamp).toNat <
      (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I).toNat)
    (hreserve : (auctionSlotWord ⟨204⟩ (auctionCreateBidEnterMap σ I) I).toNat ≤
      I.weiValue.toNat)
    (hmulFit :
      (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat *
        (UInt256.land (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ I) I)
          ⟨255⟩).toNat < UInt256.size)
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1165⟩
      [auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1547⟩
      [UInt256.div
        (UInt256.mul
          (UInt256.land (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ I) I) ⟨255⟩)
          (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I)) ⟨100⟩,
        ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem
        (auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionStartWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I)
        (auctionPackedBidderWord (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I))
        (auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I)))
      (UInt256.ofNat 10) ByteArray.empty (cA, auctionCreateBidEnterMap σ I) k C := by
  let σ1 := auctionCreateBidEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  let minBidRaw := auctionSlotWord ⟨205⟩ σ1 I
  let minBid := UInt256.land minBidRaw ⟨255⟩
  obtain ⟨_, _, rd1511⟩ := auctionCreateBidX_toMinBidCheck
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm hstatus hnoun htime hreserve hreach
  obtain ⟨_, _, rd1511'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1511⟩
      [⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled] using rd1511⟩
  obtain ⟨_, _, rd1515₀⟩ := (evm_run rd1511' with [jumpdest, push1 ⟨205⟩]).sload
    (by decide) (by evm_ov)
  obtain ⟨_, _, rd1515⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1515⟩
      [minBidRaw, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by simpa [minBidRaw, auctionSlotWord, σ1] using rd1515₀⟩
  have rd1520 := evm_run rd1515 with [
    push1 ⟨32⟩, dup3, add,
    raw mload 0 amount (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload160 noun amount start finish bidder settled)
      (by decide) (by evm_ov)]
  have rd5650 := evm_run rd1520 with [
    push1 ⟨100⟩, swap2, push2 ⟨1537⟩, swap2, push1 ⟨255⟩, swap1, swap2, and,
    swap1, push2 ⟨5650⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd1537⟩ := auctionCreateBidCheckedMulOk
    (a := amount) (b := minBid) (ret := ⟨1537⟩)
    (R := [⟨100⟩, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I])
    rd5650 (by simpa [amount, minBid, minBidRaw, σ1] using hmulFit) (by jump_dest)
    (by simp)
  have rd5673 := evm_run rd1537 with [
    jumpdest, push2 ⟨1547⟩, swap2, swap1, push2 ⟨5673⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd1547⟩ := auctionCreateBidCheckedDiv100Ok
    (x := UInt256.mul minBid amount) (ret := ⟨1547⟩)
    (R := [⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I])
    rd5673 (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [σ1, noun, amount, start, finish, packed, bidder, settled, minBidRaw, minBid]
      using rd1547⟩

end Auction
