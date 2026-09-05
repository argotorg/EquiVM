import Benchmarks.Auction.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

abbrev auctionTransferOwnershipArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

def auctionTransferOwnershipStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "newOwner"
    (.address (AccountAddress.ofNat (auctionTransferOwnershipArgWord I).toNat))

def auctionTransferOwnershipPostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  auctionSetOwnerPostMap σ I (auctionTransferOwnershipArgWord I)

def auctionTransferOwnershipPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  auctionSetOwnerPostState evm (auctionTransferOwnershipArgWord I)

theorem auctionTransferOwnershipStore_arg (I : ExecutionEnv) :
    (auctionTransferOwnershipStore I).get? "newOwner" =
      some (.address (AccountAddress.ofNat (auctionTransferOwnershipArgWord I).toNat)) := by
  rw [auctionTransferOwnershipStore, store_get_self]

theorem auctionTransferOwnershipStore_owner (I : ExecutionEnv) :
    (auctionTransferOwnershipStore I).get? "_owner" = none := by
  rw [auctionTransferOwnershipStore, store_get_ne _ _ (by decide)]
  native_decide

theorem auctionDispatch_transferOwnership {I : ExecutionEnv}
    (hsel : selIs I (auctionSelBytes 19)) :
    dispatchMsg auctionContract I.calldata = some transferOwnershipTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [initializeTransition, createBidTransition, settleAndCreateTransition,
      settleAuctionTransition, pauseTransition, unpauseTransition, setTimeBufferTransition,
      setReservePriceTransition, setMinBidIncTransition])
    (post := [renounceOwnershipTransition, ownerGetter, pausedGetter, nounsGetter, wethGetter,
      timeBufferGetter, reservePriceGetter, minBidIncGetter, durationGetter, auctionGetter])
    (ti := transferOwnershipTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = auctionSelBytes 19 := (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, initializeSelectorBytes, createBidSelectorBytes,
        settleAndCreateSelectorBytes, settleAuctionSelectorBytes, pauseSelectorBytes,
        unpauseSelectorBytes, setTimeBufferSelectorBytes, setReservePriceSelectorBytes,
        setMinBidIncSelectorBytes, hcd, auctionSelBytes]
      native_decide
  · rw [selectorOf, transferOwnershipSelectorBytes]
    simpa [selIs, auctionSelBytes] using hsel

theorem auctionDecode_transferOwnership {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (auctionTransferOwnershipArgWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (transferOwnershipTransition.params.map Param.name)
        (transitionSignature transferOwnershipTransition).paramTypes I.calldata =
      some (auctionTransferOwnershipStore I) := by
  show decodeCalldata ["newOwner"] [addr] I.calldata =
    some (auctionTransferOwnershipStore I)
  simpa [auctionTransferOwnershipStore, auctionTransferOwnershipArgWord, addr, calldataWord] using
    decodeCalldata_address_ok (cd := I.calldata) (x := "newOwner") hsz36 hbig hcanon

theorem auctionDecode_transferOwnership_none_short {I : ExecutionEnv}
    (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (transferOwnershipTransition.params.map Param.name)
        (transitionSignature transferOwnershipTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["newOwner"] [addr] I.calldata = none
  by_cases hsz4 : 4 ≤ I.calldata.size
  · simpa [addr] using
      decodeCalldata_address_none_short (cd := I.calldata) (x := "newOwner") hsz4 hshort
  · have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [decodeCalldata_scalarWords_eq (names := ["newOwner"]) (types := [addr])
      (cd := I.calldata) (by decide)]
    rw [if_pos (by rw [htlen]; omega : I.calldata.toList.length < 4)]

theorem auctionDecode_transferOwnership_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (transferOwnershipTransition.params.map Param.name)
        (transitionSignature transferOwnershipTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["newOwner"] [addr] I.calldata = none
  simpa [addr] using
    decodeCalldata_address_none_huge (cd := I.calldata) (x := "newOwner") hbig

theorem auctionDecode_transferOwnership_none_noncanon {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (auctionTransferOwnershipArgWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (transferOwnershipTransition.params.map Param.name)
        (transitionSignature transferOwnershipTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["newOwner"] [addr] I.calldata = none
  simpa [auctionTransferOwnershipArgWord, addr, calldataWord] using
    decodeCalldata_address_none_noncanon (cd := I.calldata) (x := "newOwner")
      hsz36 hbig hnc

theorem evalExpr_transferOwnership_owner (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionTransferOwnershipStore I }
        evm (.storage ownerRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := auctionTransferOwnershipStore I } evm ownerRef =
        .ok { base := "_owner", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, ownerRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_owner", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar (t := .address) (hbase := auctionTransferOwnershipStore_owner I)
    (her := her) (hty := hty) (hloc := by rfl)]
  exact congrArg EvalResult.ok (by
    simpa [auctionAddrLoc] using auctionStorageLocLoad_address_offset0 evm ⟨151⟩)

theorem evalExpr_transferOwnership_sender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionTransferOwnershipStore I }
      evm sender = .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_transferOwnership_owner_eq_true (evm : EVM.State) (I : ExecutionEnv)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionTransferOwnershipStore I }
      evm (.binary .eq sender (.storage ownerRef)) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_transferOwnership_sender, evalExpr_transferOwnership_owner,
    bind, EvalResult.bind, evalBinaryOp?]
  rw [auctionMaskedAddress_eq_source_of_word_eq (I := evm.executionEnv) howner]
  simp [BEq.beq]

theorem evalExpr_transferOwnership_owner_eq_false (evm : EVM.State) (I : ExecutionEnv)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask ≠
        auctionSourceWord evm.executionEnv) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionTransferOwnershipStore I }
      evm (.binary .eq sender (.storage ownerRef)) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_transferOwnership_sender, evalExpr_transferOwnership_owner,
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

theorem evalExpr_transferOwnership_arg (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionTransferOwnershipStore I }
      evm (.var "newOwner") =
        .ok (.address (AccountAddress.ofNat (auctionTransferOwnershipArgWord I).toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [auctionTransferOwnershipStore_arg]

theorem evalExpr_transferOwnership_zeroAddr (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionTransferOwnershipStore I }
      evm zeroAddr = .ok (.address (AccountAddress.ofNat 0)) := by
  rw [zeroAddr, evalExpr?.eq_16, evalExpr?.eq_1]
  change (EvalResult.ok (Value.int 0)).bind
      (fun value => EvalResult.ofOption EvalError.typeError
        (castValue? value (.elem .address))) =
    EvalResult.ok (Value.address (AccountAddress.ofNat 0))
  rfl

theorem auctionTransferOwnershipArgAddress_ne_zero (I : ExecutionEnv)
    (hcanon : (auctionTransferOwnershipArgWord I).toNat < EVM.addressModulus)
    (hnew : auctionTransferOwnershipArgWord I ≠ ⟨0⟩) :
    AccountAddress.ofNat (auctionTransferOwnershipArgWord I).toNat ≠ AccountAddress.ofNat 0 := by
  intro haddr
  apply hnew
  apply u256_inj
  have hval := congrArg Fin.val haddr
  unfold AccountAddress.ofNat at hval
  rw [Fin.val_ofNat, Fin.val_ofNat] at hval
  have hmod : (auctionTransferOwnershipArgWord I).toNat % AccountAddress.size =
      (auctionTransferOwnershipArgWord I).toNat := by
    exact Nat.mod_eq_of_lt (by
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)
  rw [hmod] at hval
  simpa using hval

theorem evalExpr_transferOwnership_newOwner_ne_zero_true (evm : EVM.State) (I : ExecutionEnv)
    (hcanon : (auctionTransferOwnershipArgWord I).toNat < EVM.addressModulus)
    (hnew : auctionTransferOwnershipArgWord I ≠ ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionTransferOwnershipStore I }
      evm (.binary .ne (.var "newOwner") zeroAddr) = .ok (.bool true) := by
  have haddr := auctionTransferOwnershipArgAddress_ne_zero I hcanon hnew
  simp only [evalExpr?, evalExpr_transferOwnership_arg, evalExpr_transferOwnership_zeroAddr,
    bind, EvalResult.bind, evalBinaryOp?]
  rw [show ((.address (AccountAddress.ofNat (auctionTransferOwnershipArgWord I).toNat) : Value) ==
          .address (AccountAddress.ofNat 0)) = false by
    simp [BEq.beq, haddr]]
  rfl

theorem evalExpr_transferOwnership_newOwner_ne_zero_false (evm : EVM.State) (I : ExecutionEnv)
    (hzero : auctionTransferOwnershipArgWord I = ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionTransferOwnershipStore I }
      evm (.binary .ne (.var "newOwner") zeroAddr) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_transferOwnership_arg, evalExpr_transferOwnership_zeroAddr,
    bind, EvalResult.bind, evalBinaryOp?]
  rw [hzero]
  simp [BEq.beq]

theorem auctionTransferOwnershipAssign (evm : EVM.State) (I : ExecutionEnv)
    (hcanon : (auctionTransferOwnershipArgWord I).toNat < EVM.addressModulus) :
    assignStorageRef? auctionConfig
        { contract := auctionContract, locals := auctionTransferOwnershipStore I } evm .storage
        ownerRef (.address (AccountAddress.ofNat (auctionTransferOwnershipArgWord I).toNat)) =
      .ok ({ contract := auctionContract, locals := auctionTransferOwnershipStore I },
        auctionTransferOwnershipPostState evm I) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := auctionTransferOwnershipStore I } evm
      ownerRef = .ok { base := "_owner", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, ownerRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_owner", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
    decide
  have hstore :
      storageLocStore evm (auctionAddrLoc ⟨151⟩)
          (.address (AccountAddress.ofNat (auctionTransferOwnershipArgWord I).toNat)) =
        some (auctionTransferOwnershipPostState evm I) := by
    change storageLocStore evm (addressOffset0Loc ⟨151⟩)
        (.address (AccountAddress.ofNat (auctionTransferOwnershipArgWord I).toNat)) =
      some (auctionSetOwnerPostState evm (auctionTransferOwnershipArgWord I))
    simpa [auctionSetOwnerPostState, auctionSetOwnerWord] using
      storageLocStore_address_offset0 evm ⟨151⟩ (auctionTransferOwnershipArgWord I) hcanon
  exact assignStorageRef_storage_scalar_value (cfg := auctionConfig)
    (solm := { contract := auctionContract, locals := auctionTransferOwnershipStore I })
    (evm := evm) (slot := ownerRef) (er := { base := "_owner", steps := [] })
    (ty := .elem .address) (loc := auctionAddrLoc ⟨151⟩)
    (hbase := auctionTransferOwnershipStore_owner I) (her := her) (hty := hty)
    (hloc := by rfl) (by trivial) hstore

theorem auctionTransferOwnershipBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hcanon : (auctionTransferOwnershipArgWord I).toNat < EVM.addressModulus)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hnew : auctionTransferOwnershipArgWord I ≠ ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionTransferOwnershipStore I)
      transferOwnershipTransition.body
      (.returned { contract := auctionContract, locals := auctionTransferOwnershipStore I }
        (auctionTransferOwnershipPostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferOwnership_owner_eq_true evm I howner)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferOwnership_newOwner_ne_zero_true evm I hcanon hnew)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferOwnership_arg evm I)
      (auctionTransferOwnershipAssign evm I hcanon))
    ExecBlock.nil

theorem auctionTransferOwnershipBodyReverts_callvalue (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionTransferOwnershipStore I)
      transferOwnershipTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalCallvalueEq_false hwv))

theorem auctionTransferOwnershipBodyReverts_owner (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask ≠
        auctionSourceWord evm.executionEnv) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionTransferOwnershipStore I)
      transferOwnershipTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_transferOwnership_owner_eq_false evm I howner))

theorem auctionTransferOwnershipBodyReverts_zero (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hzero : auctionTransferOwnershipArgWord I = ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionTransferOwnershipStore I)
      transferOwnershipTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferOwnership_owner_eq_true evm I howner)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_transferOwnership_newOwner_ne_zero_false evm I hzero))

theorem auctionReachTransferOwnershipBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = auctionBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (auctionSelBytes 19)) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨921⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsel' : ((⟨#[0xf2, 0xfd, 0xe3, 0x8b]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs, auctionSelBytes] using hsel
  have hword : auctionSelWord I = ⟨0xf2fde38b⟩ :=
    auctionSelWord_eq_of_beq I hsz 0xf2 0xfd 0xe3 0x8b ⟨0xf2fde38b⟩
      (by decide) hsel'
  obtain ⟨_, _, hsplit⟩ := auctionReachRootSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
  have hroot : UInt256.gt (armSelNat auctionBytecode auctionSplitPc) (auctionSelWord I) =
      ⟨0⟩ := by
    rw [hword]
    decide
  have h29 := RD.selectorSplitNotTakenAuto hsplit auctionSplitWellFormed hroot (by simp)
  have hupper : UInt256.gt (armSelNat auctionBytecode auctionUpperSplitPc) (auctionSelWord I) =
      ⟨0⟩ := by
    rw [hword]
    decide
  have h40 := RD.selectorSplitNotTakenAuto h29 auctionUpperSplitWellFormed hupper (by simp)
  have heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat auctionBytecode
        (nthArmPc auctionBytecode auctionUpperMidFirstArmPc j)) (auctionSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> decide
  have htake :
      UInt256.eq
        (armSelNat auctionBytecode (nthArmPc auctionBytecode auctionUpperMidFirstArmPc 4))
        (auctionSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide
  exact RD.dispatchTo (code := auctionBytecode) (ee := I) (g := g)
    (s0 := initState cA gh bl σ σ₀ g A I) (selWord := auctionSelWord I)
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (acc := (cA, σ)) ⟨921⟩ 4 h40
    (fun j hj => auctionUpperMidArmsWellFormed j (by omega)) heq0 htake
    (by jump_dest)
    (by native_decide)
    (by simp)

theorem auctionX_transferOwnership_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨921⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd921⟩ := hreach
  exact evm_run rd921 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨932⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv),
    push0, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem auctionTransferOwnershipX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨921⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5495⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨947⟩, ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd921⟩ := hreach
  exact ⟨_, _, evm_run rd921 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨932⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push2 ⟨413⟩, push2 ⟨947⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨5495⟩, jump (by jump_dest)]⟩

set_option maxHeartbeats 800000 in
theorem auctionDecodeAddressOk5495 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5495⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨0⟩)
    (hcanon : (calldataWord ee.calldata 4).toNat < EVM.addressModulus)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD auctionBytecode ee g s0 ret (calldataWord ee.calldata 4 :: R)
      mem aw rdata acc k' C' := by
  have rd5511 := evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨5511⟩,
    jumpiT (by rw [hsltval]; decide) (by jump_dest), jumpdest]
  have rd5380 := evm_run rd5511 with [dup2, calldataload, push2 ⟨5350⟩, dup2,
    push2 ⟨5380⟩, jump (by jump_dest)]
  have rd5392₀ := evm_run rd5380 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, dup2, eq]
  have heq : UInt256.eq
      (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
      (UInt256.land
        (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
        solcAddrMask) = ⟨1⟩ := by
    simpa [calldataWord] using solcAddrCanon_eq hcanon
  have rd5392 := rd5392₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by decide] at rd5392
  rw [heq] at rd5392
  have rd2850 := evm_run rd5392 with [push2 ⟨2850⟩, jumpiT (by decide) (by jump_dest),
    jumpdest]
  have rd5350 := evm_run rd2850 with [pop, jump (by jump_dest), jumpdest]
  exact ⟨_, _, by
    simpa [calldataWord] using evm_run rd5350 with [swap4, swap3, pop, pop, pop, jump hret]⟩

theorem auctionDecodeAddressLenRevert5495 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5495⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩)
    (hov : R.length + 20 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  exact evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨5511⟩,
    jumpiNT (by rw [hsltval]; decide),
    push0, dup1, raw rev 0 (by decide) (fun s _ hstk => memExpRevert0 s hstk) (by
      have hR : R.length ≤ 1024 - 20 := Nat.le_sub_of_add_le hov
      simp only [List.length_cons]
      omega)]

set_option maxHeartbeats 800000 in
theorem auctionDecodeAddressNoncanonRevert5495 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5495⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨0⟩)
    (hnc : ¬ (calldataWord ee.calldata 4).toNat < EVM.addressModulus)
    (hov : R.length + 20 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  have rd5511 := evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨5511⟩,
    jumpiT (by rw [hsltval]; decide) (by jump_dest), jumpdest]
  have rd5380 := evm_run rd5511 with [dup2, calldataload, push2 ⟨5350⟩, dup2,
    push2 ⟨5380⟩, jump (by jump_dest)]
  have rd5392₀ := evm_run rd5380 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, dup2, eq]
  have heq0word : UInt256.eq (calldataWord ee.calldata 4)
      (UInt256.land (calldataWord ee.calldata 4) solcAddrMask) = ⟨0⟩ := by
    apply u256_eq_of_ne
    intro heqword
    apply hnc
    apply solcAddrCanonical_of_clean
    rw [← heqword, u256_eq_refl]
  have heq0 : UInt256.eq
      (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
      (UInt256.land
        (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
        solcAddrMask) = ⟨0⟩ := by
    simpa [calldataWord] using heq0word
  have rd5392 := rd5392₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by decide] at rd5392
  rw [heq0] at rd5392
  exact evm_run rd5392 with [
    push2 ⟨2850⟩, jumpiNT (by decide),
    push0, dup1, raw rev 0 (by decide) (fun s _ hstk => memExpRevert0 s hstk) (by
      have hR : R.length ≤ 1024 - 20 := Nat.le_sub_of_add_le hov
      simp only [List.length_cons]
      omega)]

theorem auctionTransferOwnershipX_decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (auctionTransferOwnershipArgWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨921⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2698⟩
      [auctionTransferOwnershipArgWord I, ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  obtain ⟨_, _, rd5495⟩ := auctionTransferOwnershipX_toDecoder (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hreach hwv
  obtain ⟨_, _, rd947⟩ :=
    auctionDecodeAddressOk5495 (R := [⟨413⟩, sel]) rd5495 hslt hcanon
      (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa [auctionTransferOwnershipArgWord, calldataWord] using
      evm_run rd947 with [jumpdest, push2 ⟨2698⟩, jump (by jump_dest)]⟩

theorem auctionTransferOwnershipX_decodeRevert_short {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨921⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  obtain ⟨_, _, rd5495⟩ := auctionTransferOwnershipX_toDecoder (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hreach hwv
  exact auctionDecodeAddressLenRevert5495 (R := [⟨413⟩, sel]) rd5495 hslt
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem auctionTransferOwnershipX_decodeRevert_huge {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨921⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  obtain ⟨_, _, rd5495⟩ := auctionTransferOwnershipX_toDecoder (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hreach hwv
  exact auctionDecodeAddressLenRevert5495 (R := [⟨413⟩, sel]) rd5495 hslt
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem auctionTransferOwnershipX_decodeRevert_noncanon {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (auctionTransferOwnershipArgWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨921⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  obtain ⟨_, _, rd5495⟩ := auctionTransferOwnershipX_toDecoder (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hreach hwv
  exact auctionDecodeAddressNoncanonRevert5495 (R := [⟨413⟩, sel]) rd5495 hslt
    (by simpa [auctionTransferOwnershipArgWord, calldataWord] using hnc)
    (by simp only [List.length_cons, List.length_nil]; omega)

def auctionNewOwnerZeroStringWord1 : UInt256 :=
  ⟨0x4f776e61626c653a206e6577206f776e657220697320746865207a65726f2061⟩

def auctionNewOwnerZeroStringWord2 : UInt256 :=
  UInt256.shiftLeft (⟨0x646472657373⟩ : UInt256) ⟨208⟩

noncomputable def auctionNewOwnerZeroStringMem4 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray auctionNewOwnerZeroStringWord2).write 0
    (solcErrorStringMem3 ⟨38⟩ auctionNewOwnerZeroStringWord1 mem) 228 32

theorem auctionNewOwnerZeroStringMem4_read64 :
    (auctionNewOwnerZeroStringMem4 solcFreePtrMem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold auctionNewOwnerZeroStringMem4
  rw [toByteArray_write_read_below_of_gap auctionNewOwnerZeroStringWord2
    (solcErrorStringMem3 ⟨38⟩ auctionNewOwnerZeroStringWord1 solcFreePtrMem) 228 64]
  · exact solcErrorStringMem3_read64 ⟨38⟩ auctionNewOwnerZeroStringWord1
      solcFreePtrMem_size solcFreePtrMem_read64
  · rw [solcErrorStringMem3_size ⟨38⟩ auctionNewOwnerZeroStringWord1 solcFreePtrMem_size]
    omega
  · omega
  · rw [solcErrorStringMem3_size ⟨38⟩ auctionNewOwnerZeroStringWord1 solcFreePtrMem_size]
    native_decide

theorem auctionNewOwnerZeroStringMem4_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ (auctionNewOwnerZeroStringMem4 solcFreePtrMem).size
        ∨ (⟨64⟩ : UInt256) ≥ (UInt256.ofNat 9) * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((auctionNewOwnerZeroStringMem4 solcFreePtrMem).readWithPadding
         (⟨64⟩ : UInt256).toNat 32))) = (⟨128⟩ : UInt256) := by
  apply mloadFreePtrValue
  · unfold auctionNewOwnerZeroStringMem4
    have hge := toByteArray_write_size_ge_off_add32 auctionNewOwnerZeroStringWord2
      (solcErrorStringMem3 ⟨38⟩ auctionNewOwnerZeroStringWord1 solcFreePtrMem) 228 (by
        rw [solcErrorStringMem3_size ⟨38⟩ auctionNewOwnerZeroStringWord1 solcFreePtrMem_size]
        native_decide)
    omega
  · decide
  · exact auctionNewOwnerZeroStringMem4_read64

set_option maxHeartbeats 1000000 in
theorem auctionX_transferOwnership_success {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (auctionTransferOwnershipArgWord I).toNat < EVM.addressModulus)
    (howner :
      UInt256.land (auctionSlotWord ⟨151⟩ σ I) solcAddrMask = auctionSourceWord I)
    (hnew : auctionTransferOwnershipArgWord I ≠ ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨921⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret auctionBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, auctionTransferOwnershipPostMap σ I) ByteArray.empty := by
  obtain ⟨_, _, rd2698⟩ := auctionTransferOwnershipX_decoded (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := auctionSelWord I) hwv hsz36 hsize hszhi hcanon hreach
  have rd2701₀ := evm_run rd2698 with [jumpdest, push1 ⟨151⟩]
  obtain ⟨_, _, rd2702₀⟩ := rd2701₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2702⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2702⟩
      [auctionSlotWord ⟨151⟩ σ I, auctionTransferOwnershipArgWord I, ⟨413⟩,
        auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2702₀⟩
  have rd2712₁ := evm_run rd2702 with [
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
  have rd2712 := rd2712₁
  rw [heq] at rd2712
  have rd2740 := evm_run rd2712 with [
    push2 ⟨2740⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  have rd2750₀ := evm_run rd2740 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and]
  have hsolcMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have hclean :
      UInt256.land (auctionTransferOwnershipArgWord I) solcAddrMask =
        auctionTransferOwnershipArgWord I :=
    solcAddrMask_clean hcanon
  have rd2750 := rd2750₀
  rw [hsolcMask] at rd2750
  rw [hclean] at rd2750
  have rd2841 := evm_run rd2750 with [
    push2 ⟨2841⟩, jumpiT (by exact hnew) (by jump_dest), jumpdest]
  have rd3574 := evm_run rd2841 with [push2 ⟨2850⟩, dup2, push2 ⟨3574⟩,
    jump (by jump_dest)]
  have rd3578₀ := evm_run rd3574 with [jumpdest, push1 ⟨151⟩, dup1]
  obtain ⟨_, _, rd3579₀⟩ := rd3578₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd3579⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3579⟩
      [auctionSlotWord ⟨151⟩ σ I, ⟨151⟩, auctionTransferOwnershipArgWord I,
        ⟨2850⟩, auctionTransferOwnershipArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3579₀⟩
  have hpostComm :
      UInt256.lor (UInt256.land solcAddrMask (auctionTransferOwnershipArgWord I))
          (UInt256.land (auctionSlotWord ⟨151⟩ σ I) (UInt256.lnot solcAddrMask)) =
        auctionSetOwnerWord (auctionSlotWord ⟨151⟩ σ I)
          (auctionTransferOwnershipArgWord I) := by
    rw [u256_land_comm solcAddrMask (auctionTransferOwnershipArgWord I)]
    unfold auctionSetOwnerWord setAddressOffset0Word
    rw [u256_lor_comm]
  have rd3605₀ := evm_run rd3579 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, dup2, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, dup4, and, dup2, lor,
    swap1, swap4]
  have rd3605 := rd3605₀
  rw [hsolcMask] at rd3605
  rw [hpostComm] at rd3605
  obtain ⟨_, _, rd3606₀⟩ := rd3605.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd3606⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3606⟩
      [solcAddrMask, auctionSlotWord ⟨151⟩ σ I,
        UInt256.land solcAddrMask (auctionTransferOwnershipArgWord I),
        auctionTransferOwnershipArgWord I, ⟨2850⟩, auctionTransferOwnershipArgWord I,
        ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionTransferOwnershipPostMap σ I) k C := by
    exact ⟨_, _, by simpa [auctionTransferOwnershipPostMap, auctionSetOwnerPostMap] using
      rd3606₀⟩
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
  have rd2850 := evm_run rd3653 with [
    pop, pop, jump (by jump_dest), jumpdest, pop, jump (by jump_dest), jumpdest]
  exact rd2850.stop (by decide) (by evm_ov)

theorem auctionX_transferOwnership_revert_owner {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (auctionTransferOwnershipArgWord I).toNat < EVM.addressModulus)
    (howner :
      UInt256.land (auctionSlotWord ⟨151⟩ σ I) solcAddrMask ≠ auctionSourceWord I)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨921⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2698⟩ := auctionTransferOwnershipX_decoded (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := auctionSelWord I) hwv hsz36 hsize hszhi hcanon hreach
  have rd2701₀ := evm_run rd2698 with [jumpdest, push1 ⟨151⟩]
  obtain ⟨_, _, rd2702₀⟩ := rd2701₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2702⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2702⟩
      [auctionSlotWord ⟨151⟩ σ I, auctionTransferOwnershipArgWord I, ⟨413⟩,
        auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2702₀⟩
  have rd2712₁ := evm_run rd2702 with [
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
  have rd2712 := rd2712₁
  rw [heq] at rd2712
  have rd2720 := evm_run rd2712 with [
    push2 ⟨2740⟩, jumpiNT (by decide),
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov)]
  have rd2724 := rd2720.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd5522 := evm_run rd2724 with [
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

theorem auctionX_transferOwnership_revert_zero {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (auctionTransferOwnershipArgWord I).toNat < EVM.addressModulus)
    (howner :
      UInt256.land (auctionSlotWord ⟨151⟩ σ I) solcAddrMask = auctionSourceWord I)
    (hzero : auctionTransferOwnershipArgWord I = ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨921⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2698⟩ := auctionTransferOwnershipX_decoded (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := auctionSelWord I) hwv hsz36 hsize hszhi hcanon hreach
  have rd2701₀ := evm_run rd2698 with [jumpdest, push1 ⟨151⟩]
  obtain ⟨_, _, rd2702₀⟩ := rd2701₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2702⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2702⟩
      [auctionSlotWord ⟨151⟩ σ I, auctionTransferOwnershipArgWord I, ⟨413⟩,
        auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2702₀⟩
  have rd2712₁ := evm_run rd2702 with [
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
  have rd2712 := rd2712₁
  rw [heq] at rd2712
  have rd2740 := evm_run rd2712 with [
    push2 ⟨2740⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  have rd2750₀ := evm_run rd2740 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and]
  have hsolcMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have hzmask : UInt256.land (auctionTransferOwnershipArgWord I) solcAddrMask = ⟨0⟩ := by
    rw [solcAddrMask_clean hcanon, hzero]
  have rd2750 := rd2750₀
  rw [hsolcMask] at rd2750
  rw [hzmask] at rd2750
  have rd2758 := evm_run rd2750 with [
    push2 ⟨2841⟩, jumpiNT (by decide),
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov)]
  have rd2762 := rd2758.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd2781 := evm_run rd2762 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 6 (solcErrorStringMem0 solcFreePtrMem) (UInt256.ofNat 5)
      (by decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (solcErrorStringMem1 solcFreePtrMem) (UInt256.ofNat 6)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨38⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 3 (solcErrorStringMem2 ⟨38⟩ solcFreePtrMem) (UInt256.ofNat 7)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd2814 := rd2781.pushConst auctionNewOwnerZeroStringWord1
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd2819 := evm_run rd2814 with [
    push1 ⟨68⟩, dup3, add,
    raw mstore 3 (solcErrorStringMem3 ⟨38⟩ auctionNewOwnerZeroStringWord1 solcFreePtrMem)
      (UInt256.ofNat 8) (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd2826 := rd2819.pushConst (⟨0x646472657373⟩ : UInt256)
    (width := 6) (op := .PUSH6) (by decide) (by decide) (by evm_ov)
  have rd2829₀ := evm_run rd2826 with [push1 ⟨208⟩, shl]
  have rd2829 := rd2829₀
  rw [show UInt256.shiftLeft (⟨0x646472657373⟩ : UInt256) ⟨208⟩ =
      auctionNewOwnerZeroStringWord2 by rfl] at rd2829
  have rd2837₀ := evm_run rd2829 with [
    push1 ⟨100⟩, dup3, add,
    raw mstore 3 (auctionNewOwnerZeroStringMem4 solcFreePtrMem)
      (UInt256.ofNat 9) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨132⟩, add]
  have rd2837 := rd2837₀
  rw [show (⟨132⟩ : UInt256) + ⟨128⟩ = ⟨260⟩ by decide] at rd2837
  have rd994 := evm_run rd2837 with [push2 ⟨994⟩, jump (by jump_dest)]
  have rd1001₀ := evm_run rd994 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by decide)
      mem_cost auctionNewOwnerZeroStringMem4_mload64 (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd1001 := rd1001₀
  rw [show UInt256.sub (⟨260⟩ : UInt256) ⟨128⟩ = ⟨132⟩ by decide] at rd1001
  exact evm_run rd1001 with [raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem auctionTransferOwnershipBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (_hcode : I.code = auctionBytecode)
    (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (_hsel : selIs I (auctionSelBytes 19))
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (auctionSelBytes 19) rfl _hsel
  have hdispatch := auctionDispatch_transferOwnership _hsel
  have hreach := auctionReachTransferOwnershipBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    _hcode hsz4 _hsize _hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz36 : 36 ≤ I.calldata.size
    · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
      · by_cases hcanon : (auctionTransferOwnershipArgWord I).toNat < EVM.addressModulus
        · let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
          have hownerWord :
              auctionSlotWord ⟨151⟩ σ_evm I = auctionSlotWord ⟨151⟩ σ_solm I :=
            accountMapEquiv_storage_findD _hAccounts I.codeOwner ⟨151⟩ ⟨0⟩
          have hdecode := auctionDecode_transferOwnership (I := I) hsz36 hbig hcanon
          by_cases howner :
              UInt256.land (auctionSlotWord ⟨151⟩ σ_evm I) solcAddrMask =
                auctionSourceWord I
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
            by_cases hzero : auctionTransferOwnershipArgWord I = ⟨0⟩
            · have hbody := auctionTransferOwnershipBodyReverts_zero evmS I
                (by simp only [evmS, initState]; exact hwv) hownerSolm hzero
              exact (auctionX_transferOwnership_revert_zero (g := Sat256.ofUInt256 g)
                  hwv hsz36 _hsize hbig hcanon howner hzero hreach)
                |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
            · have hbody := auctionTransferOwnershipBodyReturns evmS I
                (by simp only [evmS, initState]; exact hwv) hcanon hownerSolm hzero
              have hpostAccounts :
                  accountMapEquiv (auctionTransferOwnershipPostMap σ_evm I)
                    (auctionTransferOwnershipPostState evmS I).accountMap := by
                have hpostWord :
                    auctionSetOwnerWord (Option.option ⟨0⟩
                        (fun self => self.lookupStorage ⟨151⟩)
                        (Batteries.RBMap.find? σ_solm I.codeOwner))
                        (auctionTransferOwnershipArgWord I) =
                      auctionSetOwnerWord (auctionSlotWord ⟨151⟩ σ_evm I)
                        (auctionTransferOwnershipArgWord I) := by
                  have h := congrArg
                    (fun w => auctionSetOwnerWord w (auctionTransferOwnershipArgWord I))
                    hownerWord
                  symm
                  simpa [auctionSlotWord, Account.lookupStorage] using h
                have hstore := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨151⟩
                  (auctionSetOwnerWord (auctionSlotWord ⟨151⟩ σ_evm I)
                    (auctionTransferOwnershipArgWord I)) _hAccounts
                simpa [auctionTransferOwnershipPostMap, auctionTransferOwnershipPostState,
                  auctionSetOwnerPostMap, auctionSetOwnerPostState, evmS, initState,
                  storageStore_accountMap, auctionSlotWord, Solm.EVM.storageLoad,
                  State.lookupAccount, hpostWord] using hstore
              exact (auctionX_transferOwnership_success (g := Sat256.ofUInt256 g)
                  _hperm hwv hsz36 _hsize hbig hcanon howner hzero hreach)
                |>.reEquivExecutionGenAccountMapEquiv _hcode hdispatch hdecode hbody
                  (by simp [auctionTransferOwnershipPostState, auctionSetOwnerPostState, evmS,
                    initState, storageStore_createdAccounts])
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
                simpa [evmS, initState, auctionSlotWord, Solm.EVM.storageLoad,
                  State.lookupAccount, auctionSourceWord] using h
              simpa [hownerWord] using hmap
            have hbody := auctionTransferOwnershipBodyReverts_owner evmS I
              (by simp only [evmS, initState]; exact hwv) hownerSolm
            exact (auctionX_transferOwnership_revert_owner (g := Sat256.ofUInt256 g)
                hwv hsz36 _hsize hbig hcanon howner hreach)
              |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
        · exact (auctionTransferOwnershipX_decodeRevert_noncanon (g := Sat256.ofUInt256 g)
              hwv hsz36 _hsize hbig hcanon hreach)
            |>.reEquivDecodingFailed _hcode hdispatch
              (auctionDecode_transferOwnership_none_noncanon (I := I) hsz36 hbig hcanon)
      · have hbigLe : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
        exact (auctionTransferOwnershipX_decodeRevert_huge (g := Sat256.ofUInt256 g)
            hwv _hsize hbigLe hreach)
          |>.reEquivDecodingFailed _hcode hdispatch
            (auctionDecode_transferOwnership_none_huge (I := I) hbigLe)
    · have hshort : I.calldata.size < 36 := by omega
      exact (auctionTransferOwnershipX_decodeRevert_short (g := Sat256.ofUInt256 g)
          hwv hsz4 _hsize hshort hreach)
        |>.reEquivDecodingFailed _hcode hdispatch
          (auctionDecode_transferOwnership_none_short (I := I) hshort)
  · by_cases hsz36 : 36 ≤ I.calldata.size
    · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
      · by_cases hcanon : (auctionTransferOwnershipArgWord I).toNat < EVM.addressModulus
        · have hdecode := auctionDecode_transferOwnership (I := I) hsz36 hbig hcanon
          have hbody := auctionTransferOwnershipBodyReverts_callvalue
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (by simpa [initState] using hwv)
          exact (auctionX_transferOwnership_callvalue_ne hreach hwv)
            |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
        · exact (auctionX_transferOwnership_callvalue_ne hreach hwv)
            |>.reEquivDecodingFailed _hcode hdispatch
              (auctionDecode_transferOwnership_none_noncanon (I := I) hsz36 hbig hcanon)
      · have hbigLe : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
        exact (auctionX_transferOwnership_callvalue_ne hreach hwv)
          |>.reEquivDecodingFailed _hcode hdispatch
            (auctionDecode_transferOwnership_none_huge (I := I) hbigLe)
    · have hshort : I.calldata.size < 36 := by omega
      exact (auctionX_transferOwnership_callvalue_ne hreach hwv)
        |>.reEquivDecodingFailed _hcode hdispatch
          (auctionDecode_transferOwnership_none_short (I := I) hshort)

end Auction
