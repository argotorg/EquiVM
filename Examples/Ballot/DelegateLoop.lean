import Examples.Ballot.Delegate

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Ballot

/-! ## Parameterized helpers for the `delegate(address)` loop current word -/

abbrev delegateCurrentToValue (w : UInt256) : Value :=
  .address (AccountAddress.ofNat w.toNat)

abbrev delegateCurrentStore (w : UInt256) : Store :=
  (∅ : Store).insert "to" (delegateCurrentToValue w)

abbrev delegateCurrentWithSenderStore (I : ExecutionEnv) (w : UInt256) : Store :=
  (delegateCurrentStore w).insert "sender" (.storageRef (delegateSenderRef I) voterStructTy)

def delegateCurrentVoterRef (w : UInt256) : EvaledStorageRef :=
  { base := "voters", steps := [.mindex (.address (AccountAddress.ofNat w.toNat))] }

def delegateCurrentVoterFieldRef (w : UInt256) (field : Ident) : EvaledStorageRef :=
  { base := "voters",
    steps := [.mindex (.address (AccountAddress.ofNat w.toNat)), .field field] }

abbrev delegateCurrentWithDelegateStore (I : ExecutionEnv) (w : UInt256) : Store :=
  (delegateCurrentWithSenderStore I w).insert "delegate_"
    (.storageRef (delegateCurrentVoterRef w) voterStructTy)

noncomputable def delegateCurrentLoopMem (I : ExecutionEnv) (w : UInt256) : ByteArray :=
  delegateLoopHashMem w (delegateSourceWord I)

theorem delegateCurrentStore_to (w : UInt256) :
    (delegateCurrentStore w).get? "to" = some (delegateCurrentToValue w) := by
  simp [delegateCurrentStore]

theorem delegateCurrentWithSenderStore_to (I : ExecutionEnv) (w : UInt256) :
    (delegateCurrentWithSenderStore I w).get? "to" =
      some (delegateCurrentToValue w) := by
  unfold delegateCurrentWithSenderStore
  rw [store_get_ne (delegateCurrentStore w) (.storageRef (delegateSenderRef I) voterStructTy)
    (by decide), delegateCurrentStore_to]

theorem delegateCurrentWithDelegateStore_to (I : ExecutionEnv) (w : UInt256) :
    (delegateCurrentWithDelegateStore I w).get? "to" =
      some (delegateCurrentToValue w) := by
  unfold delegateCurrentWithDelegateStore
  rw [store_get_ne (delegateCurrentWithSenderStore I w)
    (.storageRef (delegateCurrentVoterRef w) voterStructTy) (by decide),
    delegateCurrentWithSenderStore_to]

def delegateCurrentVoterPackedCurrent (evm : EVM.State) (w : UInt256) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (delegateVoterPackedSlot w)

abbrev delegateCurrentVoterDelegateWordCurrent (evm : EVM.State) (w : UInt256) : UInt256 :=
  UInt256.land (UInt256.div (delegateCurrentVoterPackedCurrent evm w) ⟨256⟩) solcAddrMask

theorem delegateCurrentVoterDelegateWordCurrent_init {cA gh bl σ σ₀ A I} {g : Sat256}
    {w : UInt256} :
    delegateCurrentVoterDelegateWordCurrent (initState cA gh bl σ σ₀ g A I) w =
      delegateVoterDelegateWord σ I w := by
  rfl

abbrev delegateCurrentNextValue (evm : EVM.State) (w : UInt256) : Value :=
  .address (AccountAddress.ofNat (delegateCurrentVoterDelegateWordCurrent evm w).toNat)

abbrev delegateCurrentNextStore (evm : EVM.State) (I : ExecutionEnv) (w : UInt256) : Store :=
  (delegateCurrentWithSenderStore I w).insert "to" (delegateCurrentNextValue evm w)

theorem delegateCurrentNextStore_to (evm : EVM.State) (I : ExecutionEnv) (w : UInt256) :
    (delegateCurrentNextStore evm I w).get? "to" = some (delegateCurrentNextValue evm w) := by
  simp [delegateCurrentNextStore]

theorem delegateCurrentDelegateAddress_ne_zero (evm : EVM.State) (w : UInt256)
    (hdelegate : delegateCurrentVoterDelegateWordCurrent evm w ≠ ⟨0⟩) :
    AccountAddress.ofNat (delegateCurrentVoterDelegateWordCurrent evm w).toNat ≠
      AccountAddress.ofNat 0 := by
  intro haddr
  apply hdelegate
  apply u256_inj
  have hval := congrArg Fin.val haddr
  unfold AccountAddress.ofNat at hval
  rw [Fin.val_ofNat, Fin.val_ofNat] at hval
  rw [Nat.mod_eq_of_lt (by
    exact solcAddrMask_result_canonical
      (UInt256.div (delegateCurrentVoterPackedCurrent evm w) ⟨256⟩))] at hval
  exact hval

theorem delegateWord_eq_source_of_address_eq_source {I : ExecutionEnv} {x : UInt256}
    (hcanon : x.toNat < EVM.addressModulus)
    (haddr : AccountAddress.ofNat x.toNat = I.source) :
    x = delegateSourceWord I := by
  apply u256_inj
  have hval := congrArg Fin.val haddr
  unfold AccountAddress.ofNat at hval
  rw [Fin.val_ofNat] at hval
  rw [Nat.mod_eq_of_lt (by
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)] at hval
  rw [delegateSourceWord_toNat]
  exact hval

theorem evalExpr_delegate_current_to (evm : EVM.State) (I : ExecutionEnv) (w : UInt256) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateCurrentWithSenderStore I w }
      evm (.var "to") = .ok (delegateCurrentToValue w) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable
      ((delegateCurrentWithSenderStore I w).get? "to") = .ok (delegateCurrentToValue w)
  rw [delegateCurrentWithSenderStore_to]
  rfl

theorem evalStorageRef_delegate_current_voterField (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) (field : Ident) :
    evalStorageRef ballotConfig { contract := ballotContract, locals := delegateCurrentWithSenderStore I w }
      evm (voterF (.var "to") field) = .ok (delegateCurrentVoterFieldRef w field) := by
  simp only [evalStorageRef, evalStorageRefSteps.eq_def, evalStorageRefStep.eq_def, voterF,
    evalExpr_delegate_current_to evm I w, delegateCurrentToValue, valueToKey?,
    EvalResult.ofOption, EvalResult.bind, bind, pure, List.nil_append]
  simp [delegateCurrentVoterFieldRef]

theorem resolveStorageRef_delegate_current_voterDelegate (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) :
    resolveStorageRef? ballotConfig { contract := ballotContract, locals := delegateCurrentWithSenderStore I w }
      evm (voterF (.var "to") "delegate") =
        .ok (delegateCurrentVoterFieldRef w "delegate", .elem .address) := by
  exact resolveStorageRef?_ok
    (hbase := by simp [delegateCurrentWithSenderStore, delegateCurrentStore, voterF])
    (her := evalStorageRef_delegate_current_voterField evm I w "delegate")
    (hty := by
      simp [delegateCurrentVoterFieldRef, storageTypeAt?, storageTypeStep?, ballotContract,
        ballotStorageDecls, voterStructTy, addrSt])

theorem evalExpr_delegate_current_voter_delegate (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateCurrentWithSenderStore I w }
      evm (.storage (voterF (.var "to") "delegate")) =
        .ok (delegateCurrentNextValue evm w) := by
  have hresolve := resolveStorageRef_delegate_current_voterDelegate evm I w
  have hread :
      readStorage? ballotConfig evm (delegateCurrentVoterFieldRef w "delegate") (.elem .address) =
        .ok (delegateCurrentNextValue evm w) := by
    rw [readStorage?_elem (hloc := by rfl)]
    change EvalResult.ok (storageLocLoad evm
        { slot := delegateVoterPackedSlot w, offset := 1, size := 20,
          hbound := _, type := .address }) =
      EvalResult.ok (delegateCurrentNextValue evm w)
    rw [storageLocLoad_address_offset1]
    simp [delegateCurrentNextValue, delegateCurrentVoterDelegateWordCurrent,
      delegateCurrentVoterPackedCurrent]
  rw [evalExpr?]
  simp only [hresolve, hread, bind, EvalResult.bind]

theorem evalExpr_delegate_current_loop_done (evm : EVM.State) (I : ExecutionEnv) (w : UInt256)
    (hdelegate : delegateCurrentVoterDelegateWordCurrent evm w = ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateCurrentWithSenderStore I w }
      evm (.binary .ne (.storage (voterF (.var "to") "delegate")) zeroAddr) =
        .ok (.bool false) := by
  have hstorage := evalExpr_delegate_current_voter_delegate evm I w
  simp [evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure, hstorage, zeroAddr,
    evalBinaryOp?, hdelegate, addrSt, castValue?]

theorem evalExpr_delegate_current_loop_continues (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) (hdelegate : delegateCurrentVoterDelegateWordCurrent evm w ≠ ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateCurrentWithSenderStore I w }
      evm (.binary .ne (.storage (voterF (.var "to") "delegate")) zeroAddr) =
        .ok (.bool true) := by
  have hstorage := evalExpr_delegate_current_voter_delegate evm I w
  have haddr := delegateCurrentDelegateAddress_ne_zero evm w hdelegate
  simp [evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure, hstorage, zeroAddr,
    evalBinaryOp?, haddr, addrSt, castValue?]

theorem assign_delegate_current_to_next (evm : EVM.State) (I : ExecutionEnv) (w : UInt256) :
    assignStorageRef? ballotConfig
      { contract := ballotContract, locals := delegateCurrentWithSenderStore I w } evm
      .localVar ({ base := "to" } : StorageRef) (delegateCurrentNextValue evm w) =
        .ok ({ contract := ballotContract, locals := delegateCurrentNextStore evm I w }, evm) := by
  have hget :
      (delegateCurrentWithSenderStore I w)["to"]? = some (delegateCurrentToValue w) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact delegateCurrentWithSenderStore_to I w
  simp [assignStorageRef?, updateLocalPath?, delegateCurrentNextStore, EvalResult.bind,
    bind, pure]

theorem evalExpr_delegate_current_next_ne_sender_true (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) (hsrc : evm.executionEnv.source = I.source)
    (hnotSender : delegateCurrentVoterDelegateWordCurrent evm w ≠ delegateSourceWord I) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateCurrentNextStore evm I w }
      evm (.binary .ne (.var "to") sender) = .ok (.bool true) := by
  have haddr :
      AccountAddress.ofNat (delegateCurrentVoterDelegateWordCurrent evm w).toNat ≠
        evm.executionEnv.source := by
    intro h
    apply hnotSender
    apply delegateWord_eq_source_of_address_eq_source
      (solcAddrMask_result_canonical (UInt256.div (delegateCurrentVoterPackedCurrent evm w) ⟨256⟩))
    simpa [hsrc] using h
  have htoExpr :
      evalExpr? ballotConfig { contract := ballotContract, locals := delegateCurrentNextStore evm I w }
        evm (.var "to") = .ok (delegateCurrentNextValue evm w) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((delegateCurrentNextStore evm I w).get? "to") = .ok (delegateCurrentNextValue evm w)
    rw [delegateCurrentNextStore_to]
    rfl
  have hsenderExpr :
      evalExpr? ballotConfig { contract := ballotContract, locals := delegateCurrentNextStore evm I w }
        evm sender = .ok (.address evm.executionEnv.source) := by
    unfold sender
    rw [evalExpr?]
    rfl
  simpa [evalExpr?, EvalResult.bind, bind, htoExpr, hsenderExpr, delegateCurrentNextValue,
    evalBinaryOp?] using haddr

theorem evalExpr_delegate_current_next_ne_sender_false (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) (hsrc : evm.executionEnv.source = I.source)
    (hSender : delegateCurrentVoterDelegateWordCurrent evm w = delegateSourceWord I) :
    evalExpr? ballotConfig { contract := ballotContract, locals := delegateCurrentNextStore evm I w }
      evm (.binary .ne (.var "to") sender) = .ok (.bool false) := by
  have haddr :
      AccountAddress.ofNat (delegateCurrentVoterDelegateWordCurrent evm w).toNat =
        evm.executionEnv.source := by
    rw [hSender]
    simpa [hsrc] using delegateSource_ofNat I
  have htoExpr :
      evalExpr? ballotConfig { contract := ballotContract, locals := delegateCurrentNextStore evm I w }
        evm (.var "to") = .ok (delegateCurrentNextValue evm w) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((delegateCurrentNextStore evm I w).get? "to") = .ok (delegateCurrentNextValue evm w)
    rw [delegateCurrentNextStore_to]
    rfl
  have hsenderExpr :
      evalExpr? ballotConfig { contract := ballotContract, locals := delegateCurrentNextStore evm I w }
        evm sender = .ok (.address evm.executionEnv.source) := by
    unfold sender
    rw [evalExpr?]
    rfl
  simp [evalExpr?, EvalResult.bind, bind, htoExpr, hsenderExpr, delegateCurrentNextValue, haddr,
    evalBinaryOp?]

theorem ballotDelegateSolm_loopExitCurrent (evm : EVM.State) (I : ExecutionEnv) (w : UInt256)
    (hdelegate : delegateCurrentVoterDelegateWordCurrent evm w = ⟨0⟩) :
    ExecStmt ballotConfig { contract := ballotContract, locals := delegateCurrentWithSenderStore I w }
      evm
      (.while (.binary .ne (.storage (voterF (.var "to") "delegate")) zeroAddr)
        [ .assign .localVar { base := "to" } (.storage (voterF (.var "to") "delegate")),
          .require (.binary .ne (.var "to") sender) ])
      (.ok { contract := ballotContract, locals := delegateCurrentWithSenderStore I w } evm) := by
  exact ExecStmt.whileFalse (evalExpr_delegate_current_loop_done evm I w hdelegate)

theorem ballotDelegateSolm_loopContinueBodyCurrent (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) (hsrc : evm.executionEnv.source = I.source)
    (hnotSender : delegateCurrentVoterDelegateWordCurrent evm w ≠ delegateSourceWord I) :
    ExecBlock ballotConfig { contract := ballotContract, locals := delegateCurrentWithSenderStore I w }
      evm
      [ .assign .localVar { base := "to" } (.storage (voterF (.var "to") "delegate")),
        .require (.binary .ne (.var "to") sender) ]
      (.ok { contract := ballotContract, locals := delegateCurrentNextStore evm I w } evm) := by
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_delegate_current_voter_delegate evm I w)
      (assign_delegate_current_to_next evm I w))
    (ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_delegate_current_next_ne_sender_true evm I w hsrc hnotSender))
      ExecBlock.nil)

theorem ballotDelegateSolm_loopRevertSenderCurrent (evm : EVM.State) (I : ExecutionEnv)
    (w : UInt256) (hsrc : evm.executionEnv.source = I.source)
    (hdelegate : delegateCurrentVoterDelegateWordCurrent evm w ≠ ⟨0⟩)
    (hSender : delegateCurrentVoterDelegateWordCurrent evm w = delegateSourceWord I) :
    ExecStmt ballotConfig { contract := ballotContract, locals := delegateCurrentWithSenderStore I w }
      evm
      (.while (.binary .ne (.storage (voterF (.var "to") "delegate")) zeroAddr)
        [ .assign .localVar { base := "to" } (.storage (voterF (.var "to") "delegate")),
          .require (.binary .ne (.var "to") sender) ])
      .reverted := by
  refine ExecStmt.whileRevert (evalExpr_delegate_current_loop_continues evm I w hdelegate) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_delegate_current_voter_delegate evm I w)
      (assign_delegate_current_to_next evm I w))
      (ExecBlock.consRevert
      (ExecStmt.requireFalse
        (evalExpr_delegate_current_next_ne_sender_false evm I w hsrc hSender)))

/-! ### Loop-cycle string revert tail -/

def delegateLoopFoundStringWord : UInt256 :=
  ⟨0x466f756e64206c6f6f7020696e2064656c65676174696f6e2e00000000000000⟩

noncomputable def delegateLoopFoundErrorMem0 (toWord senderWord : UInt256) : ByteArray :=
  (UInt256.toByteArray delegateErrorSelector).write 0
    (delegateLoopHashMem toWord senderWord) 128 32

noncomputable def delegateLoopFoundErrorMem1 (toWord senderWord : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0
    (delegateLoopFoundErrorMem0 toWord senderWord) 132 32

noncomputable def delegateLoopFoundErrorMem2 (toWord senderWord : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨25⟩ : UInt256)).write 0
    (delegateLoopFoundErrorMem1 toWord senderWord) 164 32

noncomputable def delegateLoopFoundErrorMem3 (toWord senderWord : UInt256) : ByteArray :=
  (UInt256.toByteArray delegateLoopFoundStringWord).write 0
    (delegateLoopFoundErrorMem2 toWord senderWord) 196 32

theorem delegateLoopFoundErrorMem0_size (toWord senderWord : UInt256) :
    (delegateLoopFoundErrorMem0 toWord senderWord).size = 160 := by
  unfold delegateLoopFoundErrorMem0
  rw [toByteArray_write_eq _ _ _ (by rw [delegateLoopHashMem_size]; omega)
      (by rw [delegateLoopHashMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, delegateLoopHashMem_size, ByteArray_zeroes_size,
    show 128 - 96 = 32 from by norm_num,
    toByteArray_size]

theorem delegateLoopFoundErrorMem1_size (toWord senderWord : UInt256) :
    (delegateLoopFoundErrorMem1 toWord senderWord).size = 164 := by
  unfold delegateLoopFoundErrorMem1
  rw [write32_eq _ _ 132 (by rw [toByteArray_size])
      (by rw [delegateLoopFoundErrorMem0_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, delegateLoopFoundErrorMem0_size,
    toByteArray_size]
  omega

theorem delegateLoopFoundErrorMem2_size (toWord senderWord : UInt256) :
    (delegateLoopFoundErrorMem2 toWord senderWord).size = 196 := by
  unfold delegateLoopFoundErrorMem2
  rw [write32_eq _ _ 164 (by rw [toByteArray_size])
      (by rw [delegateLoopFoundErrorMem1_size]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, delegateLoopFoundErrorMem1_size,
    toByteArray_size]
  omega

theorem delegateLoopFoundErrorMem3_size (toWord senderWord : UInt256) :
    (delegateLoopFoundErrorMem3 toWord senderWord).size = 228 := by
  unfold delegateLoopFoundErrorMem3
  rw [write32_eq _ _ 196 (by rw [toByteArray_size])
      (by rw [delegateLoopFoundErrorMem2_size]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, delegateLoopFoundErrorMem2_size,
    toByteArray_size]
  omega

theorem delegateLoopFoundErrorMem0_read64 (toWord senderWord : UInt256) :
    (delegateLoopFoundErrorMem0 toWord senderWord).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold delegateLoopFoundErrorMem0
  rw [toByteArray_write_eq _ _ _ (by rw [delegateLoopHashMem_size]; omega)
      (by rw [delegateLoopHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, delegateLoopHashMem_size,
        ByteArray_zeroes_size,
        show 128 - 96 = 32 from by norm_num,
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, delegateLoopHashMem_size, ByteArray_zeroes_size,
      show 128 - 96 = 32 from by norm_num]
    omega)]
  rw [extract_append_left _ _ _ _ (by rw [delegateLoopHashMem_size])]
  rw [← readWithPadding_eq_extract _ 64 (by rw [delegateLoopHashMem_size])]
  exact delegateLoopHashMem_read64 toWord senderWord

theorem delegateLoopFoundErrorMem1_read64 (toWord senderWord : UInt256) :
    (delegateLoopFoundErrorMem1 toWord senderWord).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold delegateLoopFoundErrorMem1
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
      (by rw [delegateLoopFoundErrorMem0_size]; omega) (by omega),
    delegateLoopFoundErrorMem0_read64]

theorem delegateLoopFoundErrorMem2_read64 (toWord senderWord : UInt256) :
    (delegateLoopFoundErrorMem2 toWord senderWord).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold delegateLoopFoundErrorMem2
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
      (by rw [delegateLoopFoundErrorMem1_size]) (by omega),
    delegateLoopFoundErrorMem1_read64]

theorem delegateLoopFoundErrorMem3_read64 (toWord senderWord : UInt256) :
    (delegateLoopFoundErrorMem3 toWord senderWord).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold delegateLoopFoundErrorMem3
  rw [write32_read_below _ _ 196 64 (by rw [toByteArray_size])
      (by rw [delegateLoopFoundErrorMem2_size]) (by omega),
    delegateLoopFoundErrorMem2_read64]

theorem delegateLoopFoundErrorMem3_mload64 (toWord senderWord : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (delegateLoopFoundErrorMem3 toWord senderWord).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((delegateLoopFoundErrorMem3 toWord senderWord).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [delegateLoopFoundErrorMem3_size]; decide) (by decide)
    (delegateLoopFoundErrorMem3_read64 toWord senderWord)

set_option maxHeartbeats 4000000 in
theorem ballotDelegateX_loopFoundRevert1058 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel w : UInt256} {R : List UInt256} {k C : ℕ}
    (h : RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1058⟩ R
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hov : R.length + 4 ≤ 1024) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd1061 := evm_run h with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost (by
        unfold delegateCurrentLoopMem
        exact delegateLoopHashMem_mload64 w (delegateSourceWord I))
      (by decide) (by evm_ov) ]
  have rd1065 := rd1061.pushConst ⟨0x461bcd⟩ (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd1084 := evm_run rd1065 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 6 (delegateLoopFoundErrorMem0 w (delegateSourceWord I)) (UInt256.ofNat 5)
      (by decide) mem_cost (by
        unfold delegateCurrentLoopMem
        rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (delegateLoopFoundErrorMem1 w (delegateSourceWord I)) (UInt256.ofNat 6)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨25⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 3 (delegateLoopFoundErrorMem2 w (delegateSourceWord I)) (UInt256.ofNat 7)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1117 := rd1084.pushConst delegateLoopFoundStringWord (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd507 := evm_run rd1117 with [
    push1 ⟨68⟩, dup3, add,
    raw mstore 3 (delegateLoopFoundErrorMem3 w (delegateSourceWord I)) (UInt256.ofNat 8)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨100⟩, add, push2 ⟨507⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide)
      mem_cost (delegateLoopFoundErrorMem3_mload64 w (delegateSourceWord I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]
  exact rd507

/-! ### EVM loop segment at pc 972 -/

theorem ballotDelegateX_loopExitFrom972 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel w : UInt256}
    (hcanon : w.toNat < EVM.addressModulus)
    (hdelegate : delegateVoterDelegateWord σ I w = ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨972⟩
      [delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateHashMem (delegateSourceWord I)) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1134⟩
      [delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd972⟩ := hreach
  have rd987 := evm_run rd972 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, dup2, and,
    push0, swap1, dup2 ]
  have rd995 := evm_run rd987 with [
    raw mstore 0 (delegateLoopKeyMem w (delegateSourceWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by
        change (UInt256.toByteArray (UInt256.land solcAddrMask w)).write 0
            (delegateHashMem (delegateSourceWord I)) 0 32 =
          delegateLoopKeyMem w (delegateSourceWord I)
        rw [u256_land_comm solcAddrMask w]
        rw [solcAddrMask_clean hcanon]
        rfl) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩, dup2, swap1,
    raw mstore 0 (delegateCurrentLoopMem I w)
      (UInt256.ofNat 3) (by decide) mem_cost (by
        unfold delegateCurrentLoopMem
        rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1, swap2,
    raw keccak256 0 (delegateVoterSlot w) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by
        unfold delegateCurrentLoopMem
        exact delegateLoopVoterKeccakSlot w (delegateSourceWord I) hcanon)
      (by decide) (by evm_ov),
    add ]
  obtain ⟨_, _, rd1002₀⟩ := rd995.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1002⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1002⟩
      [delegateVoterPackedWord σ I w, solcAddrMask, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      unfold delegateCurrentLoopMem
      simpa [delegateVoterPackedWord, delegateVoterPackedSlot, solcAddrMask, initState,
        u256_add_comm] using rd1002₀⟩
  have rd1005 := evm_run rd1002 with [push2 ⟨256⟩, swap1]
  have rd1006 := RD.div rd1005 (by native_decide) (by norm_num)
  have rd1008 := evm_run rd1006 with [and, iszero]
  have hzero :
      UInt256.isZero
          (UInt256.land (UInt256.div (delegateVoterPackedWord σ I w) ⟨256⟩) solcAddrMask) =
        ⟨1⟩ := by
    change UInt256.isZero (delegateVoterDelegateWord σ I w) = ⟨1⟩
    rw [hdelegate]
    decide
  have rd1008' := rd1008
  rw [hzero] at rd1008'
  exact ⟨_, _, evm_run rd1008' with [push2 ⟨1134⟩, jumpiT (by decide) (by jump_dest)]⟩

theorem ballotDelegateX_loopContinueFrom972 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel w : UInt256}
    (hcanon : w.toNat < EVM.addressModulus)
    (hnext : delegateVoterDelegateWord σ I w ≠ ⟨0⟩)
    (hnotSender : delegateVoterDelegateWord σ I w ≠ delegateSourceWord I)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨972⟩
      [delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateHashMem (delegateSourceWord I)) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨972⟩
      [delegateSenderSlot I, delegateVoterDelegateWord σ I w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd972⟩ := hreach
  have rd987 := evm_run rd972 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, dup2, and,
    push0, swap1, dup2 ]
  have rd995 := evm_run rd987 with [
    raw mstore 0 (delegateLoopKeyMem w (delegateSourceWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by
        change (UInt256.toByteArray (UInt256.land solcAddrMask w)).write 0
            (delegateHashMem (delegateSourceWord I)) 0 32 =
          delegateLoopKeyMem w (delegateSourceWord I)
        rw [u256_land_comm solcAddrMask w]
        rw [solcAddrMask_clean hcanon]
        rfl) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩, dup2, swap1,
    raw mstore 0 (delegateCurrentLoopMem I w)
      (UInt256.ofNat 3) (by decide) mem_cost (by
        unfold delegateCurrentLoopMem
        rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1, swap2,
    raw keccak256 0 (delegateVoterSlot w) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by
        unfold delegateCurrentLoopMem
        exact delegateLoopVoterKeccakSlot w (delegateSourceWord I) hcanon)
      (by decide) (by evm_ov),
    add ]
  obtain ⟨_, _, rd1002₀⟩ := rd995.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1002⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1002⟩
      [delegateVoterPackedWord σ I w, solcAddrMask, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      unfold delegateCurrentLoopMem
      simpa [delegateVoterPackedWord, delegateVoterPackedSlot, solcAddrMask, initState,
        u256_add_comm] using rd1002₀⟩
  have rd1005 := evm_run rd1002 with [push2 ⟨256⟩, swap1]
  have rd1006 := RD.div rd1005 (by native_decide) (by norm_num)
  have rd1008 := evm_run rd1006 with [and, iszero]
  have hnonzero :
      UInt256.isZero
          (UInt256.land (UInt256.div (delegateVoterPackedWord σ I w) ⟨256⟩) solcAddrMask) =
        ⟨0⟩ := by
    change UInt256.isZero (delegateVoterDelegateWord σ I w) = ⟨0⟩
    exact isZero_eq_zero_of_ne hnext
  have rd1008' := rd1008
  rw [hnonzero] at rd1008'
  have rd1013 := evm_run rd1008' with [push2 ⟨1134⟩, jumpiNT (by decide)]
  have rd1041 := evm_run rd1013 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap2, dup3, and,
    push0, swap1, dup2,
    raw mstore 0 (delegateCurrentLoopMem I w)
      (UInt256.ofNat 3) (by decide) mem_cost (by
        change (UInt256.toByteArray (UInt256.land solcAddrMask w)).write 0
            (delegateCurrentLoopMem I w) 0 32 = delegateCurrentLoopMem I w
        rw [u256_land_comm solcAddrMask w]
        rw [solcAddrMask_clean hcanon]
        unfold delegateCurrentLoopMem
        exact delegateLoopHashMem_writeKey w (delegateSourceWord I))
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩, dup2, swap1,
    raw mstore 0 (delegateCurrentLoopMem I w)
      (UInt256.ofNat 3) (by decide) mem_cost (by
        unfold delegateCurrentLoopMem
        exact delegateLoopHashMem_writeBase w (delegateSourceWord I))
      (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1, swap2,
    raw keccak256 0 (delegateVoterSlot w) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by
        unfold delegateCurrentLoopMem
        exact delegateLoopVoterKeccakSlot w (delegateSourceWord I) hcanon)
      (by decide) (by evm_ov),
    add ]
  obtain ⟨_, _, rd1042₀⟩ := rd1041.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1042⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1042⟩
      [delegateVoterPackedWord σ I w, delegateSenderSlot I, solcAddrMask, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      unfold delegateCurrentLoopMem
      simpa [delegateVoterPackedWord, delegateVoterPackedSlot, initState, u256_add_comm]
        using rd1042₀⟩
  have rd1045 := evm_run rd1042 with [push2 ⟨256⟩, swap1]
  have rd1046 := RD.div rd1045 (by native_decide) (by norm_num)
  have rd1054 := evm_run rd1046 with [swap1, swap2, and, swap1, caller, dup3, sub]
  have hdiff :
      UInt256.sub
          (UInt256.land solcAddrMask (UInt256.div (delegateVoterPackedWord σ I w) ⟨256⟩))
          (UInt256.ofNat I.source.val) ≠ ⟨0⟩ := by
    rw [u256_land_comm solcAddrMask (UInt256.div (delegateVoterPackedWord σ I w) ⟨256⟩)]
    change UInt256.sub (delegateVoterDelegateWord σ I w) (delegateSourceWord I) ≠ ⟨0⟩
    exact u256_sub_ne_zero_of_ne hnotSender
  have rd972next := evm_run rd1054 with [
    push2 ⟨1129⟩, jumpiT hdiff (by jump_dest),
    jumpdest, push2 ⟨972⟩, jump (by jump_dest) ]
  exact ⟨_, _, by
    simpa [delegateVoterDelegateWord,
      u256_land_comm solcAddrMask (UInt256.div (delegateVoterPackedWord σ I w) ⟨256⟩)]
      using rd972next⟩

set_option maxHeartbeats 4000000 in
theorem ballotDelegateX_loopSenderRevertTailFrom972 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel w : UInt256}
    (hcanon : w.toNat < EVM.addressModulus)
    (hnext : delegateVoterDelegateWord σ I w ≠ ⟨0⟩)
    (hcycle : delegateVoterDelegateWord σ I w = delegateSourceWord I)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨972⟩
      [delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateHashMem (delegateSourceWord I)) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ R k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1058⟩ R
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C ∧
      R.length + 4 ≤ 1024 := by
  obtain ⟨_, _, rd972⟩ := hreach
  have rd987 := evm_run rd972 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, dup2, and,
    push0, swap1, dup2 ]
  have rd995 := evm_run rd987 with [
    raw mstore 0 (delegateLoopKeyMem w (delegateSourceWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by
        change (UInt256.toByteArray (UInt256.land solcAddrMask w)).write 0
            (delegateHashMem (delegateSourceWord I)) 0 32 =
          delegateLoopKeyMem w (delegateSourceWord I)
        rw [u256_land_comm solcAddrMask w]
        rw [solcAddrMask_clean hcanon]
        rfl) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩, dup2, swap1,
    raw mstore 0 (delegateCurrentLoopMem I w)
      (UInt256.ofNat 3) (by decide) mem_cost (by
        unfold delegateCurrentLoopMem
        rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1, swap2,
    raw keccak256 0 (delegateVoterSlot w) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by
        unfold delegateCurrentLoopMem
        exact delegateLoopVoterKeccakSlot w (delegateSourceWord I) hcanon)
      (by decide) (by evm_ov),
    add ]
  obtain ⟨_, _, rd1002₀⟩ := rd995.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1002⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1002⟩
      [delegateVoterPackedWord σ I w, solcAddrMask, delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      unfold delegateCurrentLoopMem
      simpa [delegateVoterPackedWord, delegateVoterPackedSlot, solcAddrMask, initState,
        u256_add_comm] using rd1002₀⟩
  have rd1005 := evm_run rd1002 with [push2 ⟨256⟩, swap1]
  have rd1006 := RD.div rd1005 (by native_decide) (by norm_num)
  have rd1008 := evm_run rd1006 with [and, iszero]
  have hnonzero :
      UInt256.isZero
          (UInt256.land (UInt256.div (delegateVoterPackedWord σ I w) ⟨256⟩) solcAddrMask) =
        ⟨0⟩ := by
    change UInt256.isZero (delegateVoterDelegateWord σ I w) = ⟨0⟩
    exact isZero_eq_zero_of_ne hnext
  have rd1008' := rd1008
  rw [hnonzero] at rd1008'
  have rd1013 := evm_run rd1008' with [push2 ⟨1134⟩, jumpiNT (by decide)]
  have rd1041 := evm_run rd1013 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap2, dup3, and,
    push0, swap1, dup2,
    raw mstore 0 (delegateCurrentLoopMem I w)
      (UInt256.ofNat 3) (by decide) mem_cost (by
        change (UInt256.toByteArray (UInt256.land solcAddrMask w)).write 0
            (delegateCurrentLoopMem I w) 0 32 = delegateCurrentLoopMem I w
        rw [u256_land_comm solcAddrMask w]
        rw [solcAddrMask_clean hcanon]
        unfold delegateCurrentLoopMem
        exact delegateLoopHashMem_writeKey w (delegateSourceWord I))
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩, dup2, swap1,
    raw mstore 0 (delegateCurrentLoopMem I w)
      (UInt256.ofNat 3) (by decide) mem_cost (by
        unfold delegateCurrentLoopMem
        exact delegateLoopHashMem_writeBase w (delegateSourceWord I))
      (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1, swap2,
    raw keccak256 0 (delegateVoterSlot w) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by
        unfold delegateCurrentLoopMem
        exact delegateLoopVoterKeccakSlot w (delegateSourceWord I) hcanon)
      (by decide) (by evm_ov),
    add ]
  obtain ⟨_, _, rd1042₀⟩ := rd1041.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1042⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1042⟩
      [delegateVoterPackedWord σ I w, delegateSenderSlot I, solcAddrMask, ⟨156⟩, sel]
      (delegateCurrentLoopMem I w) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      unfold delegateCurrentLoopMem
      simpa [delegateVoterPackedWord, delegateVoterPackedSlot, initState, u256_add_comm]
        using rd1042₀⟩
  have rd1045 := evm_run rd1042 with [push2 ⟨256⟩, swap1]
  have rd1046 := RD.div rd1045 (by native_decide) (by norm_num)
  have rd1054 := evm_run rd1046 with [swap1, swap2, and, swap1, caller, dup3, sub]
  have hdiff :
      UInt256.sub
          (UInt256.land solcAddrMask (UInt256.div (delegateVoterPackedWord σ I w) ⟨256⟩))
          (UInt256.ofNat I.source.val) = ⟨0⟩ := by
    rw [u256_land_comm solcAddrMask (UInt256.div (delegateVoterPackedWord σ I w) ⟨256⟩)]
    change UInt256.sub (delegateVoterDelegateWord σ I w) (delegateSourceWord I) = ⟨0⟩
    rw [hcycle]
    exact u256_sub_self (delegateSourceWord I)
  have rd1054' := rd1054
  rw [hdiff] at rd1054'
  have rd1058 := evm_run rd1054' with [push2 ⟨1129⟩, jumpiNT (by decide)]
  exact ⟨_, _, _, rd1058, by simp⟩

theorem ballotDelegateX_loopSenderRevertFrom972 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel w : UInt256}
    (hcanon : w.toNat < EVM.addressModulus)
    (hnext : delegateVoterDelegateWord σ I w ≠ ⟨0⟩)
    (hcycle : delegateVoterDelegateWord σ I w = delegateSourceWord I)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨972⟩
      [delegateSenderSlot I, w, ⟨156⟩, sel]
      (delegateHashMem (delegateSourceWord I)) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨R, k, C, rd1058, hov⟩ :=
    ballotDelegateX_loopSenderRevertTailFrom972 (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel) (w := w)
      hcanon hnext hcycle hreach
  exact ballotDelegateX_loopFoundRevert1058 (sel := sel) (w := w) rd1058 hov

theorem ballotDelegateBodyReverts_loopSender (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (delegateSenderSlot I) ≠ ⟨0⟩)
    (hvoted : UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (delegateSenderPackedSlot I))
        ⟨255⟩ = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hnext : delegateCurrentVoterDelegateWordCurrent evm (delegateToWord I) ≠ ⟨0⟩)
    (hcycle : delegateCurrentVoterDelegateWordCurrent evm (delegateToWord I) =
      delegateSourceWord I) :
    ExecTransitionBody ballotConfig ballotContract evm (delegateStore I)
      delegateTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.letStorage (resolveStorageRef_delegate_sender evm I hsrc)) <|
        ExecBlock.consNormal (ExecStmt.requireTrue
          (evalExpr_delegate_sender_weight_zero_false evm I hweight)) <|
          ExecBlock.consNormal (ExecStmt.requireTrue
            (evalExpr_delegate_sender_not_voted_true evm I hvoted)) <|
            ExecBlock.consNormal (ExecStmt.requireTrue
              (evalExpr_delegate_to_ne_sender_true evm I hsrc hcanon hnotself)) <|
              ExecBlock.consRevert <| by
                simpa [delegateCurrentWithSenderStore, delegateCurrentStore,
                  delegateWithSenderStore, delegateStore, delegateCurrentToValue,
                  delegateToValue] using
                  ballotDelegateSolm_loopRevertSenderCurrent evm I (delegateToWord I) hsrc
                    hnext hcycle

theorem ballotDelegateLoopSenderRevertEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (delegateToWord I).toNat < EVM.addressModulus)
    (hweight : delegateSenderWeightWord σ_evm I ≠ ⟨0⟩)
    (hvoted : delegateSenderVotedByte σ_evm I = ⟨0⟩)
    (hnotself : delegateToWord I ≠ delegateSourceWord I)
    (hnext : delegateVoterDelegateWord σ_evm I (delegateToWord I) ≠ ⟨0⟩)
    (hcycle : delegateVoterDelegateWord σ_evm I (delegateToWord I) = delegateSourceWord I)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := ballotDispatch_delegate (cd := I.calldata) hsel
  have hdec := ballotDecode_delegate_ok (I := I) hsz36 hbig hcanon
  have hweightSolm : delegateSenderWeightWord σ_solm I ≠ ⟨0⟩ := by
    simpa [← delegateSenderWeightWord_accountMapEquiv hAccounts] using hweight
  have hvotedSolm : delegateSenderVotedByte σ_solm I = ⟨0⟩ := by
    simpa [← delegateSenderVotedByte_accountMapEquiv hAccounts] using hvoted
  have hnextSolm : delegateVoterDelegateWord σ_solm I (delegateToWord I) ≠ ⟨0⟩ := by
    simpa [← delegateVoterDelegateWord_accountMapEquiv hAccounts (delegateToWord I)]
      using hnext
  have hcycleSolm :
      delegateVoterDelegateWord σ_solm I (delegateToWord I) = delegateSourceWord I := by
    simpa [← delegateVoterDelegateWord_accountMapEquiv hAccounts (delegateToWord I)]
      using hcycle
  have hnextCurrent :
      delegateCurrentVoterDelegateWordCurrent
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (delegateToWord I) ≠
        ⟨0⟩ := by
    rw [delegateCurrentVoterDelegateWordCurrent_init]
    exact hnextSolm
  have hcycleCurrent :
      delegateCurrentVoterDelegateWordCurrent
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (delegateToWord I) =
        delegateSourceWord I := by
    rw [delegateCurrentVoterDelegateWordCurrent_init]
    exact hcycleSolm
  have hbody := ballotDelegateBodyReverts_loopSender
    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
    (by simp only [initState]; exact hwv)
    (by simp [initState])
    hcanon
    (by simpa [delegateSenderWeightWord, delegateSenderSlot, initState] using hweightSolm)
    (by
      change UInt256.land (delegateSenderPackedWord σ_solm I) ⟨255⟩ = ⟨0⟩
      rw [u256_land_comm (delegateSenderPackedWord σ_solm I) ⟨255⟩]
      exact hvotedSolm)
    hnotself
    hnextCurrent
    hcycleCurrent
  obtain ⟨_, _, rd972⟩ := ballotDelegateX_afterNotSelf (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (sel := sel) hsz36 hsize hbig hcanon hweight hvoted hnotself hreach
  exact (ballotDelegateX_loopSenderRevertFrom972 (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      (sel := sel) (w := delegateToWord I) hcanon hnext hcycle ⟨_, _, rd972⟩)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem ballotDelegateBodyCoreLoopFrontier
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcontinue :
      36 ≤ I.calldata.size →
      I.calldata.size < 2 ^ 255 + 4 →
      (delegateToWord I).toNat < EVM.addressModulus →
      delegateSenderWeightWord σ_evm I ≠ ⟨0⟩ →
      delegateSenderVotedByte σ_evm I = ⟨0⟩ →
      delegateToWord I ≠ delegateSourceWord I →
      I.perm = true →
      delegateVoterDelegateWord σ_evm I (delegateToWord I) ≠ ⟨0⟩ →
      delegateVoterDelegateWord σ_evm I (delegateToWord I) ≠ delegateSourceWord I →
      runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
        σ_evm σ_solm σ₀ g A I) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  refine ballotDelegateBodyCoreFrontier hcode hsize hperm hwv hsel hreach hAccounts ?_
  intro hsz36 hbig hcanon hweight hvoted hnotself hperm hnext
  by_cases hcycle : delegateVoterDelegateWord σ_evm I (delegateToWord I) = delegateSourceWord I
  · exact ballotDelegateLoopSenderRevertEquiv hcode hsize hwv hsel hsz36 hbig hcanon hweight
      hvoted hnotself hnext hcycle hreach hAccounts
  · exact hcontinue hsz36 hbig hcanon hweight hvoted hnotself hperm hnext hcycle

end Ballot
