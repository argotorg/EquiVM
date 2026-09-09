import Benchmarks.Dss.Clipper.Fallback

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

theorem clipperCountSelectorWord {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (clipperSelBytes 5)) :
    clipperSelWord I = clipperSelNat 5 := by
  simpa [clipperSelWord, solcSelectorWord, clipperSelNat] using
    solcSelectorWord_eq_of_beq I hsz 0x06 0x66 0x1a 0xbd (clipperSelNat 5)
      (by decide +native) (by simpa [clipperSelBytes, selIs] using hsel)

theorem clipperDispatch_count (v : ClipperImmutables) {I : ExecutionEnv}
    (hsel : selIs I (clipperSelBytes 5)) :
    dispatchMsg (contract v) I.calldata = some countTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract v)
    (pre := [activeTransition, bufTransition, calcTransition, chipTransition, chostTransition])
    (post :=
      [cuspTransition, denyTransition, dogTransition, fileUintTransition, fileAddressTransition,
        getStatusTransition, ilkTransition v, kickTransition v, kicksTransition, listTransition,
        redoTransition v, relyTransition, salesTransition, spotterTransition, stoppedTransition,
        tailTransition, takeTransition v, tipTransition, upchostTransition v, vatTransition v,
        vowTransition, wardsTransition, yankTransition v])
    (ti := countTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · rfl
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | hfalse
    · rw [selectorOf, activeSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, bufSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, calcSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, chipSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, chostSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · cases hfalse
  · rw [selectorOf, countSelectorBytes]
    simpa [clipperSelBytes] using hsel

theorem clipperDecode_count (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode (countTransition.params.map Param.name)
      (transitionSignature countTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode (config v).abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldataWithMode_empty_ok hsz

theorem clipperEvalActiveLength (v : ClipperImmutables) (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "active" = none) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.arrayLength .storage activeRef) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat)) := by
  let er : EvaledStorageRef := { base := "active", steps := [] }
  have her : evalStorageRef (config v)
      { contract := contract v, locals := locals } evm activeRef = .ok er := by
    unfold evalStorageRef activeRef
    simp only [evalStorageRefSteps]
    rfl
  have hty : storageTypeAt? (contract v).storage er = some (.dynamicArray uint256St) := by
    simp [er, storageTypeAt?, contract, storageDecls]
  have hres :
      resolveStorageRef? (config v)
        { contract := contract v, locals := locals } evm activeRef =
        .ok (er, .dynamicArray uint256St) :=
    resolveStorageRef?_ok hbase her hty
  rw [evalExpr?]
  simp only [hres, bind, EvalResult.bind]
  change readStorageArrayLength? (config v) evm er (.dynamicArray uint256St) =
    .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat))
  change (match (config v).storage.layout
      ({ base := "active", steps := [.length] } : EvaledStorageRef) evm with
    | some lenLoc =>
        match storageLocLoad evm lenLoc with
        | Value.int n => pure (Value.int n)
        | _ => EvalResult.error .storageError
    | none => EvalResult.error .storageError) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat))
  rw [show (config v).storage.layout
      ({ base := "active", steps := [.length] } : EvaledStorageRef) evm =
        some (wordLoc ⟨11⟩) from rfl]
  simp [clipperStorageLocLoad_uint256]
  rfl

theorem clipperCountBodyReturns (v : ClipperImmutables) (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) (hbase : locals.get? "active" = none) :
    ExecTransitionBody (config v) (contract v) evm locals countTransition.body
      (.returned { contract := contract v, locals := locals } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat))])) := by
  simpa [countTransition] using
    nonpayableReturnExprBodyReturns (cfg := config v) (contract := contract v) h
      (clipperEvalActiveLength v evm locals hbase)

set_option maxHeartbeats 1000000 in
theorem clipperReachCountBody {cA gh bl σ σ₀ A I} {g : Sat256} (v : ClipperImmutables)
    {code : ByteArray} (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (clipperSelBytes 5)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨468⟩ : UInt256)
      [clipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := clipperReachRoot (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hpatch hcode hwv hsz hsize
  have hword := clipperCountSelectorWord hsz hsel
  have h260 := clipperSplitTaken (pc := (⟨32⟩ : UInt256)) (pivot := clipperSelNat 20)
    (tgt := (⟨260⟩ : UInt256)) h32
    (by
        change decode code (⟨32⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨32⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 20, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨32⟩ : UInt256)) = some (.GT, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨32⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨260⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨32⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; decide +native)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨260⟩ : UInt256) (by decide +native))
    (by simp)
  have h369 := clipperSplitTaken (pc := (⟨261⟩ : UInt256)) (pivot := clipperSelNat 9)
    (tgt := (⟨369⟩ : UInt256))
    (h260.jumpdest
      (by
          change decode code (⟨260⟩ : UInt256) = some (.JUMPDEST, .none)
          clipper_decode)
      (by simp))
    (by
        change decode code (⟨261⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨261⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 9, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨261⟩ : UInt256)) = some (.GT, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨261⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨369⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨261⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; decide +native)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨369⟩ : UInt256) (by decide +native))
    (by simp)
  have h429 := clipperSplitTaken (pc := (⟨370⟩ : UInt256)) (pivot := clipperSelNat 21)
    (tgt := (⟨429⟩ : UInt256))
    (h369.jumpdest
      (by
          change decode code (⟨369⟩ : UInt256) = some (.JUMPDEST, .none)
          clipper_decode)
      (by simp))
    (by
        change decode code (⟨370⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨370⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 21, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨370⟩ : UInt256)) = some (.GT, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨370⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨429⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨370⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; decide +native)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨429⟩ : UInt256) (by decide +native))
    (by simp)
  have h468 := clipperArmTaken (pc := (⟨430⟩ : UInt256)) (sel := clipperSelNat 5)
    (tgt := (⟨468⟩ : UInt256))
    (h429.jumpdest
      (by
          change decode code (⟨429⟩ : UInt256) = some (.JUMPDEST, .none)
          clipper_decode)
      (by simp))
    (by
        change decode code (⟨430⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨430⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 5, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨430⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨430⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨468⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨430⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; decide +native)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨468⟩ : UInt256) (by decide +native))
    (by simp)
  exact ⟨_, _, h468⟩

theorem clipperCountGetterEntryWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcGetterEntryWf code (⟨468⟩ : UInt256) (⟨476⟩ : UInt256) (⟨1453⟩ : UInt256) := by
  unfold solcGetterEntryWf
  repeat' first | apply And.intro
  all_goals
    rw [clipperDecodeBeforeFirstPatch v hpatch _ (by decide +native)]
    decide +native

@[reducible] def clipperWordSlotSwapGetterWf
    (code : ByteArray) (pc slot : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (slot, 1))
  ∧ decode code p3 = some (.SLOAD, .none)
  ∧ decode code p4 = some (.SWAP1, .none)
  ∧ decode code p5 = some (.JUMP, .none)

-- GENERALIZES Reasoning.Solc.RD.solcWordSlotGetter: solc 0.6 also emits
-- `SLOAD; SWAP1; JUMP` for some no-argument getters, leaving the return pc off-stack.
theorem clipperWordSlotSwapGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc slot ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (ret :: R) mem aw rdata (cA, σ) k C)
    (hwf : clipperWordSlotSwapGetterWf code pc slot)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (solcSlotWord σ ee slot :: R)
      mem aw rdata (cA, σ) k' C' := by
  rcases hwf with ⟨hd0, hd1, hd2, hd3, hd4⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 slot hd1 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd4⟩ := rd3.sload hd2 (by simp only [List.length_cons]; omega)
  have rd5 := rd4.swap1 hd3 (by omega)
  have rdRet := rd5.jump hd4 hret (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa [solcSlotWord] using rdRet⟩

theorem clipperCountSlotGetterWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    clipperWordSlotSwapGetterWf code (⟨1453⟩ : UInt256) (⟨11⟩ : UInt256) := by
  unfold clipperWordSlotSwapGetterWf
  repeat' first | apply And.intro
  all_goals
    exact clipperDecodeBeforeFirstPatchOfDecode v hpatch _ _
      (by decide +native) (by decide +native) (by decide +native)

theorem clipperX_count (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I)
      (⟨468⟩ : UInt256) [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (solcSlotWord σ I ⟨11⟩)) := by
  obtain ⟨_, _, h1453⟩ := RD.solcGetterThunk hreach
    (clipperCountGetterEntryWf v hpatch)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨1453⟩ : UInt256) (by decide +native))
  obtain ⟨_, _, h476⟩ := clipperWordSlotSwapGetter (slot := (⟨11⟩ : UInt256))
    (R := [sel]) h1453 (clipperCountSlotGetterWf v hpatch)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨476⟩ : UInt256) (by decide +native))
    (by simp only [List.length_singleton]; omega)
  exact RD.solcReturnWordFromMem h476 (clipperReturnWord476Wf v hpatch)
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64 (solcSlotWord σ I ⟨11⟩))
    (solcReturnMem_read128 (solcSlotWord σ I ⟨11⟩))
    (by simp only [List.length_nil]; omega)

theorem clipperCountBody (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (clipperSelBytes 5))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (clipperSelBytes 5) (by decide +native) hsel
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ countTransition.body
        (.returned { contract := contract v, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (solcSlotWord σ_solm I ⟨11⟩).toNat))])) := by
    simpa [solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      clipperCountBodyReturns v
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  have hword : solcSlotWord σ_evm I ⟨11⟩ = solcSlotWord σ_solm I ⟨11⟩ :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨11⟩ ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (solcSlotWord σ_solm I ⟨11⟩).toNat)] =
        some [Value.int (Int.ofNat (solcSlotWord σ_evm I ⟨11⟩).toNat)] := by
    rw [hword]
  have henc :
      returnEquiv (UInt256.toByteArray (solcSlotWord σ_evm I ⟨11⟩))
        (some [(.int (Int.ofNat (solcSlotWord σ_evm I ⟨11⟩).toNat))])
        countTransition.returnType := by
    rw [show countTransition.returnType = [uint256] from rfl]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (solcSlotWord σ_evm I ⟨11⟩))
  have hreach := clipperReachCountBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (v := v) hpatch hcode hwv hsz hsize hsel
  have hret := clipperX_count (v := v) (code := code) (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (sel := clipperSelWord I) hpatch hreach
  exact hret.reEquivExecutionTransport hcode (clipperDispatch_count v hsel)
    (clipperDecode_count v hsz) hbody hval hAccounts henc

end Benchmarks.Dss.Clipper
