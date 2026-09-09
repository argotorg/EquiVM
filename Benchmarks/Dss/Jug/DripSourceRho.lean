import Benchmarks.Dss.Jug.DripBase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Jug

theorem jugDripSourceBodyRhoReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (jugSlotWord (fileDutyRhoSlotFor I) σ I).toNat) :
    let locals := dripLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dripTransition.body .reverted := by
  intro locals evm0
  have htimeGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ge (.env .timestamp) (.storage (ilksF (.var "ilk") "rho"))) =
          .ok (.bool false) := by
    simpa [locals, evm0, initState, jugSlotWord] using
      (evalExpr_dripNowGeRho_false (evm := evm0) (I := I) hsz36 (by
        simpa [evm0, initState, jugSlotWord] using hlt))
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dripTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    exact ExecBlock.consRevert (ExecStmt.requireFalse htimeGuard)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem jugReachDripBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = jugBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (jugSelBytes 2)) :
    ∃ k C, RD jugBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨328⟩ [jugSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : jugSelWord I = ⟨0x44e2a5a8⟩ :=
    jugSelWord_eq_of_beq I hsz 0x44 0xe2 0xa5 0xa8 ⟨0x44e2a5a8⟩
      (by decide +native) (by simpa [jugSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat jugBytecode jugRootSplitPc) (jugSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat jugBytecode (nthArmPc jugBytecode jugLowFirstArmPc j))
        (jugSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> decide +native
  have htake :
      UInt256.eq (armSelNat jugBytecode (nthArmPc jugBytecode jugLowFirstArmPc 4))
        (jugSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact jugReachLowBody 4 (by omega) ⟨328⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by decide +native)

theorem RD.jugDripDecodeToRoutine {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨350⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hwf : code = jugBytecode)
    (hroutine : (D_J code 0).contains ⟨1235⟩ = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨1235⟩
      (calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd351 := h.jumpdest (by decide +native) (by evm_ov)
  have rd352 := rd351.pop (by decide +native) (by evm_ov)
  have rd353 := rd352.calldataload (by decide +native) (by evm_ov)
  have rd356 := rd353.push2 ⟨1235⟩ (by decide +native) (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using rd356.jump (by decide +native) hroutine (by evm_ov)⟩

theorem jugDripX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD jugBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨328⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD jugBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1235⟩
        [fileDutyIlkWord I, ⟨357⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := jugBytecode) (sel := sel) (entry := ⟨328⟩) (ret := ⟨357⟩)
    (decoded := ⟨350⟩) (need := ⟨32⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest)
    (by
      exact solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.jugDripDecodeToRoutine
    (code := jugBytecode) (ret := ⟨357⟩) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [fileDutyIlkWord] using hroutine⟩

theorem jugDripX_loadRho {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hsz36 : 36 ≤ I.calldata.size)
    (h : RD jugBytecode I g s0 ⟨1235⟩
      [fileDutyIlkWord I, ⟨357⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD jugBytecode I g s0 ⟨1254⟩
      (jugSlotWord (fileDutyRhoSlotFor I) σ I :: ⟨0⟩ :: fileDutyIlkWord I ::
        ⟨357⟩ :: [sel])
      (dripIlkHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((dripIlkHashMem I).readWithPadding 0 64))) =
        solcMappingSlot ⟨1⟩ (fileDutyIlkWord I) := by
    simpa [dripIlkHashMem] using
      twoWordHashMem_solcMappingSlot (⟨1⟩ : UInt256) (fileDutyIlkWord I)
        solcFreePtrMem_size
  have rd1236 := h.jumpdest (by decide +native) (by evm_ov)
  have rd1238 := rd1236.push1 ⟨0⟩ (by decide +native) (by evm_ov)
  have rd1239 := rd1238.dup2 (by decide +native) (by evm_ov)
  have rd1240pre := rd1239.dup2 (by decide +native) (by evm_ov)
  have rd1241 := rd1240pre.mstore 0 (wordAt0Mem (fileDutyIlkWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd1248pre := evm_run rd1241 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd1248 := rd1248pre.mstore 0 (dripIlkHashMem I)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd1251pre := evm_run rd1248 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov)]
  have rd1252 := rd1251pre.keccak256 0 (solcMappingSlot ⟨1⟩ (fileDutyIlkWord I))
    (UInt256.ofNat 3) (by decide +native) mem_cost hslot (by decide +native) (by evm_ov)
  have rd1253 := rd1252.add (by decide +native) (by evm_ov)
  obtain ⟨k1254, C1254, rd1254raw⟩ := rd1253.sload (by decide +native) (by evm_ov)
  exact ⟨k1254, C1254, by
    simpa [jugSlotWord, fileDutyRhoSlotFor_eq hsz36] using rd1254raw⟩

theorem jugDripX_invalidNow {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hsz36 : 36 ≤ I.calldata.size)
    (hlt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (jugSlotWord (fileDutyRhoSlotFor I) σ I).toNat)
    (h : RD jugBytecode I g s0 ⟨1235⟩
      [fileDutyIlkWord I, ⟨357⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev jugBytecode g s0 := by
  obtain ⟨_, _, rd1254⟩ := jugDripX_loadRho (I := I) hsz36 h
  have rd1255 := RD.timestamp rd1254 (by decide +native) (by evm_ov)
  have rd1256 := rd1255.lt (by decide +native) (by evm_ov)
  have hltWord :
      UInt256.lt (UInt256.ofNat I.header.timestamp)
        (jugSlotWord (fileDutyRhoSlotFor I) σ I) = ⟨1⟩ := by
    exact ult_one hlt
  rw [hltWord] at rd1256
  have rd1257 := rd1256.iszero (by decide +native) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1257
  have rd1260 := rd1257.pushConst (⟨1323⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by decide +native) (by evm_ov)
  have rd1261 := rd1260.jumpiNT (by decide +native) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1261⟩)
    (len := ⟨15⟩)
    (rawWord := ⟨0x4a75672f696e76616c69642d6e6f77⟩)
    (shift := ⟨136⟩)
    (word := ⟨0x4a75672f696e76616c69642d6e6f770000000000000000000000000000000000⟩)
    (op := .PUSH15)
    (width := 15)
    rd1261
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | decide +native)
    (by decide)
    (by decide +native)
    (dripIlkHashMem_size I)
    (dripIlkHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem jugDripX_nowOk {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hsz36 : 36 ≤ I.calldata.size)
    (hle :
      (jugSlotWord (fileDutyRhoSlotFor I) σ I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (h : RD jugBytecode I g s0 ⟨1235⟩
      [fileDutyIlkWord I, ⟨357⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD jugBytecode I g s0 ⟨1323⟩
      [⟨0⟩, fileDutyIlkWord I, ⟨357⟩, sel]
      (dripIlkHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd1254⟩ := jugDripX_loadRho (I := I) hsz36 h
  have rd1255 := RD.timestamp rd1254 (by decide +native) (by evm_ov)
  have rd1256 := rd1255.lt (by decide +native) (by evm_ov)
  have hltWord :
      UInt256.lt (UInt256.ofNat I.header.timestamp)
        (jugSlotWord (fileDutyRhoSlotFor I) σ I) = ⟨0⟩ := by
    exact ult_zero hle
  rw [hltWord] at rd1256
  have rd1257 := rd1256.iszero (by decide +native) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1257
  have rd1260 := rd1257.pushConst (⟨1323⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by decide +native) (by evm_ov)
  exact ⟨_, _, rd1260.jumpiT (by decide +native) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

theorem jugDripSourceBodyVatIlksNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hle :
      (jugSlotWord (fileDutyRhoSlotFor I) σ I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (hvatNoCode :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (dripVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat = 0) :
    let locals := dripLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dripTransition.body .reverted := by
  intro locals evm0
  have htimeGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ge (.env .timestamp) (.storage (ilksF (.var "ilk") "rho"))) =
          .ok (.bool true) := by
    simpa [locals, evm0, initState, jugSlotWord] using
      (evalExpr_dripNowGeRho_true (evm := evm0) (I := I) hsz36 (by
        simpa [evm0, initState, jugSlotWord] using hle))
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (dripVatAddress evm0.accountMap evm0.executionEnv)) := by
    simpa [locals] using evalExpr_dripStorageVat evm0 I
  have hvatNoCode0 :
      (UInt256.ofNat
        ((evm0.lookupAccount (dripVatAddress evm0.accountMap evm0.executionEnv)).option 0
          (fun acc => acc.code.size))).toNat = 0 := by
    simpa [evm0, initState] using hvatNoCode
  have hvatGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool false) := by
    exact evalExpr_dripVatCodeGuard_false hvat hvatNoCode0
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dripTransition.body
        .reverted := by
    simp only [dripTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue htimeGuard) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hvatGuard)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem jugDripSourceBodyVatIlksCallFailed {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hle :
      (jugSlotWord (fileDutyRhoSlotFor I) σ I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (hvatCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (dripVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      typedCallViaEVM config evm0 (EVM.address (dripVatAddress σ I)) "ilks" 0
        [.fixedBytes bytes32Width (fileDutyIlkBytes I)] (false, evmVat, out) true) :
    let locals := dripLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dripTransition.body .reverted := by
  intro locals evm0
  have htimeGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ge (.env .timestamp) (.storage (ilksF (.var "ilk") "rho"))) =
          .ok (.bool true) := by
    simpa [locals, evm0, initState, jugSlotWord] using
      (evalExpr_dripNowGeRho_true (evm := evm0) (I := I) hsz36 (by
        simpa [evm0, initState, jugSlotWord] using hle))
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (dripVatAddress evm0.accountMap evm0.executionEnv)) := by
    simpa [locals] using evalExpr_dripStorageVat evm0 I
  have hvatCode0 :
      0 <
        (UInt256.ofNat
          ((evm0.lookupAccount (dripVatAddress evm0.accountMap evm0.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat := by
    simpa [evm0, initState] using hvatCode
  have hvatGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) := by
    exact evalExpr_dripVatCodeGuard_true hvat hvatCode0
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0 [.var "ilk"] =
        .ok [.fixedBytes bytes32Width (fileDutyIlkBytes I)] := by
    simpa [locals] using evalExprs_dripVatIlksArgs evm0 I
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dripTransition.body
        .reverted := by
    simp only [dripTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue htimeGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
    exact ExecBlock.consRevert
      (ExecStmt.externalCallFailure (sendVal := 0) hvat (by simp [evalExpr?, pure]) hargs
        (by simpa [evm0] using hcall))
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem jugDripSourceBodyVatIlksReturnDecodeReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hle :
      (jugSlotWord (fileDutyRhoSlotFor I) σ I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (hvatCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (dripVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      typedCallViaEVM config evm0 (EVM.address (dripVatAddress σ I)) "ilks" 0
        [.fixedBytes bytes32Width (fileDutyIlkBytes I)] (true, evmVat, out) true)
    (hdec : config.externalABI.decode? "ilks" out = none) :
    let locals := dripLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dripTransition.body .reverted := by
  intro locals evm0
  have htimeGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ge (.env .timestamp) (.storage (ilksF (.var "ilk") "rho"))) =
          .ok (.bool true) := by
    simpa [locals, evm0, initState, jugSlotWord] using
      (evalExpr_dripNowGeRho_true (evm := evm0) (I := I) hsz36 (by
        simpa [evm0, initState, jugSlotWord] using hle))
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (dripVatAddress evm0.accountMap evm0.executionEnv)) := by
    simpa [locals] using evalExpr_dripStorageVat evm0 I
  have hvatCode0 :
      0 <
        (UInt256.ofNat
          ((evm0.lookupAccount (dripVatAddress evm0.accountMap evm0.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat := by
    simpa [evm0, initState] using hvatCode
  have hvatGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) := by
    exact evalExpr_dripVatCodeGuard_true hvat hvatCode0
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0 [.var "ilk"] =
        .ok [.fixedBytes bytes32Width (fileDutyIlkBytes I)] := by
    simpa [locals] using evalExprs_dripVatIlksArgs evm0 I
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dripTransition.body
        .reverted := by
    simp only [dripTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue htimeGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
    exact ExecBlock.consRevert
      (ExecStmt.externalCallReturnDecodeRevert (sendVal := 0) hvat
        (by simp [evalExpr?, pure]) hargs (by simpa [evm0] using hcall) hdec)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem jugDripSourceBodyVatIlksAddOverflowReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hle :
      (jugSlotWord (fileDutyRhoSlotFor I) σ I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (hvatCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (dripVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      typedCallViaEVM config evm0 (EVM.address (dripVatAddress σ I)) "ilks" 0
        [.fixedBytes bytes32Width (fileDutyIlkBytes I)] (true, evmVat, out) true)
    (hdec :
      config.externalABI.decode? "ilks" out =
        some [.int (Int.ofNat (dripVatIlksArtWord out).toNat),
          .int (Int.ofNat (dripVatIlksPrevWord out).toNat)])
    (hover :
      UInt256.size ≤ (jugSlotWord ⟨4⟩ evmVat.accountMap evmVat.executionEnv).toNat +
        (jugSlotWord (fileDutyDutySlotFor I) evmVat.accountMap evmVat.executionEnv).toNat) :
    let locals := dripLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dripTransition.body .reverted := by
  intro locals evm0
  let base := jugSlotWord ⟨4⟩ evmVat.accountMap evmVat.executionEnv
  let duty := jugSlotWord (fileDutyDutySlotFor I) evmVat.accountMap evmVat.executionEnv
  have htimeGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ge (.env .timestamp) (.storage (ilksF (.var "ilk") "rho"))) =
          .ok (.bool true) := by
    simpa [locals, evm0, initState, jugSlotWord] using
      (evalExpr_dripNowGeRho_true (evm := evm0) (I := I) hsz36 (by
        simpa [evm0, initState, jugSlotWord] using hle))
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (dripVatAddress evm0.accountMap evm0.executionEnv)) := by
    simpa [locals] using evalExpr_dripStorageVat evm0 I
  have hvatCode0 :
      0 <
        (UInt256.ofNat
          ((evm0.lookupAccount (dripVatAddress evm0.accountMap evm0.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat := by
    simpa [evm0, initState] using hvatCode
  have hvatGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) := by
    exact evalExpr_dripVatCodeGuard_true hvat hvatCode0
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0 [.var "ilk"] =
        .ok [.fixedBytes bytes32Width (fileDutyIlkBytes I)] := by
    simpa [locals] using evalExprs_dripVatIlksArgs evm0 I
  have hprev :
      evalExpr? config { contract := contract, locals := dripVatIlksLocals I out } evmVat
        (.tupleGet (.var "vatIlk") 1) =
          .ok (.int (Int.ofNat (dripVatIlksPrevWord out).toNat)) :=
    evalExpr_dripVatIlksPrev evmVat I out
  have haddArgs :
      evalExprs? config { contract := contract, locals := dripVatIlksPrevLocals I out } evmVat
        [.storage baseRef, .storage (ilksF (.var "ilk") "duty")] =
          .ok [.int (Int.ofNat base.toNat), .int (Int.ofNat duty.toNat)] := by
    simpa [base, duty] using evalExprs_dripAddArgs evmVat I out hsz36
  have hlookup : lookupCallable? contract "_add" = some addFunction.toCallable := by
    rfl
  have hbind :
      bindParams? addFunction.params
        [.int (Int.ofNat base.toNat), .int (Int.ofNat duty.toNat)] =
          some (uintBinaryLocals base duty) := by
    simp [addFunction, uintBinaryLocals, bindParams?]
  have haddRevert :
      ExecStmt config { contract := contract, locals := dripVatIlksPrevLocals I out } evmVat
        (.internalCall "_add"
          [.storage baseRef, .storage (ilksF (.var "ilk") "duty")] "fee")
        .reverted := by
    exact internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := dripVatIlksPrevLocals I out })
      (evm := evmVat) (name := "_add") (retVar := "fee")
      (args := [.storage baseRef, .storage (ilksF (.var "ilk") "duty")])
      (argVals := [.int (Int.ofNat base.toNat), .int (Int.ofNat duty.toNat)])
      (callee := addFunction) (locals := uintBinaryLocals base duty)
      haddArgs hlookup hbind
      (by
        simpa [base, duty] using execAddFunctionRevert evmVat (x := base) (y := duty) hover)
  have hprevStmt :
      ExecStmt config { contract := contract, locals := dripVatIlksLocals I out } evmVat
        (.letDecl "prev" (some uint256) (.tupleGet (.var "vatIlk") 1))
        (.ok { contract := contract, locals := dripVatIlksPrevLocals I out } evmVat) := by
    simpa [dripVatIlksPrevLocals] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := dripVatIlksLocals I out })
        (evm := evmVat)
        (name := "prev")
        (ty := some uint256)
        (expr := .tupleGet (.var "vatIlk") 1)
        (value := .int (Int.ofNat (dripVatIlksPrevWord out).toNat))
        hprev)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dripTransition.body
        .reverted := by
    simp only [dripTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue htimeGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
    refine ExecBlock.consNormal
      (ExecStmt.externalCallSuccess (sendVal := 0) hvat
        (by simp [evalExpr?, pure]) hargs (by simpa [evm0] using hcall) hdec) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, dripVatIlksLocals, collapseReturns] using hprevStmt) ?_
    exact ExecBlock.consRevert (by
      simpa [locals, dripVatIlksLocals, dripVatIlksPrevLocals, collapseReturns] using haddRevert)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem jugDripSourceBodyVatIlksRmulOverflowReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hle :
      (jugSlotWord (fileDutyRhoSlotFor I) σ I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (hvatCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (dripVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      typedCallViaEVM config evm0 (EVM.address (dripVatAddress σ I)) "ilks" 0
        [.fixedBytes bytes32Width (fileDutyIlkBytes I)] (true, evmVat, out) true)
    (hdec :
      config.externalABI.decode? "ilks" out =
        some [.int (Int.ofNat (dripVatIlksArtWord out).toNat),
          .int (Int.ofNat (dripVatIlksPrevWord out).toNat)])
    (haddNo :
      ¬ UInt256.size ≤
        (jugSlotWord ⟨4⟩ evmVat.accountMap evmVat.executionEnv).toNat +
          (jugSlotWord (fileDutyDutySlotFor I) evmVat.accountMap evmVat.executionEnv).toNat)
    (hage :
      UInt256.sub (UInt256.ofNat evmVat.executionEnv.header.timestamp)
        (jugSlotWord (fileDutyRhoSlotFor I) evmVat.accountMap evmVat.executionEnv) = ⟨0⟩)
    (hrmulOverflow : UInt256.size ≤ jugRay.toNat * (dripVatIlksPrevWord out).toNat) :
    let locals := dripLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dripTransition.body .reverted := by
  intro locals evm0
  let base := jugSlotWord ⟨4⟩ evmVat.accountMap evmVat.executionEnv
  let duty := jugSlotWord (fileDutyDutySlotFor I) evmVat.accountMap evmVat.executionEnv
  let fee := base + duty
  have htimeGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ge (.env .timestamp) (.storage (ilksF (.var "ilk") "rho"))) =
          .ok (.bool true) := by
    simpa [locals, evm0, initState, jugSlotWord] using
      (evalExpr_dripNowGeRho_true (evm := evm0) (I := I) hsz36 (by
        simpa [evm0, initState, jugSlotWord] using hle))
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (dripVatAddress evm0.accountMap evm0.executionEnv)) := by
    simpa [locals] using evalExpr_dripStorageVat evm0 I
  have hvatCode0 :
      0 <
        (UInt256.ofNat
          ((evm0.lookupAccount (dripVatAddress evm0.accountMap evm0.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat := by
    simpa [evm0, initState] using hvatCode
  have hvatGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) := by
    exact evalExpr_dripVatCodeGuard_true hvat hvatCode0
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0 [.var "ilk"] =
        .ok [.fixedBytes bytes32Width (fileDutyIlkBytes I)] := by
    simpa [locals] using evalExprs_dripVatIlksArgs evm0 I
  have hprev :
      evalExpr? config { contract := contract, locals := dripVatIlksLocals I out } evmVat
        (.tupleGet (.var "vatIlk") 1) =
          .ok (.int (Int.ofNat (dripVatIlksPrevWord out).toNat)) :=
    evalExpr_dripVatIlksPrev evmVat I out
  have haddArgs :
      evalExprs? config { contract := contract, locals := dripVatIlksPrevLocals I out } evmVat
        [.storage baseRef, .storage (ilksF (.var "ilk") "duty")] =
          .ok [.int (Int.ofNat base.toNat), .int (Int.ofNat duty.toNat)] := by
    simpa [base, duty] using evalExprs_dripAddArgs evmVat I out hsz36
  have hlookupAdd : lookupCallable? contract "_add" = some addFunction.toCallable := by
    rfl
  have hbindAdd :
      bindParams? addFunction.params [.int (Int.ofNat base.toNat), .int (Int.ofNat duty.toNat)] =
        some (uintBinaryLocals base duty) := by
    simp [addFunction, uintBinaryLocals, bindParams?]
  have hfitAdd : base.toNat + duty.toNat < UInt256.size := by
    exact Nat.lt_of_not_ge haddNo
  have haddReturn :
      ExecStmt config { contract := contract, locals := dripVatIlksPrevLocals I out } evmVat
        (.internalCall "_add"
          [.storage baseRef, .storage (ilksF (.var "ilk") "duty")] "fee")
        (.ok { contract := contract, locals := dripFeeLocals I out fee } evmVat) := by
    have h := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := dripVatIlksPrevLocals I out })
      (evm := evmVat) (name := "_add") (retVar := "fee")
      (args := [.storage baseRef, .storage (ilksF (.var "ilk") "duty")])
      (argVals := [.int (Int.ofNat base.toNat), .int (Int.ofNat duty.toNat)])
      (callee := addFunction) (locals := uintBinaryLocals base duty)
      haddArgs hlookupAdd hbindAdd
      (execAddFunctionReturn evmVat (x := base) (y := duty) (sum := fee) rfl hfitAdd)
    simpa [resumeAfterInternalCall, dripFeeLocals, fee] using h
  have hrpowArgs :
      evalExprs? config { contract := contract, locals := dripFeeLocals I out fee } evmVat
        [ .var "fee",
          sub256 (.env .timestamp) (.storage (ilksF (.var "ilk") "rho")),
          .intLit one ] =
          .ok [.int (Int.ofNat fee.toNat), .int 0, .int (Int.ofNat jugRay.toNat)] :=
    evalExprs_dripRpowNZeroArgs evmVat I out fee hsz36 hage
  have hlookupRpow : lookupCallable? contract "_rpow" = some rpowFunction.toCallable := by
    rfl
  have hbindRpow :
      bindParams? rpowFunction.params
          [.int (Int.ofNat fee.toNat), .int 0, .int (Int.ofNat jugRay.toNat)] =
        some (uintTernaryLocals fee ⟨0⟩ jugRay) := by
    simp [rpowFunction, uintTernaryLocals, bindParams?, jugUInt256Zero_toNat]
  have hrpowBody :
      ∃ doneLocals,
        ExecFuncBody config { contract := contract, locals := uintTernaryLocals fee ⟨0⟩ jugRay }
          evmVat rpowFunction.body
          (.returned { contract := contract, locals := doneLocals }
            evmVat (some [.int (Int.ofNat jugRay.toNat)])) := by
    by_cases hfee0 : fee = ⟨0⟩
    · exact ⟨uintTernaryLocals ⟨0⟩ ⟨0⟩ jugRay, by
        simpa [hfee0] using execRpowFunctionReturnXZeroNZero (evm := evmVat) (b := jugRay)⟩
    · have h := execRpowFunctionReturnXNonzeroNZero (evm := evmVat) (x := fee)
        (b := jugRay) hfee0
      exact ⟨rpowLocalsZHN fee ⟨0⟩ jugRay jugRay (UInt256.div jugRay ⟨2⟩) ⟨0⟩, h⟩
  obtain ⟨rpowDoneLocals, hrpowBody⟩ := hrpowBody
  have hrpowReturn :
      ExecStmt config { contract := contract, locals := dripFeeLocals I out fee } evmVat
        (.internalCall "_rpow"
          [ .var "fee",
            sub256 (.env .timestamp) (.storage (ilksF (.var "ilk") "rho")),
            .intLit one ] "pow")
        (.ok { contract := contract, locals := dripPowLocals I out fee jugRay } evmVat) := by
    have h := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := dripFeeLocals I out fee })
      (evm := evmVat) (name := "_rpow") (retVar := "pow")
      (args :=
        [ .var "fee",
          sub256 (.env .timestamp) (.storage (ilksF (.var "ilk") "rho")),
          .intLit one ])
      (argVals := [.int (Int.ofNat fee.toNat), .int 0, .int (Int.ofNat jugRay.toNat)])
      (callee := rpowFunction) (locals := uintTernaryLocals fee ⟨0⟩ jugRay)
      (calleeSolm := { contract := contract, locals := rpowDoneLocals })
      hrpowArgs hlookupRpow hbindRpow hrpowBody
    simpa [resumeAfterInternalCall, dripPowLocals] using h
  have hrmulArgs :
      evalExprs? config { contract := contract, locals := dripPowLocals I out fee jugRay }
        evmVat [.var "pow", .var "prev"] =
        .ok [.int (Int.ofNat jugRay.toNat),
          .int (Int.ofNat (dripVatIlksPrevWord out).toNat)] :=
    evalExprs_dripRmulArgs evmVat I out fee jugRay
  have hlookupRmul : lookupCallable? contract "_rmul" = some rmulFunction.toCallable := by
    rfl
  have hbindRmul :
      bindParams? rmulFunction.params
          [.int (Int.ofNat jugRay.toNat), .int (Int.ofNat (dripVatIlksPrevWord out).toNat)] =
        some (uintBinaryLocals jugRay (dripVatIlksPrevWord out)) := by
    simp [rmulFunction, uintBinaryLocals, bindParams?]
  have hrmulRevert :
      ExecStmt config { contract := contract, locals := dripPowLocals I out fee jugRay } evmVat
        (.internalCall "_rmul" [.var "pow", .var "prev"] "rate") .reverted := by
    exact internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := dripPowLocals I out fee jugRay })
      (evm := evmVat) (name := "_rmul") (retVar := "rate")
      (args := [.var "pow", .var "prev"])
      (argVals :=
        [.int (Int.ofNat jugRay.toNat),
          .int (Int.ofNat (dripVatIlksPrevWord out).toNat)])
      (callee := rmulFunction) (locals := uintBinaryLocals jugRay (dripVatIlksPrevWord out))
      hrmulArgs hlookupRmul hbindRmul
      (execRmulFunctionRevertMul evmVat (x := jugRay) (y := dripVatIlksPrevWord out)
        hrmulOverflow)
  have hprevStmt :
      ExecStmt config { contract := contract, locals := dripVatIlksLocals I out } evmVat
        (.letDecl "prev" (some uint256) (.tupleGet (.var "vatIlk") 1))
        (.ok { contract := contract, locals := dripVatIlksPrevLocals I out } evmVat) := by
    simpa [dripVatIlksPrevLocals] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := dripVatIlksLocals I out })
        (evm := evmVat)
        (name := "prev")
        (ty := some uint256)
        (expr := .tupleGet (.var "vatIlk") 1)
        (value := .int (Int.ofNat (dripVatIlksPrevWord out).toNat))
        hprev)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dripTransition.body
        .reverted := by
    simp only [dripTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue htimeGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
    refine ExecBlock.consNormal
      (ExecStmt.externalCallSuccess (sendVal := 0) hvat
        (by simp [evalExpr?, pure]) hargs (by simpa [evm0] using hcall) hdec) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, dripVatIlksLocals, collapseReturns] using hprevStmt) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, dripVatIlksLocals, dripVatIlksPrevLocals, collapseReturns] using
        haddReturn) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, dripVatIlksLocals, dripVatIlksPrevLocals, dripFeeLocals,
        collapseReturns] using hrpowReturn) ?_
    exact ExecBlock.consRevert (by
      simpa [locals, dripVatIlksLocals, dripVatIlksPrevLocals, dripFeeLocals, dripPowLocals,
        collapseReturns] using hrmulRevert)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

end Benchmarks.Dss.Jug
