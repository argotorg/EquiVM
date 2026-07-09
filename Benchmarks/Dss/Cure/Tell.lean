import Benchmarks.Dss.Cure.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Cure

/-! ## `tell()` -/

def tellLiveWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  cureSlotWord ⟨1⟩ σ I

def tellSrcsLenWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  cureSlotWord ⟨2⟩ σ I

def tellWhenWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  cureSlotWord ⟨4⟩ σ I

def tellLCountWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  cureSlotWord ⟨8⟩ σ I

def tellSayWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  cureSlotWord ⟨9⟩ σ I

def tellTimestampWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.header.timestamp

abbrev tellLiveEvaledRef : EvaledStorageRef :=
  { base := "live", steps := [] }

abbrev tellWhenEvaledRef : EvaledStorageRef :=
  { base := "when", steps := [] }

abbrev tellLCountEvaledRef : EvaledStorageRef :=
  { base := "lCount", steps := [] }

abbrev tellSayEvaledRef : EvaledStorageRef :=
  { base := "say", steps := [] }

abbrev tellGuardExpr : Expr :=
  .binary .and
    (.binary .eq (.storage liveRef) (.intLit 0))
    (.binary .or
      (.binary .eq (.storage lCountRef) (.arrayLength .storage srcsRef))
      (.binary .ge (.env .timestamp) (.storage whenRef)))

theorem evalExpr_ge_uint256_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {new old : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat new.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat old.toNat)))
    (hge : old.toNat ≤ new.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .ge lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact_mod_cast hge

theorem evalExpr_ge_uint256_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {new old : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat new.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat old.toNat)))
    (hlt : new.toNat < old.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .ge lhs rhs) =
      .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact_mod_cast hlt

theorem evalExpr_tellLiveStorage {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "live" = none) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (.storage liveRef) =
        .ok (.int (Int.ofNat (tellLiveWord σ I).toNat)) := by
  rw [evalExpr_storage_scalar (er := tellLiveEvaledRef) (t := .int uint256Int)
    (loc := wordLoc ⟨1⟩)]
  · exact congrArg EvalResult.ok (cureStorageLocLoad_uint256 _ ⟨1⟩)
  · exact hbase
  · simp [tellLiveEvaledRef, liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind,
      pure, bind]
  · simp [storageTypeAt?, contract, storageDecls, uint256St]
  · funext evm
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, tellLiveEvaledRef]

theorem evalExpr_tellWhenStorage {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "when" = none) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (.storage whenRef) =
        .ok (.int (Int.ofNat (tellWhenWord σ I).toNat)) := by
  rw [evalExpr_storage_scalar (er := tellWhenEvaledRef) (t := .int uint256Int)
    (loc := wordLoc ⟨4⟩)]
  · exact congrArg EvalResult.ok (cureStorageLocLoad_uint256 _ ⟨4⟩)
  · exact hbase
  · simp [tellWhenEvaledRef, whenRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind,
      pure, bind]
  · simp [storageTypeAt?, contract, storageDecls, uint256St]
  · funext evm
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, tellWhenEvaledRef]

theorem evalExpr_tellLCountStorage {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "lCount" = none) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (.storage lCountRef) =
        .ok (.int (Int.ofNat (tellLCountWord σ I).toNat)) := by
  rw [evalExpr_storage_scalar (er := tellLCountEvaledRef) (t := .int uint256Int)
    (loc := wordLoc ⟨8⟩)]
  · exact congrArg EvalResult.ok (cureStorageLocLoad_uint256 _ ⟨8⟩)
  · exact hbase
  · simp [tellLCountEvaledRef, lCountRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind,
      pure, bind]
  · simp [storageTypeAt?, contract, storageDecls, uint256St]
  · funext evm
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, tellLCountEvaledRef]

theorem evalExpr_tellSayStorage {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "say" = none) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (.storage sayRef) =
        .ok (.int (Int.ofNat (tellSayWord σ I).toNat)) := by
  rw [evalExpr_storage_scalar (er := tellSayEvaledRef) (t := .int uint256Int)
    (loc := wordLoc ⟨9⟩)]
  · exact congrArg EvalResult.ok (cureStorageLocLoad_uint256 _ ⟨9⟩)
  · exact hbase
  · simp [tellSayEvaledRef, sayRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind,
      pure, bind]
  · simp [storageTypeAt?, contract, storageDecls, uint256St]
  · funext evm
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, tellSayEvaledRef]

theorem evalExpr_tellSrcsLength {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := ∅ }
      (initState cA gh bl σ σ₀ g A I) (.arrayLength .storage srcsRef) =
        .ok (.int (Int.ofNat (tellSrcsLenWord σ I).toNat)) := by
  simp [evalExpr?, tellSrcsLenWord, cureSlotWord, initState, config, contract,
    srcsRef, storageDecls, storageLayout, solidityStorageLayout, storageLayoutRaw,
    readStorageArrayLength?, resolveStorageRef?, storageTypeAt?, evalStorageRef,
    evalStorageRefSteps, wordLoc, EvalResult.ofOption, EvalResult.bind, pure, bind]
  change
    (match storageLocLoad
      (initState cA gh bl σ σ₀ g A I) (wordLoc ⟨2⟩) with
    | Value.int n => EvalResult.ok (Value.int n)
    | _ => EvalResult.error EvalError.storageError) =
      EvalResult.ok (Value.int ↑(cureSlotWord ⟨2⟩ σ I).toNat)
  rw [cureStorageLocLoad_uint256]
  simp [cureSlotWord, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount,
    Account.lookupStorage]

theorem evalExpr_tellTimestamp {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store} :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (.env .timestamp) =
        .ok (.int (Int.ofNat (tellTimestampWord I).toNat)) := by
  simp [evalExpr?, envValue, tellTimestampWord, initState, pure]

theorem cureTellGuardEval_countTrue {cA gh bl σ σ₀ A I} {g : Sat256}
    (hlive : tellLiveWord σ I = ⟨0⟩)
    (hcount : tellLCountWord σ I = tellSrcsLenWord σ I) :
    evalExpr? config { contract := contract, locals := ∅ }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .and
        (.binary .eq (.storage liveRef) (.intLit 0))
        (.binary .or
          (.binary .eq (.storage lCountRef) (.arrayLength .storage srcsRef))
          (.binary .ge (.env .timestamp) (.storage whenRef)))) =
        .ok (.bool true) := by
  have hliveEval := evalExpr_tellLiveStorage (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := ∅)
    (by simp)
  have hlcountEval := evalExpr_tellLCountStorage (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := ∅)
    (by simp)
  have hsrcsEval := evalExpr_tellSrcsLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
  simp [evalExpr?, EvalResult.bind, bind, hliveEval, hlcountEval, hsrcsEval,
    evalBinaryOp?, hlive, hcount, pure]

theorem cureTellGuardEval_timeTrue {cA gh bl σ σ₀ A I} {g : Sat256}
    (hlive : tellLiveWord σ I = ⟨0⟩)
    (hcount : tellLCountWord σ I ≠ tellSrcsLenWord σ I)
    (htime : (tellWhenWord σ I).toNat ≤ (tellTimestampWord I).toNat) :
    evalExpr? config { contract := contract, locals := ∅ }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .and
        (.binary .eq (.storage liveRef) (.intLit 0))
        (.binary .or
          (.binary .eq (.storage lCountRef) (.arrayLength .storage srcsRef))
          (.binary .ge (.env .timestamp) (.storage whenRef)))) =
        .ok (.bool true) := by
  have hliveEval := evalExpr_tellLiveStorage (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := ∅)
    (by simp)
  have hlcountEval := evalExpr_tellLCountStorage (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := ∅)
    (by simp)
  have hsrcsEval := evalExpr_tellSrcsLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have htimeEval := evalExpr_ge_uint256_true
    (evalExpr_tellTimestamp (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := ∅))
    (evalExpr_tellWhenStorage (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := ∅)
      (by simp))
    htime
  have hcountEq :
      (Value.int ↑(tellLCountWord σ I).toNat ==
        Value.int ↑(tellSrcsLenWord σ I).toNat) = false := by
    rw [beq_eq_false_iff_ne]
    intro hval
    rw [Value.int.injEq] at hval
    exact hcount (u256_inj (Int.ofNat.inj hval))
  simp [evalExpr?, EvalResult.bind, bind, hliveEval, hlcountEval, hsrcsEval, htimeEval,
    evalBinaryOp?, hlive, hcountEq, pure]

theorem cureTellGuardEval_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hlive : tellLiveWord σ I = ⟨0⟩)
    (hcount : tellLCountWord σ I ≠ tellSrcsLenWord σ I)
    (htime : (tellTimestampWord I).toNat < (tellWhenWord σ I).toNat) :
    evalExpr? config { contract := contract, locals := ∅ }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .and
        (.binary .eq (.storage liveRef) (.intLit 0))
        (.binary .or
          (.binary .eq (.storage lCountRef) (.arrayLength .storage srcsRef))
          (.binary .ge (.env .timestamp) (.storage whenRef)))) =
        .ok (.bool false) := by
  have hliveEval := evalExpr_tellLiveStorage (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := ∅)
    (by simp)
  have hlcountEval := evalExpr_tellLCountStorage (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := ∅)
    (by simp)
  have hsrcsEval := evalExpr_tellSrcsLength (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have htimeEval := evalExpr_ge_uint256_false
    (evalExpr_tellTimestamp (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := ∅))
    (evalExpr_tellWhenStorage (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := ∅)
      (by simp))
    htime
  have hcountEq :
      (Value.int ↑(tellLCountWord σ I).toNat ==
        Value.int ↑(tellSrcsLenWord σ I).toNat) = false := by
    rw [beq_eq_false_iff_ne]
    intro hval
    rw [Value.int.injEq] at hval
    exact hcount (u256_inj (Int.ofNat.inj hval))
  simp [evalExpr?, EvalResult.bind, bind, hliveEval, hlcountEval, hsrcsEval, htimeEval,
    evalBinaryOp?, hlive, hcountEq, pure]

theorem cureTellGuardEval_liveFalse {cA gh bl σ σ₀ A I} {g : Sat256}
    (hlive : tellLiveWord σ I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := ∅ }
      (initState cA gh bl σ σ₀ g A I) tellGuardExpr =
        .ok (.bool false) := by
  have hliveEval := evalExpr_tellLiveStorage (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := ∅)
    (by simp)
  have hliveEq :
      (Value.int ↑(tellLiveWord σ I).toNat == Value.int 0) = false := by
    rw [beq_eq_false_iff_ne]
    intro hval
    rw [Value.int.injEq] at hval
    change Int.ofNat (tellLiveWord σ I).toNat = Int.ofNat 0 at hval
    exact hlive (u256_inj (Int.ofNat.inj hval))
  simp [tellGuardExpr, evalExpr?, EvalResult.bind, bind, hliveEval, evalBinaryOp?,
    hliveEq, pure]

theorem cureTellSourceBodyOk {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hguard :
      evalExpr? config { contract := contract, locals := ∅ }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) tellGuardExpr =
          .ok (.bool true)) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅ tellTransition.body
      (.returned { contract := contract, locals := ∅ }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (some [(.int (Int.ofNat (tellSayWord σ I).toNat))])) := by
  let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
  have hsayEval :
      evalExpr? config { contract := contract, locals := ∅ } evm0 (.storage sayRef) =
        .ok (.int (Int.ofNat (tellSayWord σ I).toNat)) :=
    evalExpr_tellSayStorage (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      (locals := ∅) (by simp)
  have hblock :
      ExecBlock config { contract := contract, locals := ∅ } evm0
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require tellGuardExpr,
          .return [.storage sayRef] ]
        (.returned { contract := contract, locals := ∅ } evm0
          (some [(.int (Int.ofNat (tellSayWord σ I).toNat))])) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [evm0] using hguard)) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hsayEval))
  simpa [ExecTransitionBody, tellTransition, nonpayable, tellGuardExpr, evm0] using
    ExecFuncBody.execBlockRet hblock

theorem cureTellSourceBodyReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hguard :
      evalExpr? config { contract := contract, locals := ∅ }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) tellGuardExpr =
          .ok (.bool false)) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅ tellTransition.body
      .reverted := by
  let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
  have hblock :
      ExecBlock config { contract := contract, locals := ∅ } evm0
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require tellGuardExpr,
          .return [.storage sayRef] ]
        .reverted := by
    exact nonpayableSecondRequireReverts
      (cfg := config) (solm := { contract := contract, locals := ∅ }) (evm := evm0)
      (guard := tellGuardExpr) (rest := [.return [.storage sayRef]])
      (by simp [evm0, initState]; exact hwv) (by simpa [evm0] using hguard)
  simpa [ExecTransitionBody, tellTransition, nonpayable, tellGuardExpr, evm0] using
    ExecFuncBody.execBlockRevert hblock

/-! ### `tell` bytecode routine helpers -/

@[reducible] def cureTellCountTimeTailPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p6 := p5 + ⟨1⟩
  let p8 := p6 + UInt256.ofNat 2
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p14 := p11 + UInt256.ofNat 3
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p18 := p16 + UInt256.ofNat 2
  let p19 := p18 + ⟨1⟩
  let p21 := p19 + UInt256.ofNat 2
  let p22 := p21 + ⟨1⟩
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p27 := p24 + UInt256.ofNat 3
  p27 + ⟨1⟩

@[reducible] def cureTellCountSuccessWf
    (code : ByteArray) (pc guardPc successPc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p6 := p5 + ⟨1⟩
  let p8 := p6 + UInt256.ofNat 2
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p14 := p11 + UInt256.ofNat 3
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p18 := p16 + UInt256.ofNat 2
  let p19 := p18 + ⟨1⟩
  let p21 := p19 + UInt256.ofNat 2
  let p22 := p21 + ⟨1⟩
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p27 := p24 + UInt256.ofNat 3
  let p28 := p27 + ⟨1⟩
  let p29 := p28 + ⟨1⟩
  let p31 := p29 + UInt256.ofNat 2
  let p32 := p31 + ⟨1⟩
  let p33 := p32 + ⟨1⟩
  let p34 := p33 + ⟨1⟩
  let g1 := guardPc + ⟨1⟩
  let g4 := g1 + UInt256.ofNat 3
  let s1 := successPc + ⟨1⟩
  let s2 := s1 + ⟨1⟩
  let s4 := s2 + UInt256.ofNat 2
  let s5 := s4 + ⟨1⟩
  let s6 := s5 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p5 = some (.SLOAD, .none)
  ∧ decode code p6 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p8 = some (.EQ, .none)
  ∧ decode code p9 = some (.DUP1, .none)
  ∧ decode code p10 = some (.ISZERO, .none)
  ∧ decode code p11 = some (.Push .PUSH2, some (guardPc, 2))
  ∧ decode code p14 = some (.JUMPI, .none)
  ∧ decode code p15 = some (.POP, .none)
  ∧ decode code p16 = some (.Push .PUSH1, some (⟨2⟩, 1))
  ∧ decode code p18 = some (.SLOAD, .none)
  ∧ decode code p19 = some (.Push .PUSH1, some (⟨8⟩, 1))
  ∧ decode code p21 = some (.SLOAD, .none)
  ∧ decode code p22 = some (.EQ, .none)
  ∧ decode code p23 = some (.DUP1, .none)
  ∧ decode code p24 = some (.Push .PUSH2, some (guardPc, 2))
  ∧ decode code p27 = some (.JUMPI, .none)
  ∧ decode code p28 = some (.POP, .none)
  ∧ decode code p29 = some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode code p31 = some (.SLOAD, .none)
  ∧ decode code p32 = some (.TIMESTAMP, .none)
  ∧ decode code p33 = some (.LT, .none)
  ∧ decode code p34 = some (.ISZERO, .none)
  ∧ guardPc = p34 + ⟨1⟩
  ∧ decode code guardPc = some (.JUMPDEST, .none)
  ∧ decode code g1 = some (.Push .PUSH2, some (successPc, 2))
  ∧ decode code g4 = some (.JUMPI, .none)
  ∧ decode code successPc = some (.JUMPDEST, .none)
  ∧ decode code s1 = some (.POP, .none)
  ∧ decode code s2 = some (.Push .PUSH1, some (⟨9⟩, 1))
  ∧ decode code s4 = some (.SLOAD, .none)
  ∧ decode code s5 = some (.SWAP1, .none)
  ∧ decode code s6 = some (.JUMP, .none)

theorem RD.cureTellRoutineCountSuccess {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc guardPc successPc ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : cureTellCountSuccessWf code pc guardPc successPc)
    (hlive : solcSlotWord σ ee ⟨1⟩ = ⟨0⟩)
    (hcount : solcSlotWord σ ee ⟨8⟩ = solcSlotWord σ ee ⟨2⟩)
    (hguard : (D_J code 0).contains guardPc = true)
    (hsuccess : (D_J code 0).contains successPc = true)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      ((σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨9⟩ ⟨0⟩)) :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd6, hd8, hd9, hd10, hd11, hd14, hd15, hd16,
      hd18, hd19, hd21, hd22, hd23, hd24, hd27, _hd28, _hd29, _hd31, _hd32,
      _hd33, _hd34, _hguardEq, hdg0, hdg1, hdg4, hds0, hds1, hds2, hds4,
      hds5, hds6⟩
  have rd5 := evm_run h with [
    raw jumpdest hd0 (by simp only [List.length_cons]; omega),
    raw push1 ⟨0⟩ hd1 (by simp only [List.length_cons]; omega),
    raw push1 ⟨1⟩ hd3 (by simp only [List.length_cons]; omega)]
  obtain ⟨_, _, rd6⟩ := rd5.sload hd5 (by simp only [List.length_cons]; omega)
  have hliveRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) = ⟨0⟩ := by
    simpa [solcSlotWord] using hlive
  rw [hliveRaw] at rd6
  have rd9 := rd6.push1 ⟨0⟩ hd6 (by simp only [List.length_cons]; omega)
    |>.eq hd8 (by simp only [List.length_cons]; omega)
  have rd9' := rd9
  rw [uInt256_eq_self] at rd9'
  have rd10 := rd9'.dup1 hd9 (by simp only [List.length_cons]; omega)
  have rd14 := rd10.iszero hd10 (by simp only [List.length_cons]; omega)
    |>.push2 guardPc hd11 (by simp only [List.length_cons]; omega)
  have rd14' := rd14
  rw [show UInt256.isZero ⟨1⟩ = ⟨0⟩ by native_decide] at rd14'
  have rd15 := rd14'.jumpiNT hd14 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by simp only [List.length_cons]; omega)
  have rd18 := rd15.pop hd15 (by simp only [List.length_cons]; omega)
    |>.push1 ⟨2⟩ hd16 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd19⟩ := rd18.sload hd18 (by simp only [List.length_cons]; omega)
  have rd21 := rd19.push1 ⟨8⟩ hd19 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd22⟩ := rd21.sload hd21 (by simp only [List.length_cons]; omega)
  have hcountRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨8⟩ ⟨0⟩)) =
        (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) := by
    simpa [solcSlotWord] using hcount
  have rd23 := rd22.eq hd22 (by simp only [List.length_cons]; omega)
  have rd23' := rd23
  rw [hcountRaw, uInt256_eq_self] at rd23'
  have rd24 := rd23'.dup1 hd23 (by simp only [List.length_cons]; omega)
  have rd27 := rd24.push2 guardPc hd24 (by simp only [List.length_cons]; omega)
  have rdg0 := rd27.jumpiT hd27 one_ne_zero_uint hguard
    (by simp only [List.length_cons]; omega)
  have rdg4 := rdg0.jumpdest hdg0 (by simp only [List.length_cons]; omega)
    |>.push2 successPc hdg1 (by simp only [List.length_cons]; omega)
  have rds0 := rdg4.jumpiT hdg4 one_ne_zero_uint hsuccess
    (by simp only [List.length_cons]; omega)
  have rds2 := rds0.jumpdest hds0 (by simp only [List.length_cons]; omega)
    |>.pop hds1 (by simp only [List.length_cons]; omega)
    |>.push1 ⟨9⟩ hds2 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rds5⟩ := rds2.sload hds4 (by simp only [List.length_cons]; omega)
  have rds6 := rds5.swap1 hds5 (by omega)
  exact ⟨_, _, rds6.jump hds6 hret (by simp only [List.length_cons]; omega)⟩

theorem RD.cureTellRoutineCountFalseToTimeTail {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {pc guardPc successPc ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : cureTellCountSuccessWf code pc guardPc successPc)
    (hlive : solcSlotWord σ ee ⟨1⟩ = ⟨0⟩)
    (hcount : solcSlotWord σ ee ⟨8⟩ ≠ solcSlotWord σ ee ⟨2⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (cureTellCountTimeTailPc pc)
      (⟨0⟩ :: ⟨0⟩ :: ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd6, hd8, hd9, hd10, hd11, hd14, hd15, hd16,
      hd18, hd19, hd21, hd22, hd23, hd24, hd27, _hd28, _hd29, _hd31, _hd32,
      _hd33, _hd34, _hguardEq, _hdg0, _hdg1, _hdg4, _hds0, _hds1, _hds2,
      _hds4, _hds5, _hds6⟩
  have rd5 := evm_run h with [
    raw jumpdest hd0 (by simp only [List.length_cons]; omega),
    raw push1 ⟨0⟩ hd1 (by simp only [List.length_cons]; omega),
    raw push1 ⟨1⟩ hd3 (by simp only [List.length_cons]; omega)]
  obtain ⟨_, _, rd6⟩ := rd5.sload hd5 (by simp only [List.length_cons]; omega)
  have hliveRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) = ⟨0⟩ := by
    simpa [solcSlotWord] using hlive
  rw [hliveRaw] at rd6
  have rd9 := rd6.push1 ⟨0⟩ hd6 (by simp only [List.length_cons]; omega)
    |>.eq hd8 (by simp only [List.length_cons]; omega)
  have rd9' := rd9
  rw [uInt256_eq_self] at rd9'
  have rd10 := rd9'.dup1 hd9 (by simp only [List.length_cons]; omega)
  have rd14 := rd10.iszero hd10 (by simp only [List.length_cons]; omega)
    |>.push2 guardPc hd11 (by simp only [List.length_cons]; omega)
  have rd14' := rd14
  rw [show UInt256.isZero ⟨1⟩ = ⟨0⟩ by native_decide] at rd14'
  have rd15 := rd14'.jumpiNT hd14 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by simp only [List.length_cons]; omega)
  have rd18 := rd15.pop hd15 (by simp only [List.length_cons]; omega)
    |>.push1 ⟨2⟩ hd16 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd19⟩ := rd18.sload hd18 (by simp only [List.length_cons]; omega)
  have rd21 := rd19.push1 ⟨8⟩ hd19 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd22⟩ := rd21.sload hd21 (by simp only [List.length_cons]; omega)
  have hcountRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨8⟩ ⟨0⟩)) ≠
        (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) := by
    intro hraw
    exact hcount (by simpa [solcSlotWord] using hraw)
  have heq0 :
      UInt256.eq
        (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨8⟩ ⟨0⟩))
        (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) = ⟨0⟩ := by
    exact u256_eq_of_ne hcountRaw
  have rd23 := rd22.eq hd22 (by simp only [List.length_cons]; omega)
  have rd23' := rd23
  rw [heq0] at rd23'
  have rd24 := rd23'.dup1 hd23 (by simp only [List.length_cons]; omega)
  have rd27 := rd24.push2 guardPc hd24 (by simp only [List.length_cons]; omega)
  have rd28 := rd27.jumpiNT hd27 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa [cureTellCountTimeTailPc] using rd28⟩

@[reducible] def cureTellTimeTailSuccessWf
    (code : ByteArray) (pc guardPc successPc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let g1 := guardPc + ⟨1⟩
  let g4 := g1 + UInt256.ofNat 3
  let s1 := successPc + ⟨1⟩
  let s2 := s1 + ⟨1⟩
  let s4 := s2 + UInt256.ofNat 2
  let s5 := s4 + ⟨1⟩
  let s6 := s5 + ⟨1⟩
  decode code pc = some (.POP, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode code p3 = some (.SLOAD, .none)
  ∧ decode code p4 = some (.TIMESTAMP, .none)
  ∧ decode code p5 = some (.LT, .none)
  ∧ decode code p6 = some (.ISZERO, .none)
  ∧ guardPc = p6 + ⟨1⟩
  ∧ decode code guardPc = some (.JUMPDEST, .none)
  ∧ decode code g1 = some (.Push .PUSH2, some (successPc, 2))
  ∧ decode code g4 = some (.JUMPI, .none)
  ∧ decode code successPc = some (.JUMPDEST, .none)
  ∧ decode code s1 = some (.POP, .none)
  ∧ decode code s2 = some (.Push .PUSH1, some (⟨9⟩, 1))
  ∧ decode code s4 = some (.SLOAD, .none)
  ∧ decode code s5 = some (.SWAP1, .none)
  ∧ decode code s6 = some (.JUMP, .none)

set_option maxHeartbeats 1000000 in
theorem RD.cureTellTimeTailSuccess {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc guardPc successPc ret junk keep : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (junk :: keep :: ret :: R) mem (UInt256.ofNat 3) rdata
      (cA, σ) k C)
    (hwf : cureTellTimeTailSuccessWf code pc guardPc successPc)
    (htime : (solcSlotWord σ ee ⟨4⟩).toNat ≤ (UInt256.ofNat ee.header.timestamp).toNat)
    (hsuccess : (D_J code 0).contains successPc = true)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      ((σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨9⟩ ⟨0⟩)) :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd4, hd5, hd6, hguardPc, hdg0, hdg1, hdg4, hds0, hds1, hds2,
      hds4, hds5, hds6⟩
  have rd1 := h.pop hd0 (by simp only [List.length_cons]; omega)
  have rd2 := rd1.push1 ⟨4⟩ hd1 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd4⟩ := rd2.sload hd2 (by simp only [List.length_cons]; omega)
  have hwhenRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨4⟩ ⟨0⟩)) =
        solcSlotWord σ ee ⟨4⟩ := by
    rfl
  rw [hwhenRaw] at rd4
  have rd5 := rd4.timestamp hd4 (by simp only [List.length_cons]; omega)
  have rd6 := rd5.lt hd5 (by simp only [List.length_cons]; omega)
  have rd6' := rd6
  rw [ult_zero htime] at rd6'
  have rdg0 := rd6'.iszero hd6 (by simp only [List.length_cons]; omega)
  have rdg0' := rdg0
  rw [show UInt256.isZero ⟨0⟩ = ⟨1⟩ by native_decide] at rdg0'
  rw [hguardPc] at hdg0 hdg1 hdg4
  have rdg4 := rdg0'.jumpdest hdg0 (by simp only [List.length_cons]; omega)
    |>.push2 successPc hdg1 (by simp only [List.length_cons]; omega)
  have rds0 := rdg4.jumpiT hdg4 one_ne_zero_uint hsuccess
    (by simp only [List.length_cons]; omega)
  have rds2 := rds0.jumpdest hds0 (by simp only [List.length_cons]; omega)
    |>.pop hds1 (by simp only [List.length_cons]; omega)
    |>.push1 ⟨9⟩ hds2 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rds5⟩ := rds2.sload hds4 (by simp only [List.length_cons]; omega)
  have rds6 := rds5.swap1 hds5 (by omega)
  exact ⟨_, _, rds6.jump hds6 hret (by simp only [List.length_cons]; omega)⟩

theorem cureTellCountSuccessWf_concrete :
    cureTellCountSuccessWf cureBytecode ⟨2232⟩ ⟨2267⟩ ⟨2326⟩ := by
  unfold cureTellCountSuccessWf
  repeat' first | apply And.intro | native_decide

theorem cureTellTimeTailSuccessWf_concrete :
    cureTellTimeTailSuccessWf cureBytecode (cureTellCountTimeTailPc ⟨2232⟩)
      ⟨2267⟩ ⟨2326⟩ := by
  unfold cureTellTimeTailSuccessWf cureTellCountTimeTailPc
  repeat' first | apply And.intro | native_decide

theorem RD.cureTellRoutineTimeSuccessConcrete {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨2232⟩ (ret :: R) mem (UInt256.ofNat 3) rdata
      (cA, σ) k C)
    (hlive : solcSlotWord σ ee ⟨1⟩ = ⟨0⟩)
    (hcount : solcSlotWord σ ee ⟨8⟩ ≠ solcSlotWord σ ee ⟨2⟩)
    (htime : (solcSlotWord σ ee ⟨4⟩).toNat ≤ (UInt256.ofNat ee.header.timestamp).toNat)
    (hsuccess : (D_J cureBytecode 0).contains ⟨2326⟩ = true)
    (hret : (D_J cureBytecode 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ret
      ((σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨9⟩ ⟨0⟩)) :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, htail⟩ := RD.cureTellRoutineCountFalseToTimeTail
    (code := cureBytecode) (g := g) (s0 := s0) (ee := ee) (pc := ⟨2232⟩)
    (guardPc := ⟨2267⟩) (successPc := ⟨2326⟩) (ret := ret) (R := R)
    h cureTellCountSuccessWf_concrete hlive hcount hov
  exact RD.cureTellTimeTailSuccess (code := cureBytecode) (g := g) (s0 := s0)
    (ee := ee) (pc := cureTellCountTimeTailPc ⟨2232⟩) (guardPc := ⟨2267⟩)
    (successPc := ⟨2326⟩) (ret := ret) (junk := ⟨0⟩) (keep := ⟨0⟩) (R := R)
    htail cureTellTimeTailSuccessWf_concrete htime hsuccess hret hov

theorem RD.cureTellTimeTailGuardFalseConcrete {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret junk keep : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 (cureTellCountTimeTailPc ⟨2232⟩)
      (junk :: keep :: ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (htime : (UInt256.ofNat ee.header.timestamp).toNat < (solcSlotWord σ ee ⟨4⟩).toNat)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ⟨2272⟩ (keep :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases cureTellTimeTailSuccessWf_concrete with
    ⟨hd0, hd1, hd2, hd4, hd5, hd6, hguardPc, hdg0, hdg1, hdg4, _hds0,
      _hds1, _hds2, _hds4, _hds5, _hds6⟩
  have rd1 := h.pop hd0 (by simp only [List.length_cons]; omega)
  have rd2 := rd1.push1 ⟨4⟩ hd1 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd4⟩ := rd2.sload hd2 (by simp only [List.length_cons]; omega)
  have hwhenRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨4⟩ ⟨0⟩)) =
        solcSlotWord σ ee ⟨4⟩ := by
    rfl
  rw [hwhenRaw] at rd4
  have rd5 := rd4.timestamp hd4 (by simp only [List.length_cons]; omega)
  have rd6 := rd5.lt hd5 (by simp only [List.length_cons]; omega)
  have rd6' := rd6
  rw [ult_one htime] at rd6'
  have rdg0 := rd6'.iszero hd6 (by simp only [List.length_cons]; omega)
  have rdg0' := rdg0
  rw [show UInt256.isZero ⟨1⟩ = ⟨0⟩ by native_decide] at rdg0'
  rw [hguardPc] at hdg0 hdg1 hdg4
  have rdg4 := rdg0'.jumpdest hdg0 (by simp only [List.length_cons]; omega)
    |>.push2 ⟨2326⟩ hdg1 (by simp only [List.length_cons]; omega)
  have rdrev := rdg4.jumpiNT hdg4 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa [cureTellCountTimeTailPc] using rdrev⟩

theorem RD.cureTellRoutineLiveNonzeroToRevertConcrete {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨2232⟩ (ret :: R) mem (UInt256.ofNat 3) rdata
      (cA, σ) k C)
    (hlive : solcSlotWord σ ee ⟨1⟩ ≠ ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ⟨2272⟩ (⟨0⟩ :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases cureTellCountSuccessWf_concrete with
    ⟨hd0, hd1, hd3, hd5, hd6, hd8, hd9, hd10, hd11, hd14, _hd15, _hd16,
      _hd18, _hd19, _hd21, _hd22, _hd23, _hd24, _hd27, _hd28, _hd29, _hd31,
      _hd32, _hd33, _hd34, hguardEq, hdg0, hdg1, hdg4, _hds0, _hds1, _hds2,
      _hds4, _hds5, _hds6⟩
  have rd5 := evm_run h with [
    raw jumpdest hd0 (by simp only [List.length_cons]; omega),
    raw push1 ⟨0⟩ hd1 (by simp only [List.length_cons]; omega),
    raw push1 ⟨1⟩ hd3 (by simp only [List.length_cons]; omega)]
  obtain ⟨_, _, rd6⟩ := rd5.sload hd5 (by simp only [List.length_cons]; omega)
  have hliveRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) ≠ ⟨0⟩ := by
    simpa [solcSlotWord] using hlive
  have heq0 :
      UInt256.eq ⟨0⟩
        (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
        ⟨0⟩ := by
    exact u256_eq_of_ne (fun hraw => hliveRaw hraw.symm)
  have rd9 := rd6.push1 ⟨0⟩ hd6 (by simp only [List.length_cons]; omega)
    |>.eq hd8 (by simp only [List.length_cons]; omega)
  have rd9' := rd9
  rw [heq0] at rd9'
  have rd10 := rd9'.dup1 hd9 (by simp only [List.length_cons]; omega)
  have rd14 := rd10.iszero hd10 (by simp only [List.length_cons]; omega)
    |>.push2 ⟨2267⟩ hd11 (by simp only [List.length_cons]; omega)
  have rd14' := rd14
  rw [show UInt256.isZero ⟨0⟩ = ⟨1⟩ by native_decide] at rd14'
  have rdg0 := rd14'.jumpiT hd14 one_ne_zero_uint (by jump_dest)
    (by simp only [List.length_cons]; omega)
  rw [hguardEq] at hdg0 hdg1 hdg4
  have rdg4 := rdg0.jumpdest hdg0 (by simp only [List.length_cons]; omega)
    |>.push2 ⟨2326⟩ hdg1 (by simp only [List.length_cons]; omega)
  have rdrev := rdg4.jumpiNT hdg4 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa using rdrev⟩

theorem cureDispatchTell {I : ExecutionEnv}
    (hsel : selIs I (cureSelBytes 16)) :
    dispatchMsg contract I.calldata = some tellTransition := by
  have hcd : I.calldata.extract 0 4 = cureSelBytes 16 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some tellTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, cureSelBytes,
    cureAmtSelectorBytes, cureCageSelectorBytes, cureDenySelectorBytes,
    cureDropSelectorBytes, cureFileSelectorBytes, cureLCountSelectorBytes,
    cureLiftSelectorBytes, cureListSelectorBytes, cureLiveSelectorBytes,
    cureLoadSelectorBytes, cureLoadedSelectorBytes, curePosSelectorBytes,
    cureRelySelectorBytes, cureSaySelectorBytes, cureSrcsSelectorBytes,
    cureTCountSelectorBytes, cureTellSelectorBytes]
  native_decide

theorem cureDecode_tell {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (tellTransition.params.map Param.name)
      (transitionSignature tellTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem cureReachTellBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cureSelBytes 16)) :
    ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨570⟩
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : cureSelWord I = ⟨0x53d700e5⟩ :=
    cureSelWord_eq_of_beq I hsz 0x53 0xd7 0x00 0xe5 ⟨0x53d700e5⟩
      (by native_decide) (by simpa [cureSelBytes] using hsel)
  obtain ⟨_, _, h185⟩ := cureReachLowUpperFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨570⟩ 1 h185 (fun j hj => cureLowUpperArmsWellFormed j (by omega))
    (fun j hj => by
      interval_cases j
      · rw [hsw]; native_decide)
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide) (by simp)

theorem cureTellReturn_count {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (cureSelBytes 16))
    (hlive : tellLiveWord σ I = ⟨0⟩)
    (hcount : tellLCountWord σ I = tellSrcsLenWord σ I) :
    RDret cureBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (cA, σ)
      (UInt256.toByteArray (tellSayWord σ I)) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (cureSelBytes 16) rfl hsel
  have hreach := cureReachTellBody (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hentry : solcGetterEntryWf cureBytecode ⟨570⟩ ⟨343⟩ ⟨2232⟩ := by
    unfold solcGetterEntryWf
    repeat' first | apply And.intro | native_decide
  have hretmem : solcReturnWordFromMemWf cureBytecode ⟨343⟩ := by
    unfold solcReturnWordFromMemWf
    repeat' first | apply And.intro | native_decide
  obtain ⟨_, _, hroutine⟩ := RD.solcGetterThunk hreach hentry (by jump_dest)
  obtain ⟨_, _, hretPc⟩ := RD.cureTellRoutineCountSuccess
    (code := cureBytecode) (g := Sat256.ofUInt256 g)
    (s0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (ee := I)
    (pc := ⟨2232⟩) (guardPc := ⟨2267⟩) (successPc := ⟨2326⟩)
    (ret := ⟨343⟩) (R := [cureSelWord I]) hroutine cureTellCountSuccessWf_concrete
    (by simpa [tellLiveWord, cureSlotWord] using hlive)
    (by simpa [tellLCountWord, tellSrcsLenWord, cureSlotWord] using hcount)
    (by jump_dest) (by jump_dest) (by jump_dest) (by simp)
  have hret := RD.solcReturnWordFromMem
    (pc := ⟨343⟩) (val := tellSayWord σ I) (ret := cureSelWord I) (R := [])
    (memout := solcReturnMem (tellSayWord σ I))
    (by simpa [tellSayWord, cureSlotWord] using hretPc)
    hretmem
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64 (tellSayWord σ I))
    (solcReturnMem_read128 (tellSayWord σ I))
    (by simp)
  simpa using hret

theorem cureTellReturn_time {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (cureSelBytes 16))
    (hlive : tellLiveWord σ I = ⟨0⟩)
    (hcount : tellLCountWord σ I ≠ tellSrcsLenWord σ I)
    (htime : (tellWhenWord σ I).toNat ≤ (tellTimestampWord I).toNat) :
    RDret cureBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (cA, σ)
      (UInt256.toByteArray (tellSayWord σ I)) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (cureSelBytes 16) rfl hsel
  have hreach := cureReachTellBody (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hentry : solcGetterEntryWf cureBytecode ⟨570⟩ ⟨343⟩ ⟨2232⟩ := by
    unfold solcGetterEntryWf
    repeat' first | apply And.intro | native_decide
  have hretmem : solcReturnWordFromMemWf cureBytecode ⟨343⟩ := by
    unfold solcReturnWordFromMemWf
    repeat' first | apply And.intro | native_decide
  obtain ⟨_, _, hroutine⟩ := RD.solcGetterThunk hreach hentry (by jump_dest)
  obtain ⟨_, _, hretPc⟩ := RD.cureTellRoutineTimeSuccessConcrete
    (g := Sat256.ofUInt256 g)
    (s0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (ee := I)
    (ret := ⟨343⟩) (R := [cureSelWord I]) hroutine
    (by simpa [tellLiveWord, cureSlotWord] using hlive)
    (by simpa [tellLCountWord, tellSrcsLenWord, cureSlotWord] using hcount)
    (by simpa [tellWhenWord, tellTimestampWord, cureSlotWord] using htime)
    (by jump_dest) (by jump_dest) (by simp)
  have hret := RD.solcReturnWordFromMem
    (pc := ⟨343⟩) (val := tellSayWord σ I) (ret := cureSelWord I) (R := [])
    (memout := solcReturnMem (tellSayWord σ I))
    (by simpa [tellSayWord, cureSlotWord] using hretPc)
    hretmem
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64 (tellSayWord σ I))
    (solcReturnMem_read128 (tellSayWord σ I))
    (by simp)
  simpa using hret

noncomputable def cureTellRevertLiteralMem : ByteArray :=
  cureBytecode.write 3826 (solcErrorStringMem2 ⟨37⟩ solcFreePtrMem) 196 37

theorem solcErrorStringMem2_read64 (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem2 len mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem2
  rw [toByteArray_write_read_below_of_gap len _ 164 64
      (by rw [solcErrorStringMem1_size hmem]; omega) (by omega)
      (by rw [solcErrorStringMem1_size hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [solcErrorStringMem0_size hmem]; omega) (by omega)
      (by rw [solcErrorStringMem0_size hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 64
      (by omega) (by omega) (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread64

theorem cureTellRevertLiteralMem_size :
    cureTellRevertLiteralMem.size = 233 := by
  unfold cureTellRevertLiteralMem
  rw [show (196 : Nat) = (solcErrorStringMem2 ⟨37⟩ solcFreePtrMem).size by
      rw [solcErrorStringMem2_size ⟨37⟩ solcFreePtrMem_size]]
  rw [write_end_size_from cureBytecode (solcErrorStringMem2 ⟨37⟩ solcFreePtrMem)
    3826 37 (by decide) (by native_decide)]
  rw [solcErrorStringMem2_size ⟨37⟩ solcFreePtrMem_size]

theorem cureTellRevertLiteralMem_read64 :
    cureTellRevertLiteralMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold cureTellRevertLiteralMem
  rw [show (196 : Nat) = (solcErrorStringMem2 ⟨37⟩ solcFreePtrMem).size by
      rw [solcErrorStringMem2_size ⟨37⟩ solcFreePtrMem_size]]
  rw [write_read_below_end_from cureBytecode (solcErrorStringMem2 ⟨37⟩ solcFreePtrMem)
    3826 37 64 (by decide) (by native_decide)
    (by rw [solcErrorStringMem2_size ⟨37⟩ solcFreePtrMem_size]; omega)]
  exact solcErrorStringMem2_read64 ⟨37⟩ solcFreePtrMem_size solcFreePtrMem_read64

theorem cureTellRevertLiteralMem_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ cureTellRevertLiteralMem.size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        (cureTellRevertLiteralMem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [cureTellRevertLiteralMem_size]; decide)
    (by decide)
    cureTellRevertLiteralMem_read64

theorem RD.cureTellRevertTail {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {stk : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD cureBytecode ee g s0 ⟨2272⟩ stk solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : stk.length + 8 ≤ 1024) :
    RDrev cureBytecode g s0 := by
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost solcFreePtrMem_mload64 (by rfl) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdHeader := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 solcFreePtrMem) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 solcFreePtrMem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨37⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 ⟨37⟩ solcFreePtrMem) (UInt256.ofNat 7)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨3826⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨37⟩ (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw codecopy
      (Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat 7).toNat 196 37)) -
        Cₘ (UInt256.ofNat 7))
      cureTellRevertLiteralMem (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)]
  exact evm_run rdHeader with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost cureTellRevertLiteralMem_mload64 (by rfl) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev
      (Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat 8).toNat 128 132)) -
        Cₘ (UInt256.ofNat 8))
      (by native_decide) mem_cost (by evm_ov)]

theorem cureTellBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = cureBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (cureSelBytes 16))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (cureSelBytes 16) rfl hsel
  have hdispatch := cureDispatchTell hsel
  have hdecode := cureDecode_tell hsz
  have hliveWord : tellLiveWord σ_evm I = tellLiveWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
  have hsrcsLenWord : tellSrcsLenWord σ_evm I = tellSrcsLenWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  have hwhenWord : tellWhenWord σ_evm I = tellWhenWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨4⟩ ⟨0⟩
  have hlcountWord : tellLCountWord σ_evm I = tellLCountWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
  have hsayWord : tellSayWord σ_evm I = tellSayWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨9⟩ ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (tellSayWord σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (tellSayWord σ_evm I).toNat)] := by
    rw [hsayWord]
  have henc :
      returnEquiv (UInt256.toByteArray (tellSayWord σ_evm I))
        (some [(.int (Int.ofNat (tellSayWord σ_evm I).toNat))])
        tellTransition.returnType := by
    rw [show tellTransition.returnType = [uint256] by rfl]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (tellSayWord σ_evm I))
  have hreach := cureReachTellBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hentry : solcGetterEntryWf cureBytecode ⟨570⟩ ⟨343⟩ ⟨2232⟩ := by
    unfold solcGetterEntryWf
    repeat' first | apply And.intro | native_decide
  obtain ⟨_, _, hroutine⟩ := RD.solcGetterThunk hreach hentry (by jump_dest)
  by_cases hliveEvm : tellLiveWord σ_evm I = ⟨0⟩
  · have hliveSolm : tellLiveWord σ_solm I = ⟨0⟩ := by
      rw [← hliveWord]
      exact hliveEvm
    by_cases hcountEvm : tellLCountWord σ_evm I = tellSrcsLenWord σ_evm I
    · have hcountSolm : tellLCountWord σ_solm I = tellSrcsLenWord σ_solm I := by
        rw [← hlcountWord, ← hsrcsLenWord]
        exact hcountEvm
      have hguard := cureTellGuardEval_countTrue (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
        hliveSolm hcountSolm
      have hbody := cureTellSourceBodyOk (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv
        (by simpa [tellGuardExpr] using hguard)
      have hret := cureTellReturn_count (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hwv hsize hsel hliveEvm hcountEvm
      exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval
        hAccounts henc
    · have hcountSolm : tellLCountWord σ_solm I ≠ tellSrcsLenWord σ_solm I := by
        intro hbad
        exact hcountEvm (by rw [hlcountWord, hsrcsLenWord, hbad])
      by_cases htimeEvm : (tellWhenWord σ_evm I).toNat ≤ (tellTimestampWord I).toNat
      · have htimeSolm : (tellWhenWord σ_solm I).toNat ≤ (tellTimestampWord I).toNat := by
          rw [← hwhenWord]
          exact htimeEvm
        have hguard := cureTellGuardEval_timeTrue (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
          hliveSolm hcountSolm htimeSolm
        have hbody := cureTellSourceBodyOk (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv
          (by simpa [tellGuardExpr] using hguard)
        have hret := cureTellReturn_time (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hwv hsize hsel hliveEvm hcountEvm htimeEvm
        exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval
          hAccounts henc
      · have htimeSolm : (tellTimestampWord I).toNat < (tellWhenWord σ_solm I).toNat := by
          rw [← hwhenWord]
          exact Nat.lt_of_not_ge htimeEvm
        have hguard := cureTellGuardEval_false (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
          hliveSolm hcountSolm htimeSolm
        have hbody := cureTellSourceBodyReverts (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv
          (by simpa [tellGuardExpr] using hguard)
        obtain ⟨_, _, htail⟩ := RD.cureTellRoutineCountFalseToTimeTail
          (code := cureBytecode) (g := Sat256.ofUInt256 g)
          (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (ee := I)
          (pc := ⟨2232⟩) (guardPc := ⟨2267⟩) (successPc := ⟨2326⟩)
          (ret := ⟨343⟩) (R := [cureSelWord I])
          hroutine cureTellCountSuccessWf_concrete
          (by simpa [tellLiveWord, cureSlotWord] using hliveEvm)
          (by simpa [tellLCountWord, tellSrcsLenWord, cureSlotWord] using hcountEvm)
          (by simp)
        obtain ⟨_, _, hrevPc⟩ := RD.cureTellTimeTailGuardFalseConcrete
          (g := Sat256.ofUInt256 g)
          (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (ee := I) (ret := ⟨343⟩) (junk := ⟨0⟩) (keep := ⟨0⟩)
          (R := [cureSelWord I]) htail
          (by simpa [tellWhenWord, tellTimestampWord, cureSlotWord]
            using Nat.lt_of_not_ge htimeEvm)
          (by simp)
        have hrev := RD.cureTellRevertTail hrevPc (by simp)
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hliveSolm : tellLiveWord σ_solm I ≠ ⟨0⟩ := by
      intro hbad
      exact hliveEvm (by rw [hliveWord, hbad])
    have hguard := cureTellGuardEval_liveFalse (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hliveSolm
    have hbody := cureTellSourceBodyReverts (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv
      (by simpa [tellGuardExpr] using hguard)
    obtain ⟨_, _, hrevPc⟩ := RD.cureTellRoutineLiveNonzeroToRevertConcrete
      (g := Sat256.ofUInt256 g)
      (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (ee := I)
      (ret := ⟨343⟩) (R := [cureSelWord I]) hroutine
      (by simpa [tellLiveWord, cureSlotWord] using hliveEvm) (by simp)
    have hrev := RD.cureTellRevertTail hrevPc (by simp)
    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

end Benchmarks.Dss.Cure
