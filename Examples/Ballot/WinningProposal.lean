import Examples.Ballot.Common
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Ballot

/-! ## `winningProposal()` -/

private theorem evalBinaryOp_lt_int_ok (x y : Int) :
    evalBinaryOp? .lt (.int x) (.int y) = .ok (.bool (x < y)) := by
  rfl

private theorem evalBinaryOp_gt_int_ok (x y : Int) :
    evalBinaryOp? .gt (.int x) (.int y) = .ok (.bool (x > y)) := by
  rfl

private theorem evalBinaryOp_add_int_ok (x y : Int) :
    evalBinaryOp? .add (.int x) (.int y) = .ok (.int (x + y)) := by
  rfl

def winningProposalLengthWord (sigma : AccountMap) (I : ExecutionEnv) : UInt256 :=
  sigma.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)

def winningProposalVoteCountSlot (p : UInt256) : UInt256 :=
  UInt256.mul ⟨2⟩ p + proposalsDataBase + ⟨1⟩

def winningProposalVoteCountWord (sigma : AccountMap) (I : ExecutionEnv) (p : UInt256) :
    UInt256 :=
  sigma.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (winningProposalVoteCountSlot p) ⟨0⟩)

def winningProposalLengthCurrent (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩

def winningProposalVoteCountCurrent (evm : EVM.State) (p : UInt256) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (winningProposalVoteCountSlot p)

def winningProposalCountEvaledRef (p : UInt256) : EvaledStorageRef :=
  { base := "proposals",
    steps := [.aindex (.int (Int.ofNat p.toNat)), .field "voteCount"] }

def winningProposalFrame (locals : Store) : Frame :=
  { contract := ballotContract, locals := locals }

theorem winningProposal_getElem?_insert_ne (locals : Store) {k a : Ident} (value : Value)
    (h : (k == a) = false) :
    (locals.insert k value)[a]? = locals[a]? := by
  simp [Std.HashMap.getElem?_insert, h]

theorem winningProposal_getElem?_insert_self (locals : Store) (k : Ident) (value : Value) :
    (locals.insert k value)[k]? = some value := by
  simp

def winningProposalLoopCondExpr : Expr :=
  .binary .lt (.var "p") (.arrayLength .storage proposalsRef)

def winningProposalLoopPostStmts : List Stmt :=
  [ .assign .localVar ({ base := "p" } : StorageRef)
      (.binary .add (.var "p") (.intLit 1)) ]

def winningProposalLoopBodyStmts : List Stmt :=
  [ .ite (.binary .gt (.storage (proposalF (.var "p") "voteCount"))
      (.var "winningVoteCount"))
      [ .assign .localVar ({ base := "winningVoteCount" } : StorageRef)
          (.storage (proposalF (.var "p") "voteCount")),
        .assign .localVar ({ base := "winningProposal_" } : StorageRef) (.var "p") ]
      [] ]

def winningProposalForStmt : Stmt :=
  .for [ .letDecl "p" (some uint256) (.intLit 0) ]
    winningProposalLoopCondExpr winningProposalLoopPostStmts winningProposalLoopBodyStmts

theorem winningProposalVoteCountSlot_spec (p : UInt256) :
    winningProposalVoteCountSlot p =
      proposalElemSlot (.int (Int.ofNat p.toNat)) + ⟨1⟩ := by
  unfold winningProposalVoteCountSlot proposalElemSlot
  rw [keyValueToWord_uint256]
  rw [u256_mul_comm ⟨2⟩ p, u256_mul_two_ofNat]
  rw [u256_add_comm (UInt256.ofNat (p.toNat * 2)) proposalsDataBase]

theorem winningProposalArrayIndexInBounds_ok (evm : EVM.State) (p : UInt256)
    (hbound : p.toNat < (winningProposalLengthCurrent evm).toNat) :
    arrayIndexInBounds? ballotConfig evm ballotContract.storage "proposals" []
      (.int (Int.ofNat p.toNat)) = .ok () := by
  have hboundStorage :
      p.toNat <
        UInt256.toNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩) := by
    simpa [winningProposalLengthCurrent] using hbound
  simp [arrayIndexInBounds?, storageTypeAt?, ballotConfig, ballotStorageLayout,
    ballotContract, ballotStorageDecls, proposalStructTy, uint256St, bytes32St,
    ballotStorageLocLoad_uint256, hboundStorage]

theorem winningProposalEvalLength (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "proposals" = none) :
    evalExpr? ballotConfig { contract := ballotContract, locals := locals } evm
      (.arrayLength .storage proposalsRef) =
        .ok (.int (Int.ofNat (winningProposalLengthCurrent evm).toNat)) := by
  have hbaseGet : locals["proposals"]? = none := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact hbase
  rw [evalExpr?]
  simp [resolveStorageRef?, evalStorageRef, evalStorageRefSteps, proposalsRef,
    readStorageArrayLength?, storageTypeAt?, ballotConfig, ballotStorageLayout,
    ballotContract, ballotStorageDecls, proposalStructTy, winningProposalLengthCurrent,
    EvalResult.ofOption, EvalResult.bind, bind, pure, hbaseGet]
  rw [ballotStorageLocLoad_uint256 evm ⟨2⟩]
  rfl

theorem winningProposalEvalVoteCount (evm : EVM.State) (locals : Store) (p : UInt256)
    (hbaseProposals : locals.get? "proposals" = none)
    (hp : locals.get? "p" = some (.int (Int.ofNat p.toNat)))
    (hbound : p.toNat < (winningProposalLengthCurrent evm).toNat) :
    evalExpr? ballotConfig { contract := ballotContract, locals := locals } evm
      (.storage (proposalF (.var "p") "voteCount")) =
        .ok (.int (Int.ofNat (winningProposalVoteCountCurrent evm p).toNat)) := by
  have hbase : locals.get? (proposalF (.var "p") "voteCount").base = none := by
    simpa [proposalF] using hbaseProposals
  have hpEval :
      evalExpr? ballotConfig { contract := ballotContract, locals := locals } evm
        (.var "p") = .ok (.int (Int.ofNat p.toNat)) := by
    have hpGet : locals["p"]? = some (.int (Int.ofNat p.toNat)) := by
      rw [← Std.HashMap.get?_eq_getElem?]
      exact hp
    simp [evalExpr?, hpGet, EvalResult.ofOption]
  have hboundsOk :
      arrayIndexInBounds? ballotConfig evm ballotContract.storage "proposals" []
        (.int (Int.ofNat p.toNat)) = .ok () :=
    winningProposalArrayIndexInBounds_ok evm p hbound
  have her :
      evalStorageRef ballotConfig { contract := ballotContract, locals := locals } evm
        (proposalF (.var "p") "voteCount") = .ok (winningProposalCountEvaledRef p) := by
    simp only [proposalF, evalStorageRef, evalStorageRefSteps.eq_def,
      evalStorageRefStep.eq_def, hpEval, valueToKey?, EvalResult.ofOption, EvalResult.bind,
      bind, pure, List.nil_append]
    rw [hboundsOk]
    simp [winningProposalCountEvaledRef]
  have hty :
      storageTypeAt? ballotContract.storage (winningProposalCountEvaledRef p) =
        some (.elem (.int uint256Int)) := by
    simp [winningProposalCountEvaledRef, storageTypeAt?, storageTypeStep?, ballotContract,
      ballotStorageDecls, proposalStructTy, uint256St]
  have hloc :
      ballotConfig.storage.layout (winningProposalCountEvaledRef p) =
        fun _ => some (wordLoc (winningProposalVoteCountSlot p)) := by
    funext evm'
    simp [winningProposalCountEvaledRef, winningProposalVoteCountSlot_spec, ballotConfig,
      ballotStorageLayout]
  have hload :
      storageLocLoad evm (wordLoc (winningProposalVoteCountSlot p)) =
        .int (Int.ofNat (winningProposalVoteCountCurrent evm p).toNat) := by
    simpa [winningProposalVoteCountCurrent] using
      (ballotStorageLocLoad_uint256 evm (winningProposalVoteCountSlot p))
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase) (her := her)
    (hty := hty) (hloc := hloc)]
  rw [hload]

theorem winningProposalEvalVar (evm : EVM.State) (locals : Store) (name : Ident)
    (v : UInt256) (h : locals.get? name = some (.int (Int.ofNat v.toNat))) :
    evalExpr? ballotConfig { contract := ballotContract, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat v.toNat)) := by
  have hget : locals[name]? = some (.int (Int.ofNat v.toNat)) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact h
  simp [evalExpr?, hget, EvalResult.ofOption]

theorem winningProposalAssignLocal (evm : EVM.State) (locals : Store) (name : Ident)
    (old value : UInt256) (h : locals.get? name = some (.int (Int.ofNat old.toNat))) :
    assignStorageRef? ballotConfig (winningProposalFrame locals) evm .localVar
      ({ base := name } : StorageRef) (.int (Int.ofNat value.toNat)) =
        .ok (winningProposalFrame (locals.insert name (.int (Int.ofNat value.toNat))), evm) := by
  have hget : locals[name]? = some (.int (Int.ofNat old.toNat)) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact h
  simp [winningProposalFrame, assignStorageRef?, hget, updateLocalPath?, EvalResult.bind, bind,
    pure]

theorem winningProposalEvalLoopCond (evm : EVM.State) (locals : Store) (p : UInt256)
    (hbase : locals.get? "proposals" = none)
    (hp : locals.get? "p" = some (.int (Int.ofNat p.toNat))) :
    evalExpr? ballotConfig { contract := ballotContract, locals := locals } evm
      winningProposalLoopCondExpr =
        .ok (.bool (Int.ofNat p.toNat <
          Int.ofNat (winningProposalLengthCurrent evm).toNat)) := by
  rw [winningProposalLoopCondExpr, evalExpr?]
  rw [winningProposalEvalVar evm locals "p" p hp]
  rw [winningProposalEvalLength evm locals hbase]
  simp only [EvalResult.bind, bind, pure]
  change evalBinaryOp? .lt (.int (Int.ofNat p.toNat))
      (.int (Int.ofNat (winningProposalLengthCurrent evm).toNat)) =
    .ok (.bool (Int.ofNat p.toNat < Int.ofNat (winningProposalLengthCurrent evm).toNat))
  rw [evalBinaryOp_lt_int_ok]
  all_goals decide

theorem winningProposalEvalLoopCond_true (evm : EVM.State) (locals : Store) (p : UInt256)
    (hbase : locals.get? "proposals" = none)
    (hp : locals.get? "p" = some (.int (Int.ofNat p.toNat)))
    (hbound : p.toNat < (winningProposalLengthCurrent evm).toNat) :
    evalExpr? ballotConfig { contract := ballotContract, locals := locals } evm
      winningProposalLoopCondExpr = .ok (.bool true) := by
  rw [winningProposalEvalLoopCond evm locals p hbase hp]
  rw [show decide (Int.ofNat p.toNat <
      Int.ofNat (winningProposalLengthCurrent evm).toNat) = true
    from decide_eq_true (Int.ofNat_lt_ofNat_of_lt hbound)]

theorem winningProposalEvalLoopCond_false (evm : EVM.State) (locals : Store) (p : UInt256)
    (hbase : locals.get? "proposals" = none)
    (hp : locals.get? "p" = some (.int (Int.ofNat p.toNat)))
    (hbound : (winningProposalLengthCurrent evm).toNat ≤ p.toNat) :
    evalExpr? ballotConfig { contract := ballotContract, locals := locals } evm
      winningProposalLoopCondExpr = .ok (.bool false) := by
  rw [winningProposalEvalLoopCond evm locals p hbase hp]
  rw [show decide (Int.ofNat p.toNat <
      Int.ofNat (winningProposalLengthCurrent evm).toNat) = false
    from decide_eq_false (by
      intro hlt
      exact Nat.not_lt_of_ge hbound (Int.ofNat_lt.mp hlt))]

theorem winningProposalEvalVoteGt (evm : EVM.State) (locals : Store)
    (p winningVoteCount : UInt256) (hbase : locals.get? "proposals" = none)
    (hp : locals.get? "p" = some (.int (Int.ofNat p.toNat)))
    (hcount : locals.get? "winningVoteCount" =
      some (.int (Int.ofNat winningVoteCount.toNat)))
    (hbound : p.toNat < (winningProposalLengthCurrent evm).toNat) :
    evalExpr? ballotConfig { contract := ballotContract, locals := locals } evm
      (.binary .gt (.storage (proposalF (.var "p") "voteCount")) (.var "winningVoteCount")) =
        .ok (.bool (Int.ofNat (winningProposalVoteCountCurrent evm p).toNat >
          Int.ofNat winningVoteCount.toNat)) := by
  rw [evalExpr?]
  rw [winningProposalEvalVoteCount evm locals p hbase hp hbound]
  rw [winningProposalEvalVar evm locals "winningVoteCount" winningVoteCount hcount]
  simp only [EvalResult.bind, bind, pure]
  change evalBinaryOp? .gt (.int (Int.ofNat (winningProposalVoteCountCurrent evm p).toNat))
      (.int (Int.ofNat winningVoteCount.toNat)) =
    .ok (.bool (Int.ofNat (winningProposalVoteCountCurrent evm p).toNat >
      Int.ofNat winningVoteCount.toNat))
  rw [evalBinaryOp_gt_int_ok]
  all_goals decide

theorem winningProposalEvalVoteGt_true (evm : EVM.State) (locals : Store)
    (p winningVoteCount : UInt256) (hbase : locals.get? "proposals" = none)
    (hp : locals.get? "p" = some (.int (Int.ofNat p.toNat)))
    (hcount : locals.get? "winningVoteCount" =
      some (.int (Int.ofNat winningVoteCount.toNat)))
    (hbound : p.toNat < (winningProposalLengthCurrent evm).toNat)
    (hgt : winningVoteCount.toNat < (winningProposalVoteCountCurrent evm p).toNat) :
    evalExpr? ballotConfig { contract := ballotContract, locals := locals } evm
      (.binary .gt (.storage (proposalF (.var "p") "voteCount")) (.var "winningVoteCount")) =
        .ok (.bool true) := by
  rw [winningProposalEvalVoteGt evm locals p winningVoteCount hbase hp hcount hbound]
  rw [show decide (Int.ofNat (winningProposalVoteCountCurrent evm p).toNat >
      Int.ofNat winningVoteCount.toNat) = true
    from decide_eq_true (Int.ofNat_lt_ofNat_of_lt hgt)]

theorem winningProposalEvalVoteGt_false (evm : EVM.State) (locals : Store)
    (p winningVoteCount : UInt256) (hbase : locals.get? "proposals" = none)
    (hp : locals.get? "p" = some (.int (Int.ofNat p.toNat)))
    (hcount : locals.get? "winningVoteCount" =
      some (.int (Int.ofNat winningVoteCount.toNat)))
    (hbound : p.toNat < (winningProposalLengthCurrent evm).toNat)
    (hgt : ¬ winningVoteCount.toNat < (winningProposalVoteCountCurrent evm p).toNat) :
    evalExpr? ballotConfig { contract := ballotContract, locals := locals } evm
      (.binary .gt (.storage (proposalF (.var "p") "voteCount")) (.var "winningVoteCount")) =
        .ok (.bool false) := by
  rw [winningProposalEvalVoteGt evm locals p winningVoteCount hbase hp hcount hbound]
  rw [show decide (Int.ofNat (winningProposalVoteCountCurrent evm p).toNat >
      Int.ofNat winningVoteCount.toNat) = false
    from decide_eq_false (by
      intro hlt
      exact hgt (Int.ofNat_lt.mp hlt))]

def winningProposalLoopAux (evm : EVM.State) :
    Nat → UInt256 → UInt256 → UInt256 → UInt256 × UInt256
  | 0, _p, winningVoteCount, winningProposal => (winningVoteCount, winningProposal)
  | fuel + 1, p, winningVoteCount, winningProposal =>
      let voteCount := winningProposalVoteCountCurrent evm p
      let winningVoteCount' :=
        if winningVoteCount.toNat < voteCount.toNat then voteCount else winningVoteCount
      let winningProposal' :=
        if winningVoteCount.toNat < voteCount.toNat then p else winningProposal
      winningProposalLoopAux evm fuel (p + ⟨1⟩) winningVoteCount' winningProposal'

def winningProposalResultCurrent (evm : EVM.State) : UInt256 :=
  (winningProposalLoopAux evm (winningProposalLengthCurrent evm).toNat ⟨0⟩ ⟨0⟩ ⟨0⟩).2

def winningProposalLoopAuxWord (sigma : AccountMap) (I : ExecutionEnv) :
    Nat → UInt256 → UInt256 → UInt256 → UInt256 × UInt256
  | 0, _p, winningVoteCount, winningProposal => (winningVoteCount, winningProposal)
  | fuel + 1, p, winningVoteCount, winningProposal =>
      let voteCount := winningProposalVoteCountWord sigma I p
      let winningVoteCount' :=
        if winningVoteCount.toNat < voteCount.toNat then voteCount else winningVoteCount
      let winningProposal' :=
        if winningVoteCount.toNat < voteCount.toNat then p else winningProposal
      winningProposalLoopAuxWord sigma I fuel (p + ⟨1⟩) winningVoteCount' winningProposal'

def winningProposalResultWord (sigma : AccountMap) (I : ExecutionEnv) : UInt256 :=
  (winningProposalLoopAuxWord sigma I (winningProposalLengthWord sigma I).toNat
    ⟨0⟩ ⟨0⟩ ⟨0⟩).2

def winningProposalLoopInv (evm : EVM.State) (target : UInt256 × UInt256)
    (v : Nat) (locals : Store) : Prop :=
  ∃ p winningVoteCount winningProposal,
    locals.get? "p" = some (.int (Int.ofNat p.toNat)) ∧
    locals.get? "winningVoteCount" = some (.int (Int.ofNat winningVoteCount.toNat)) ∧
    locals.get? "winningProposal_" = some (.int (Int.ofNat winningProposal.toNat)) ∧
    locals.get? "proposals" = none ∧
    p.toNat + v = (winningProposalLengthCurrent evm).toNat ∧
    p.toNat ≤ (winningProposalLengthCurrent evm).toNat ∧
    winningProposalLoopAux evm v p winningVoteCount winningProposal = target

theorem winningProposalLoopPostStep (evm : EVM.State) (locals : Store) (p : UInt256)
    (hold : locals.get? "p" = some (.int (Int.ofNat p.toNat)))
    (hsize : p.toNat + 1 < UInt256.size) :
    ExecBlock ballotConfig { contract := ballotContract, locals := locals } evm
      [ .assign .localVar ({ base := "p" } : StorageRef)
          (.binary .add (.var "p") (.intLit 1)) ]
      (.ok (winningProposalFrame
        (locals.insert "p" (.int (Int.ofNat (p + ⟨1⟩).toNat)))) evm) := by
  apply ExecBlock.consNormal
  · apply ExecStmt.assign
    · have hadd : Int.ofNat p.toNat + 1 = Int.ofNat (p + ⟨1⟩).toNat := by
        rw [add1_toNat hsize]
        norm_num
      change evalExpr? ballotConfig { contract := ballotContract, locals := locals } evm
        (.binary .add (.var "p") (.intLit 1)) =
          .ok (.int (Int.ofNat (p + ⟨1⟩).toNat))
      rw [evalExpr?]
      rw [winningProposalEvalVar evm locals "p" p hold]
      simp only [evalExpr?, EvalResult.bind, bind, pure]
      change evalBinaryOp? .add (.int (Int.ofNat p.toNat)) (.int 1) =
        .ok (.int (Int.ofNat (p + ⟨1⟩).toNat))
      rw [evalBinaryOp_add_int_ok]
      simpa [hadd]
      all_goals decide
    · exact winningProposalAssignLocal evm locals "p" p (p + ⟨1⟩) hold
  · exact ExecBlock.nil

theorem winningProposalLoopBodySkip (evm : EVM.State) (locals : Store) (p winningVoteCount : UInt256)
    (hbase : locals.get? "proposals" = none)
    (hp : locals.get? "p" = some (.int (Int.ofNat p.toNat)))
    (hcount : locals.get? "winningVoteCount" =
      some (.int (Int.ofNat winningVoteCount.toNat)))
    (hbound : p.toNat < (winningProposalLengthCurrent evm).toNat)
    (hgt : ¬ winningVoteCount.toNat < (winningProposalVoteCountCurrent evm p).toNat) :
    ExecBlock ballotConfig { contract := ballotContract, locals := locals } evm
      winningProposalLoopBodyStmts
      (.ok (winningProposalFrame locals) evm) := by
  rw [winningProposalLoopBodyStmts]
  apply ExecBlock.consNormal
  · exact ExecStmt.iteFalse
      (winningProposalEvalVoteGt_false evm locals p winningVoteCount hbase hp hcount hbound hgt)
      ExecBlock.nil
  · exact ExecBlock.nil

theorem winningProposalLoopBodyTake (evm : EVM.State) (locals : Store)
    (p winningVoteCount winningProposal : UInt256)
    (hbase : locals.get? "proposals" = none)
    (hp : locals.get? "p" = some (.int (Int.ofNat p.toNat)))
    (hcount : locals.get? "winningVoteCount" =
      some (.int (Int.ofNat winningVoteCount.toNat)))
    (hbest : locals.get? "winningProposal_" =
      some (.int (Int.ofNat winningProposal.toNat)))
    (hbound : p.toNat < (winningProposalLengthCurrent evm).toNat)
    (hgt : winningVoteCount.toNat < (winningProposalVoteCountCurrent evm p).toNat) :
    ExecBlock ballotConfig { contract := ballotContract, locals := locals } evm
      winningProposalLoopBodyStmts
      (.ok (winningProposalFrame
        ((locals.insert "winningVoteCount"
            (.int (Int.ofNat (winningProposalVoteCountCurrent evm p).toNat))).insert
          "winningProposal_" (.int (Int.ofNat p.toNat)))) evm) := by
  rw [winningProposalLoopBodyStmts]
  apply ExecBlock.consNormal
  · apply ExecStmt.iteTrue
      (winningProposalEvalVoteGt_true evm locals p winningVoteCount hbase hp hcount hbound hgt)
    apply ExecBlock.consNormal
    · apply ExecStmt.assign
      · exact winningProposalEvalVoteCount evm locals p hbase hp hbound
      · exact winningProposalAssignLocal evm locals "winningVoteCount" winningVoteCount
          (winningProposalVoteCountCurrent evm p) hcount
    · apply ExecBlock.consNormal
      · apply ExecStmt.assign
        · have hp' :
              (locals.insert "winningVoteCount"
                (.int (Int.ofNat (winningProposalVoteCountCurrent evm p).toNat))).get? "p" =
                some (.int (Int.ofNat p.toNat)) := by
            rw [store_get_ne locals (k := "winningVoteCount") (a := "p")
              (.int (Int.ofNat (winningProposalVoteCountCurrent evm p).toNat)) (by decide)]
            exact hp
          exact winningProposalEvalVar evm
            (locals.insert "winningVoteCount"
              (.int (Int.ofNat (winningProposalVoteCountCurrent evm p).toNat)))
            "p" p hp'
        · exact winningProposalAssignLocal evm
            (locals.insert "winningVoteCount"
              (.int (Int.ofNat (winningProposalVoteCountCurrent evm p).toNat)))
            "winningProposal_" winningProposal p (by
              rw [store_get_ne locals (k := "winningVoteCount") (a := "winningProposal_")
                (.int (Int.ofNat (winningProposalVoteCountCurrent evm p).toNat)) (by decide)]
              exact hbest)
      · exact ExecBlock.nil
  · exact ExecBlock.nil

theorem winningProposalForLoopReturns (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "proposals" = none)
    (hcount : locals.get? "winningVoteCount" = some (.int (Int.ofNat (0 : Nat))))
    (hbest : locals.get? "winningProposal_" = some (.int (Int.ofNat (0 : Nat)))) :
    ∃ locals',
      ExecStmt ballotConfig (winningProposalFrame locals) evm winningProposalForStmt
        (.ok (winningProposalFrame locals') evm) ∧
      winningProposalLoopInv evm
        (winningProposalLoopAux evm (winningProposalLengthCurrent evm).toNat ⟨0⟩ ⟨0⟩ ⟨0⟩)
        0 locals' := by
  let target :=
    winningProposalLoopAux evm (winningProposalLengthCurrent evm).toNat ⟨0⟩ ⟨0⟩ ⟨0⟩
  let P : Nat → Store → Prop := winningProposalLoopInv evm target
  have hfalse : ∀ L, P 0 L →
      evalExpr? ballotConfig (winningProposalFrame L) evm winningProposalLoopCondExpr =
        .ok (.bool false) := by
    rintro L ⟨p, winningVoteCount, winningProposal, hp, _hcount, _hbest, hprops,
      hvar, _hle, _hloop⟩
    exact winningProposalEvalLoopCond_false evm L p hprops hp (by omega)
  have htrue : ∀ v L, P (v + 1) L →
      evalExpr? ballotConfig (winningProposalFrame L) evm winningProposalLoopCondExpr =
        .ok (.bool true) := by
    rintro v L ⟨p, winningVoteCount, winningProposal, hp, _hcount, _hbest, hprops,
      hvar, _hle, _hloop⟩
    exact winningProposalEvalLoopCond_true evm L p hprops hp (by omega)
  have hstep : ∀ v L, P (v + 1) L →
      ∃ L1, ExecBlock ballotConfig (winningProposalFrame L) evm winningProposalLoopBodyStmts
              (.ok (winningProposalFrame L1) evm) ∧
            ∃ L', ExecBlock ballotConfig (winningProposalFrame L1) evm
              winningProposalLoopPostStmts (.ok (winningProposalFrame L') evm) ∧ P v L' := by
    rintro v L ⟨p, winningVoteCount, winningProposal, hp, hcountL, hbestL, hprops,
      hvar, hle, hloop⟩
    have hbound : p.toNat < (winningProposalLengthCurrent evm).toNat := by omega
    have hsize : p.toNat + 1 < UInt256.size := by
      have hlen : (winningProposalLengthCurrent evm).toNat < UInt256.size :=
        (winningProposalLengthCurrent evm).val.isLt
      omega
    by_cases hgt : winningVoteCount.toNat < (winningProposalVoteCountCurrent evm p).toNat
    · let voteCount := winningProposalVoteCountCurrent evm p
      let L1 :=
        (L.insert "winningVoteCount" (.int (Int.ofNat voteCount.toNat))).insert
          "winningProposal_" (.int (Int.ofNat p.toNat))
      let L2 := L1.insert "p" (.int (Int.ofNat (p + ⟨1⟩).toNat))
      have hbody :
          ExecBlock ballotConfig (winningProposalFrame L) evm winningProposalLoopBodyStmts
            (.ok (winningProposalFrame L1) evm) := by
        simpa [L1, voteCount, winningProposalFrame] using
          winningProposalLoopBodyTake evm L p winningVoteCount winningProposal hprops hp hcountL
            hbestL hbound hgt
      have hpL1 : L1.get? "p" = some (.int (Int.ofNat p.toNat)) := by
        simpa [L1, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using hp
      have hpost :
          ExecBlock ballotConfig (winningProposalFrame L1) evm winningProposalLoopPostStmts
            (.ok (winningProposalFrame L2) evm) := by
        simpa [winningProposalLoopPostStmts, L2, winningProposalFrame] using
          winningProposalLoopPostStep evm L1 p hpL1 hsize
      have hpL2 : L2.get? "p" = some (.int (Int.ofNat (p + ⟨1⟩).toNat)) := by
        simp [L2]
      have hcountL2 :
          L2.get? "winningVoteCount" = some (.int (Int.ofNat voteCount.toNat)) := by
        have hlast : L2.get? "winningVoteCount" = L1.get? "winningVoteCount" := by
          simpa [L2] using
            (store_get_ne L1 (.int (Int.ofNat (p + ⟨1⟩).toNat))
              (by native_decide : ("p" == "winningVoteCount") = false))
        have hmid :
            L1.get? "winningVoteCount" =
              (L.insert "winningVoteCount" (.int (Int.ofNat voteCount.toNat))).get?
                "winningVoteCount" := by
          simpa [L1] using
            (store_get_ne (L.insert "winningVoteCount" (.int (Int.ofNat voteCount.toNat)))
              (.int (Int.ofNat p.toNat))
              (by native_decide : ("winningProposal_" == "winningVoteCount") = false))
        rw [hlast, hmid]
        simp
      have hbestL2 :
          L2.get? "winningProposal_" = some (.int (Int.ofNat p.toNat)) := by
        have hlast : L2.get? "winningProposal_" = L1.get? "winningProposal_" := by
          simpa [L2] using
            (store_get_ne L1 (.int (Int.ofNat (p + ⟨1⟩).toNat))
              (by native_decide : ("p" == "winningProposal_") = false))
        rw [hlast]
        simp [L1]
      have hpropsL2 : L2.get? "proposals" = none := by
        simpa [L2, L1, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using hprops
      have hvarL2 : (p + ⟨1⟩).toNat + v = (winningProposalLengthCurrent evm).toNat := by
        rw [add1_toNat hsize]
        omega
      have hleL2 : (p + ⟨1⟩).toNat ≤ (winningProposalLengthCurrent evm).toNat := by
        rw [add1_toNat hsize]
        omega
      have hloopL2 :
          winningProposalLoopAux evm v (p + ⟨1⟩) voteCount p = target := by
        simpa [winningProposalLoopAux, voteCount, hgt] using hloop
      refine ⟨L1, hbody, L2, hpost, ?_⟩
      exact ⟨p + ⟨1⟩, voteCount, p, hpL2, hcountL2, hbestL2, hpropsL2, hvarL2,
        hleL2, hloopL2⟩
    · let L2 := L.insert "p" (.int (Int.ofNat (p + ⟨1⟩).toNat))
      have hbody :
          ExecBlock ballotConfig (winningProposalFrame L) evm winningProposalLoopBodyStmts
            (.ok (winningProposalFrame L) evm) := by
        simpa [winningProposalFrame] using
          winningProposalLoopBodySkip evm L p winningVoteCount hprops hp hcountL hbound hgt
      have hpost :
          ExecBlock ballotConfig (winningProposalFrame L) evm winningProposalLoopPostStmts
            (.ok (winningProposalFrame L2) evm) := by
        simpa [winningProposalLoopPostStmts, L2, winningProposalFrame] using
          winningProposalLoopPostStep evm L p hp hsize
      have hpL2 : L2.get? "p" = some (.int (Int.ofNat (p + ⟨1⟩).toNat)) := by
        simp [L2]
      have hcountL2 :
          L2.get? "winningVoteCount" = some (.int (Int.ofNat winningVoteCount.toNat)) := by
        simpa [L2, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using hcountL
      have hbestL2 :
          L2.get? "winningProposal_" = some (.int (Int.ofNat winningProposal.toNat)) := by
        simpa [L2, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using hbestL
      have hpropsL2 : L2.get? "proposals" = none := by
        simpa [L2, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using hprops
      have hvarL2 : (p + ⟨1⟩).toNat + v = (winningProposalLengthCurrent evm).toNat := by
        rw [add1_toNat hsize]
        omega
      have hleL2 : (p + ⟨1⟩).toNat ≤ (winningProposalLengthCurrent evm).toNat := by
        rw [add1_toNat hsize]
        omega
      have hloopL2 :
          winningProposalLoopAux evm v (p + ⟨1⟩) winningVoteCount winningProposal = target := by
        simpa [winningProposalLoopAux, hgt] using hloop
      refine ⟨L, hbody, L2, hpost, ?_⟩
      exact ⟨p + ⟨1⟩, winningVoteCount, winningProposal, hpL2, hcountL2, hbestL2,
        hpropsL2, hvarL2, hleL2, hloopL2⟩
  let L0 := locals.insert "p" (.int (Int.ofNat (0 : Nat)))
  have hinit :
      ExecBlock ballotConfig (winningProposalFrame locals) evm
        [ .letDecl "p" (some uint256) (.intLit 0) ] (.ok (winningProposalFrame L0) evm) := by
    apply ExecBlock.consNormal
    · apply ExecStmt.letDecl
      change evalExpr? ballotConfig (winningProposalFrame locals) evm (.intLit 0) =
        .ok (.int (Int.ofNat (0 : Nat)))
      simp [evalExpr?, pure, winningProposalFrame]
    · exact ExecBlock.nil
  have hp0 : L0.get? "p" = some (.int (Int.ofNat (0 : Nat))) := by
    simp [L0]
  have hcount0 : L0.get? "winningVoteCount" = some (.int (Int.ofNat (0 : Nat))) := by
    simpa [L0, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using hcount
  have hbest0 : L0.get? "winningProposal_" = some (.int (Int.ofNat (0 : Nat))) := by
    simpa [L0, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using hbest
  have hprops0 : L0.get? "proposals" = none := by
    simpa [L0, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using hbase
  have hP0 : P (winningProposalLengthCurrent evm).toNat L0 := by
    exact ⟨⟨0⟩, ⟨0⟩, ⟨0⟩, by simpa using hp0, by simpa using hcount0,
      by simpa using hbest0, hprops0, by simp, by simp, by rfl⟩
  obtain ⟨locals', hloop, hPfinal⟩ :=
    execFor_var P hfalse htrue hstep (winningProposalLengthCurrent evm).toNat L0 hP0
  refine ⟨locals', ?_, hPfinal⟩
  rw [winningProposalForStmt]
  exact ExecStmt.for hinit hloop

theorem ballotWinningProposalBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? "proposals" = none) :
    ∃ locals', ExecTransitionBody ballotConfig ballotContract evm locals winningProposalTransition.body
      (.returned { contract := ballotContract, locals := locals' } evm
        (some [(.int (Int.ofNat (winningProposalResultCurrent evm).toNat))])) := by
  let Lwp := locals.insert "winningProposal_" (.int (Int.ofNat (0 : Nat)))
  let Lcount := Lwp.insert "winningVoteCount" (.int (Int.ofNat (0 : Nat)))
  have hwpEval :
      evalExpr? ballotConfig (winningProposalFrame locals) evm (.intLit 0) =
        .ok (.int (Int.ofNat (0 : Nat))) := by
    simp [evalExpr?, pure, winningProposalFrame]
  have hcountEval :
      evalExpr? ballotConfig (winningProposalFrame Lwp) evm (.intLit 0) =
        .ok (.int (Int.ofNat (0 : Nat))) := by
    simp [evalExpr?, pure, winningProposalFrame]
  have hpropsCount : Lcount.get? "proposals" = none := by
    simpa [Lcount, Lwp, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using hbase
  have hcountCount : Lcount.get? "winningVoteCount" = some (.int (Int.ofNat (0 : Nat))) := by
    simp [Lcount]
  have hbestCount : Lcount.get? "winningProposal_" = some (.int (Int.ofNat (0 : Nat))) := by
    have hlast : Lcount.get? "winningProposal_" = Lwp.get? "winningProposal_" := by
      simpa [Lcount] using
        (store_get_ne Lwp (.int (Int.ofNat (0 : Nat)))
          (by native_decide : ("winningVoteCount" == "winningProposal_") = false))
    rw [hlast]
    simp [Lwp]
  obtain ⟨locals', hfor, hPfinal⟩ :=
    winningProposalForLoopReturns evm Lcount hpropsCount hcountCount hbestCount
  rcases hPfinal with ⟨p, count, best, hp, hcount, hbest, hprops, hvar, hle, hloop⟩
  have hbestResult : best = winningProposalResultCurrent evm := by
    simpa [winningProposalLoopAux, winningProposalResultCurrent] using congrArg Prod.snd hloop
  have hretEval :
      evalExpr? ballotConfig (winningProposalFrame locals') evm (.var "winningProposal_") =
        .ok (.int (Int.ofNat (winningProposalResultCurrent evm).toNat)) := by
    simpa [winningProposalFrame, hbestResult] using
      (winningProposalEvalVar evm locals' "winningProposal_" best hbest)
  refine ⟨locals', ExecFuncBody.execBlockRet ?_⟩
  exact ((((ABlock.start.requireStep (evalCallvalueEq_true h)).letStep hwpEval).letStep
    hcountEval).forStep hfor).returns hretEval

theorem winningProposalLengthWord_eq_current_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    winningProposalLengthWord σ I =
      winningProposalLengthCurrent (initState cA gh bl σ σ₀ g A I) := rfl

theorem winningProposalVoteCountWord_eq_current_init {cA gh bl σ σ₀ A I} {g : Sat256}
    (p : UInt256) :
    winningProposalVoteCountWord σ I p =
      winningProposalVoteCountCurrent (initState cA gh bl σ σ₀ g A I) p := rfl

theorem winningProposalLoopAux_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    ∀ fuel p winningVoteCount winningProposal,
      winningProposalLoopAux (initState cA gh bl σ σ₀ g A I) fuel p winningVoteCount
        winningProposal =
      winningProposalLoopAuxWord σ I fuel p winningVoteCount winningProposal := by
  intro fuel
  induction fuel with
  | zero => intro p winningVoteCount winningProposal; rfl
  | succ fuel ih =>
      intro p winningVoteCount winningProposal
      simp only [winningProposalLoopAux, winningProposalLoopAuxWord]
      rw [← winningProposalVoteCountWord_eq_current_init]
      split <;> rw [ih]

theorem winningProposalResultCurrent_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    winningProposalResultCurrent (initState cA gh bl σ σ₀ g A I) =
      winningProposalResultWord σ I := by
  unfold winningProposalResultCurrent winningProposalResultWord
  rw [← winningProposalLengthWord_eq_current_init]
  rw [winningProposalLoopAux_init]

theorem winningProposalLengthWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    winningProposalLengthWord σ I = winningProposalLengthWord τ I := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner ⟨2⟩ ⟨0⟩

theorem winningProposalVoteCountWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) (p : UInt256) :
    winningProposalVoteCountWord σ I p = winningProposalVoteCountWord τ I p := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner (winningProposalVoteCountSlot p) ⟨0⟩

theorem winningProposalLoopAuxWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    ∀ fuel p winningVoteCount winningProposal,
      winningProposalLoopAuxWord σ I fuel p winningVoteCount winningProposal =
        winningProposalLoopAuxWord τ I fuel p winningVoteCount winningProposal := by
  intro fuel
  induction fuel with
  | zero =>
      intro p winningVoteCount winningProposal
      rfl
  | succ fuel ih =>
      intro p winningVoteCount winningProposal
      simp only [winningProposalLoopAuxWord]
      rw [winningProposalVoteCountWord_accountMapEquiv hστ p]
      exact ih _ _ _

theorem winningProposalResultWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    winningProposalResultWord σ I = winningProposalResultWord τ I := by
  unfold winningProposalResultWord
  rw [winningProposalLengthWord_accountMapEquiv hστ]
  exact congrArg Prod.snd
    (winningProposalLoopAuxWord_accountMapEquiv hστ _ ⟨0⟩ ⟨0⟩ ⟨0⟩)

theorem ballotWinningProposalSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0x60, 0x9f, 0xf1, 0xbd]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x60, 0x9f, 0xf1, 0xbd]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem ballotDispatch_winningProposal {cd : ByteArray}
    (hsel : ((⟨#[0x60, 0x9f, 0xf1, 0xbd]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg ballotContract cd = some winningProposalTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x60, 0x9f, 0xf1, 0xbd]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [voteTransition, proposalsGetter, chairpersonGetter, delegateTransition])
    (post := [giveRightToVoteTransition, votersGetter, winnerNameTransition])
    rfl rfl ?_ (by rw [selectorOf, ballotWinningProposalSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · rw [selectorOf, ballotVoteSelectorBytes, hcd]; decide
  · rw [selectorOf, ballotProposalsSelectorBytes, hcd]; decide
  · rw [selectorOf, ballotChairpersonSelectorBytes, hcd]; decide
  · rw [selectorOf, ballotDelegateSelectorBytes, hcd]; decide

theorem ballotDecode_winningProposal {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (winningProposalTransition.params.map Param.name)
      (transitionSignature winningProposalTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-! ### EVM memory used by `winningProposal` -/

noncomputable def winningProposalBaseSlotMem : ByteArray :=
  (UInt256.toByteArray (⟨2⟩ : UInt256)).write 0 solcFreePtrMem 0 32

noncomputable def winningProposalReturnMem (val : UInt256) : ByteArray :=
  (UInt256.toByteArray val).write 0 winningProposalBaseSlotMem 128 32

noncomputable def winningProposalStoreBaseMem (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨2⟩ : UInt256)).write 0 mem 0 32

noncomputable def winningProposalReturnFromMem (mem : ByteArray) (val : UInt256) : ByteArray :=
  (UInt256.toByteArray val).write 0 mem 128 32

theorem winningProposalBaseSlotMem_size : winningProposalBaseSlotMem.size = 96 := by
  unfold winningProposalBaseSlotMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
  omega

theorem winningProposalBaseSlotMem_read0 :
    winningProposalBaseSlotMem.readWithPadding 0 32 =
      UInt256.toByteArray (⟨2⟩ : UInt256) := by
  unfold winningProposalBaseSlotMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by rw [solcFreePtrMem_size]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray (⟨2⟩ : UInt256)).size ≤ 32
    rw [toByteArray_size])

theorem winningProposalBaseSlotMem_read64 :
    winningProposalBaseSlotMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold winningProposalBaseSlotMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; omega) (by omega)
      (by rw [solcFreePtrMem_size]),
    solcFreePtrMem_read64]

theorem winningProposalBaseSlotMem_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ winningProposalBaseSlotMem.size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        (winningProposalBaseSlotMem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [winningProposalBaseSlotMem_size]; decide) (by decide)
    winningProposalBaseSlotMem_read64

theorem winningProposalDataBaseKeccak :
    UInt256.ofNat
        (fromByteArrayBigEndian (ffi.KEC (winningProposalBaseSlotMem.readWithPadding 0 32))) =
      proposalsDataBase := by
  rw [winningProposalBaseSlotMem_read0]
  unfold proposalsDataBase
  exact keccakSlot_eq _

theorem winningProposalReturnMem_size (val : UInt256) :
    (winningProposalReturnMem val).size = 160 := by
  unfold winningProposalReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [winningProposalBaseSlotMem_size]; omega)
      (by rw [winningProposalBaseSlotMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, winningProposalBaseSlotMem_size,
    ByteArray_zeroes_size,
    show 128 - 96 = 32 from by norm_num,
    toByteArray_size]

theorem winningProposalReturnMem_read64 (val : UInt256) :
    (winningProposalReturnMem val).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold winningProposalReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [winningProposalBaseSlotMem_size]; omega)
      (by rw [winningProposalBaseSlotMem_size]; exact lt_usize _ (by norm_num))]
  rw [ByteArray.append_assoc]
  rw [readWithPadding_eq_extract' _ 64 32 (by norm_num) (by norm_num) (by
    rw [ByteArray.size_append, winningProposalBaseSlotMem_size, ByteArray.size_append,
      ByteArray_zeroes_size,
      show 128 - 96 = 32 from by norm_num,
      toByteArray_size]
    omega)]
  rw [extract_append_left winningProposalBaseSlotMem
      (ffi.ByteArray.zeroes (128 - winningProposalBaseSlotMem.size) ++
        UInt256.toByteArray val)
      64 96 (by rw [winningProposalBaseSlotMem_size])]
  rw [← readWithPadding_eq_extract' winningProposalBaseSlotMem 64 32
      (by norm_num) (by norm_num) (by rw [winningProposalBaseSlotMem_size])]
  exact winningProposalBaseSlotMem_read64

theorem winningProposalReturnMem_mload64 (val : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (winningProposalReturnMem val).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((winningProposalReturnMem val).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [winningProposalReturnMem_size]; decide) (by decide)
    (winningProposalReturnMem_read64 val)

theorem winningProposalReturnMem_read128 (val : UInt256) :
    (winningProposalReturnMem val).readWithPadding 128 32 = UInt256.toByteArray val := by
  rw [readWithPadding_eq_extract' _ 128 32 (by norm_num) (by norm_num)
      (by rw [winningProposalReturnMem_size])]
  unfold winningProposalReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [winningProposalBaseSlotMem_size]; omega)
      (by rw [winningProposalBaseSlotMem_size]; exact lt_usize _ (by norm_num))]
  rw [extract_append_right_window
      (winningProposalBaseSlotMem ++
        ffi.ByteArray.zeroes (128 - winningProposalBaseSlotMem.size))
      (UInt256.toByteArray val) 128 160 (by
        rw [ByteArray.size_append, winningProposalBaseSlotMem_size, ByteArray_zeroes_size,
          show 128 - 96 = 32 from by norm_num])]
  rw [ByteArray.size_append, winningProposalBaseSlotMem_size, ByteArray_zeroes_size,
    show 128 - 96 = 32 from by norm_num]
  norm_num
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray val).size ≤ 32
    rw [toByteArray_size])

theorem winningProposalStoreBaseMem_size (mem : ByteArray) (hsize : mem.size = 96) :
    (winningProposalStoreBaseMem mem).size = 96 := by
  unfold winningProposalStoreBaseMem
  rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by rw [hsize]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size, hsize]
  omega

theorem winningProposalStoreBaseMem_read0 (mem : ByteArray) (hsize : mem.size = 96) :
    (winningProposalStoreBaseMem mem).readWithPadding 0 32 =
      UInt256.toByteArray (⟨2⟩ : UInt256) := by
  unfold winningProposalStoreBaseMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [hsize]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray (⟨2⟩ : UInt256)).size ≤ 32
    rw [toByteArray_size])

theorem winningProposalStoreBaseMem_read64 (mem : ByteArray)
    (hsize : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (winningProposalStoreBaseMem mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold winningProposalStoreBaseMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by rw [hsize]; omega)
    (by omega) (by rw [hsize]), hread64]

theorem winningProposalStoreBaseMem_keccak (mem : ByteArray) (hsize : mem.size = 96) :
    UInt256.ofNat
        (fromByteArrayBigEndian (ffi.KEC ((winningProposalStoreBaseMem mem).readWithPadding 0 32))) =
      proposalsDataBase := by
  rw [winningProposalStoreBaseMem_read0 mem hsize]
  unfold proposalsDataBase
  exact keccakSlot_eq _

theorem winningProposalReturnFromMem_size (mem : ByteArray) (val : UInt256)
    (hsize : mem.size = 96) :
    (winningProposalReturnFromMem mem val).size = 160 := by
  unfold winningProposalReturnFromMem
  rw [toByteArray_write_eq _ _ _ (by rw [hsize]; omega)
      (by rw [hsize]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
    show 128 - mem.size = 32 from by rw [hsize],
    toByteArray_size, hsize]

theorem winningProposalReturnFromMem_read64 (mem : ByteArray) (val : UInt256)
    (hsize : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (winningProposalReturnFromMem mem val).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold winningProposalReturnFromMem
  rw [toByteArray_write_eq _ _ _ (by rw [hsize]; omega)
      (by rw [hsize]; exact lt_usize _ (by norm_num))]
  rw [ByteArray.append_assoc]
  rw [readWithPadding_eq_extract' _ 64 32 (by norm_num) (by norm_num) (by
    rw [ByteArray.size_append, hsize, ByteArray.size_append, ByteArray_zeroes_size,
      show 128 - 96 = 32 from by norm_num,
      toByteArray_size]
    omega)]
  rw [extract_append_left mem
      (ffi.ByteArray.zeroes (128 - mem.size) ++ UInt256.toByteArray val)
      64 96 (by rw [hsize])]
  rw [← readWithPadding_eq_extract' mem 64 32 (by norm_num) (by norm_num) (by rw [hsize])]
  exact hread64

theorem winningProposalReturnFromMem_mload64 (mem : ByteArray) (val : UInt256)
    (hsize : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (winningProposalReturnFromMem mem val).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((winningProposalReturnFromMem mem val).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [winningProposalReturnFromMem_size mem val hsize]; decide)
    (by decide)
    (winningProposalReturnFromMem_read64 mem val hsize hread64)

theorem winningProposalReturnFromMem_read128 (mem : ByteArray) (val : UInt256)
    (hsize : mem.size = 96) :
    (winningProposalReturnFromMem mem val).readWithPadding 128 32 =
      UInt256.toByteArray val := by
  rw [readWithPadding_eq_extract' _ 128 32 (by norm_num) (by norm_num)
      (by rw [winningProposalReturnFromMem_size mem val hsize])]
  unfold winningProposalReturnFromMem
  rw [toByteArray_write_eq _ _ _ (by rw [hsize]; omega)
      (by rw [hsize]; exact lt_usize _ (by norm_num))]
  rw [extract_append_right_window
      (mem ++ ffi.ByteArray.zeroes (128 - mem.size))
      (UInt256.toByteArray val) 128 160 (by
        rw [ByteArray.size_append, hsize, ByteArray_zeroes_size,
          show 128 - 96 = 32 from by norm_num])]
  rw [ByteArray.size_append, hsize, ByteArray_zeroes_size,
    show 128 - 96 = 32 from by norm_num]
  norm_num
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray val).size ≤ 32
    rw [toByteArray_size])

/-! ### EVM loop/routine for `winningProposal` -/

private structure WinningProposalLoopState where
  p : UInt256
  winningVoteCount : UInt256
  winningProposal : UInt256
  mem : ByteArray

theorem winningProposalVoteCountSlot_evm (p : UInt256) :
    (⟨1⟩ : UInt256) + (UInt256.mul ⟨2⟩ p + proposalsDataBase) =
      winningProposalVoteCountSlot p := by
  unfold winningProposalVoteCountSlot
  exact u256_add_comm _ _

theorem ballotWinningProposalLoop {cA σ I} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    (hret : (D_J ballotBytecode 0).contains ret = true)
    (hov : R.length + 20 ≤ 1024) :
    ∀ (var : ℕ) (p winningVoteCount winningProposal : UInt256)
      (target : UInt256 × UInt256) (mem : ByteArray) (k C : ℕ),
      (winningProposalLengthWord σ I).toNat - p.toNat = var →
      p.toNat ≤ (winningProposalLengthWord σ I).toNat →
      winningProposalLoopAuxWord σ I var p winningVoteCount winningProposal = target →
      mem.size = 96 →
      mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ →
      RD ballotBytecode I g s0 ⟨1319⟩
        (p :: winningVoteCount :: winningProposal :: ret :: R)
        mem (UInt256.ofNat 3) rdata (cA, σ) k C →
      ∃ mem' k' C',
        mem'.size = 96 ∧
        mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
        RD ballotBytecode I g s0 ret (target.2 :: R)
          mem' (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  intro var p winningVoteCount winningProposal target mem k C hvar hle hloop hmem hread64 h
  let Inv : ℕ → WinningProposalLoopState → Prop := fun v a =>
    (winningProposalLengthWord σ I).toNat - a.p.toNat = v ∧
      a.p.toNat ≤ (winningProposalLengthWord σ I).toNat ∧
      winningProposalLoopAuxWord σ I v a.p a.winningVoteCount a.winningProposal = target ∧
      a.mem.size = 96 ∧
      a.mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩
  let stk : WinningProposalLoopState → List UInt256 := fun a =>
    a.p :: a.winningVoteCount :: a.winningProposal :: ret :: R
  let stateMem : WinningProposalLoopState → ByteArray := fun a => a.mem
  let stateAw : WinningProposalLoopState → UInt256 := fun _ => UInt256.ofNat 3
  let exitStk : WinningProposalLoopState → List UInt256 := fun _ => target.2 :: R
  have hexit : ∀ a, Inv 0 a → ∀ k C,
      RD ballotBytecode I g s0 ⟨1319⟩ (stk a) (stateMem a) (stateAw a) rdata (cA, σ) k C →
      ∃ k' C',
        RD ballotBytecode I g s0 ret (exitStk a) (stateMem a) (stateAw a) rdata
          (cA, σ) k' C' := by
    intro a hInv k C h
    dsimp [Inv] at hInv
    rcases hInv with ⟨hvar, _hle, hloop, _hmem, _hread64⟩
    dsimp [stk, stateMem, stateAw] at h
    have hnotlt : (winningProposalLengthWord σ I).toNat ≤ a.p.toNat := by omega
    have hlt : UInt256.lt a.p (winningProposalLengthWord σ I) = ⟨0⟩ :=
      ult_zero hnotlt
    have hbestTarget : a.winningProposal = target.2 := by
      simpa [winningProposalLoopAuxWord] using congrArg Prod.snd hloop
    have rd1322 := evm_run h with [jumpdest, push1 ⟨2⟩]
    obtain ⟨_, _, rd1323⟩ := rd1322.sload (by decide) (by evm_ov)
    have rdret := evm_run rd1323 with [
      dup2, lt, iszero, push2 ⟨1420⟩,
      jumpiT (by
        have hlt' :
            UInt256.lt a.p
              (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
                = ⟨0⟩ := by
          simpa [winningProposalLengthWord] using hlt
        rw [hlt']; decide) (by jump_dest),
      jumpdest, pop, pop, swap1, jump hret]
    exact ⟨_, _, by simpa [exitStk, stateMem, stateAw, hbestTarget] using rdret⟩
  have hbody : ∀ v a, Inv (v + 1) a → ∀ k C,
      RD ballotBytecode I g s0 ⟨1319⟩ (stk a) (stateMem a) (stateAw a) rdata (cA, σ) k C →
      ∃ a' k' C',
        Inv v a' ∧
          RD ballotBytecode I g s0 ⟨1319⟩ (stk a') (stateMem a') (stateAw a') rdata
            (cA, σ) k' C' := by
    intro v a hInv k C h
    dsimp [Inv] at hInv
    rcases hInv with ⟨hvar, hle, hloop, hmem, hread64⟩
    dsimp [stk, stateMem, stateAw] at h
    have hbound : a.p.toNat < (winningProposalLengthWord σ I).toNat := by omega
    have hlt : UInt256.lt a.p (winningProposalLengthWord σ I) = ⟨1⟩ :=
      ult_one hbound
    have hp1size : a.p.toNat + 1 < UInt256.size := by
      have hlen : (winningProposalLengthWord σ I).toNat < UInt256.size :=
        (winningProposalLengthWord σ I).val.isLt
      omega
    have hp1 : (a.p + ⟨1⟩).toNat = a.p.toNat + 1 := add1_toNat hp1size
    let voteCount := winningProposalVoteCountWord σ I a.p
    let mem1 := winningProposalStoreBaseMem a.mem
    have hmem1 : mem1.size = 96 := by
      simpa [mem1] using winningProposalStoreBaseMem_size a.mem hmem
    have hread1 : mem1.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
      simpa [mem1] using winningProposalStoreBaseMem_read64 a.mem hmem hread64
    have rd1322 := evm_run h with [jumpdest, push1 ⟨2⟩]
    obtain ⟨_, _, rd1323⟩ := rd1322.sload (by decide) (by evm_ov)
    have rd1336_prefix := evm_run rd1323 with [
      dup2, lt, iszero, push2 ⟨1420⟩,
      jumpiNT (by
        have hlt' :
            UInt256.lt a.p
              (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
                = ⟨1⟩ := by
          simpa [winningProposalLengthWord] using hlt
        rw [hlt']; decide),
      dup2, push1 ⟨2⟩, dup3, dup2]
    obtain ⟨_, _, rd1336⟩ := rd1336_prefix.sload (by decide) (by evm_ov)
    have rdVoteSlot := evm_run rd1336 with [
      dup2, lt, push2 ⟨1349⟩,
      jumpiT (by
        have hlt' :
            UInt256.lt a.p
              (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
                = ⟨1⟩ := by
          simpa [winningProposalLengthWord] using hlt
        rw [hlt']; decide) (by jump_dest),
      jumpdest, swap1, push0,
      raw mstore 0 mem1 (UInt256.ofNat 3) (by decide) mem_cost
        (by rfl) (by decide) (by evm_ov),
      push1 ⟨32⟩, push0,
      raw keccak256 0 proposalsDataBase (UInt256.ofNat 3) (by decide)
        mem_cost (winningProposalStoreBaseMem_keccak a.mem hmem) (by decide) (by evm_ov),
      swap1, push1 ⟨2⟩, mul, add, push1 ⟨1⟩, add]
    obtain ⟨_, _, rdVote⟩ := rdVoteSlot.sload (by decide) (by evm_ov)
    by_cases hgt : a.winningVoteCount.toNat < voteCount.toNat
    · let mem2 := winningProposalStoreBaseMem mem1
      have hmem2 : mem2.size = 96 := by
        simpa [mem2] using winningProposalStoreBaseMem_size mem1 hmem1
      have hread2 : mem2.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
        simpa [mem2] using winningProposalStoreBaseMem_read64 mem1 hmem1 hread1
      have hgtWord : UInt256.gt voteCount a.winningVoteCount = ⟨1⟩ := ugt_one hgt
      have rd1390_prefix := evm_run rdVote with [
        gt, iszero, push2 ⟨1412⟩,
        jumpiNT (by
          have hgtWord' :
              UInt256.gt
                (σ.find? I.codeOwner |>.option ⟨0⟩
                  (fun acc => acc.storage.findD
                    ((⟨1⟩ : UInt256) + (UInt256.mul ⟨2⟩ a.p + proposalsDataBase)) ⟨0⟩))
                a.winningVoteCount = ⟨1⟩ := by
              simpa [voteCount, winningProposalVoteCountWord,
                winningProposalVoteCountSlot_evm] using hgtWord
          rw [hgtWord']; decide),
        push1 ⟨2⟩, dup2, dup2]
      obtain ⟨_, _, rd1376⟩ := rd1390_prefix.sload (by decide) (by evm_ov)
      have rd1412 := evm_run rd1376 with [
        dup2, lt, push2 ⟨1390⟩,
        jumpiT (by
          have hlt' :
              UInt256.lt a.p
                (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
                  = ⟨1⟩ := by
            simpa [winningProposalLengthWord] using hlt
          rw [hlt']; decide) (by jump_dest),
        jumpdest, swap1, push0,
        raw mstore 0 mem2 (UInt256.ofNat 3) (by decide) mem_cost
          (by rfl) (by decide) (by evm_ov),
        push1 ⟨32⟩, push0,
        raw keccak256 0 proposalsDataBase (UInt256.ofNat 3) (by decide)
          mem_cost (winningProposalStoreBaseMem_keccak mem1 hmem1) (by decide) (by evm_ov),
        swap1, push1 ⟨2⟩, mul, add, push1 ⟨1⟩, add]
      obtain ⟨_, _, rd1407⟩ := rd1412.sload (by decide) (by evm_ov)
      have rdNext := evm_run rd1407 with [
        swap2, pop, dup1, swap3, pop,
        jumpdest, push1 ⟨1⟩, add, push2 ⟨1319⟩, jump (by jump_dest)]
      have hvarNext :
          (winningProposalLengthWord σ I).toNat - (a.p + ⟨1⟩).toNat = v := by
        rw [hp1]
        omega
      have hleNext : (a.p + ⟨1⟩).toNat ≤ (winningProposalLengthWord σ I).toNat := by
        rw [hp1]
        omega
      have hloopNext :
          winningProposalLoopAuxWord σ I v (a.p + ⟨1⟩) voteCount a.p = target := by
        simpa [winningProposalLoopAuxWord, voteCount, hgt] using hloop
      let a' : WinningProposalLoopState :=
        { p := a.p + ⟨1⟩, winningVoteCount := voteCount, winningProposal := a.p, mem := mem2 }
      have hrdNext :
          ∃ k' C',
            RD ballotBytecode I g s0 ⟨1319⟩ (stk a') (stateMem a') (stateAw a') rdata
              (cA, σ) k' C' := by
        exact ⟨_, _, by
          simpa [stk, stateMem, stateAw, a', voteCount, winningProposalVoteCountWord,
            winningProposalVoteCountSlot, u256_add_comm] using rdNext⟩
      rcases hrdNext with ⟨kNext, CNext, rdNext'⟩
      refine ⟨a', kNext, CNext, ?_, rdNext'⟩
      · dsimp [Inv, a']
        exact ⟨hvarNext, hleNext, hloopNext, hmem2, hread2⟩
    · have hgtWord : UInt256.gt voteCount a.winningVoteCount = ⟨0⟩ :=
        ugt_zero (by omega)
      have rdNext := evm_run rdVote with [
        gt, iszero, push2 ⟨1412⟩,
        jumpiT (by
          have hgtWord' :
              UInt256.gt
                (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD
                ((⟨1⟩ : UInt256) + (UInt256.mul ⟨2⟩ a.p + proposalsDataBase)) ⟨0⟩))
                a.winningVoteCount = ⟨0⟩ := by
              simpa [voteCount, winningProposalVoteCountWord,
                winningProposalVoteCountSlot_evm] using hgtWord
          rw [hgtWord']; decide) (by jump_dest),
        jumpdest, push1 ⟨1⟩, add, push2 ⟨1319⟩, jump (by jump_dest)]
      have hvarNext :
          (winningProposalLengthWord σ I).toNat - (a.p + ⟨1⟩).toNat = v := by
        rw [hp1]
        omega
      have hleNext : (a.p + ⟨1⟩).toNat ≤ (winningProposalLengthWord σ I).toNat := by
        rw [hp1]
        omega
      have hloopNext :
          winningProposalLoopAuxWord σ I v (a.p + ⟨1⟩) a.winningVoteCount a.winningProposal =
            target := by
        simpa [winningProposalLoopAuxWord, voteCount, hgt] using hloop
      let a' : WinningProposalLoopState :=
        { p := a.p + ⟨1⟩, winningVoteCount := a.winningVoteCount,
          winningProposal := a.winningProposal, mem := mem1 }
      have hrdNext :
          ∃ k' C',
            RD ballotBytecode I g s0 ⟨1319⟩ (stk a') (stateMem a') (stateAw a') rdata
              (cA, σ) k' C' := by
        exact ⟨_, _, by simpa [stk, stateMem, stateAw, a', u256_add_comm] using rdNext⟩
      rcases hrdNext with ⟨kNext, CNext, rdNext'⟩
      refine ⟨a', kNext, CNext, ?_, rdNext'⟩
      · dsimp [Inv, a']
        exact ⟨hvarNext, hleNext, hloopNext, hmem1, hread1⟩
  let a0 : WinningProposalLoopState :=
    { p := p, winningVoteCount := winningVoteCount, winningProposal := winningProposal, mem := mem }
  have hInv0 : Inv var a0 := by
    dsimp [Inv, a0]
    exact ⟨hvar, hle, hloop, hmem, hread64⟩
  obtain ⟨a', k', C', hInvFinal, hrdFinal⟩ :=
    RD.whileLoopCarry (code := ballotBytecode) (ee := I) (g := g) (s0 := s0)
      (rdata := rdata) (acc := (cA, σ)) (α := WinningProposalLoopState)
      ⟨1319⟩ ret Inv stk stateMem stateAw exitStk hexit hbody
      var a0 hInv0 k C (by simpa [stk, stateMem, stateAw, a0] using h)
  dsimp [Inv] at hInvFinal
  rcases hInvFinal with ⟨_hvarFinal, _hleFinal, _hloopFinal, hmemFinal, hreadFinal⟩
  exact ⟨a'.mem, k', C', hmemFinal, hreadFinal,
    by simpa [exitStk, stateMem, stateAw] using hrdFinal⟩

theorem ballotWinningProposalRoutine {cA σ I} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256} {mem : ByteArray} {rdata : ByteArray} {k C : ℕ}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hret : (D_J ballotBytecode 0).contains ret = true)
    (hov : R.length + 23 ≤ 1024)
    (h : RD ballotBytecode I g s0 ⟨1315⟩ (ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    ∃ mem' k' C',
      mem'.size = 96 ∧
      mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      RD ballotBytecode I g s0 ret (winningProposalResultWord σ I :: R)
        mem' (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  let target :=
    winningProposalLoopAuxWord σ I (winningProposalLengthWord σ I).toNat ⟨0⟩ ⟨0⟩ ⟨0⟩
  have rd1319 := evm_run h with [jumpdest, push0, dup1, dup1]
  obtain ⟨mem', k', C', hmem', hread', rdret⟩ :=
    ballotWinningProposalLoop (cA := cA) (σ := σ) (I := I) (g := g) (s0 := s0)
      (ret := ret) (R := R) (rdata := rdata)
      hret (by omega : R.length + 20 ≤ 1024)
      (winningProposalLengthWord σ I).toNat ⟨0⟩ ⟨0⟩ ⟨0⟩ target mem _ _
      (by simp) (by simp) (by rfl) hmem hread64 rd1319
  refine ⟨mem', k', C', hmem', hread', ?_⟩
  simpa [target, winningProposalResultWord] using rdret

theorem ballotX_winningProposal_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨264⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret ballotBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (winningProposalResultWord σ I)) := by
  obtain ⟨_, _, rd264⟩ := hreach
  have rd1315 := evm_run rd264 with [
    jumpdest, push2 ⟨272⟩, push2 ⟨1315⟩, jump (by jump_dest)]
  obtain ⟨mem', _, _, hmem', hread64', rd272⟩ :=
    ballotWinningProposalRoutine (cA := cA) (σ := σ) (I := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) (ret := ⟨272⟩) (R := [sel])
      (mem := solcFreePtrMem) (rdata := ByteArray.empty)
      solcFreePtrMem_size solcFreePtrMem_read64 (by jump_dest)
      (by simp only [List.length_cons, List.length_nil]; omega) rd1315
  let retMem := winningProposalReturnFromMem mem' (winningProposalResultWord σ I)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ retMem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (retMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    simpa [retMem] using
      winningProposalReturnFromMem_mload64 mem' (winningProposalResultWord σ I)
        hmem' hread64'
  have hread128 :
      retMem.readWithPadding 128 32 =
        UInt256.toByteArray (winningProposalResultWord σ I) := by
    simpa [retMem] using
      winningProposalReturnFromMem_read128 mem' (winningProposalResultWord σ I) hmem'
  have rd194 := evm_run rd272 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmem']; decide) (by decide) hread64')
      (by decide) (by evm_ov),
    swap1, dup2,
    raw mstore 6 retMem (UInt256.ofNat 5) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨194⟩, jump (by jump_dest)]
  exact RD.ballotReturnOneWord194OfMem rd194 hmload64 hread128
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem ballotWinningProposalBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = ballotBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x60, 0x9f, 0xf1, 0xbd]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨264⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := ballotWinningProposalSelector_size hsel
  have hd := ballotDispatch_winningProposal (cd := I.calldata) hsel
  have hdec := ballotDecode_winningProposal (I := I) hsz4
  obtain ⟨locals', hbody⟩ := ballotWinningProposalBodyReturns
    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
    (by simp only [initState]; exact hwv) (by simp)
  have hresult :
      winningProposalResultCurrent
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) =
        winningProposalResultWord σ_evm I := by
    rw [winningProposalResultCurrent_init]
    exact (winningProposalResultWord_accountMapEquiv hAccounts).symm
  exact (ballotX_winningProposal_ok (g := Sat256.ofUInt256 g) hreach)
    |>.reEquivExecutionTransport hcode hd hdec hbody (by simp [hresult])
      hAccounts
      (returnEquiv_of_encode (uint256ReturnEncoding (winningProposalResultWord σ_evm I)))

end Ballot
