import Benchmarks.Safe.ModuleStorage
import Benchmarks.Safe.LocalArrays
import Benchmarks.Safe.LinkedPages

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def modulesCountCondition : Expr :=
  andE (andE (neE (.var "next") zeroAddr) (neE (.var "next") sentinelAddr))
    (ltE (.var "moduleCount") (.var "pageSize"))

def modulesCountBody : List Stmt :=
  [ .assign .localVar (varRef "last") (.var "next"),
    .assign .localVar (varRef "next") (.storage (modulesRef (.var "next"))),
    .assign .localVar (varRef "moduleCount") (inc256 (.var "moduleCount")) ]

def modulesCountLoop : Stmt := .while modulesCountCondition modulesCountBody

structure ModulesCountLocals (locals : Store) (start pageSize : UInt256)
    (index : Nat) (current last : UInt256) : Prop where
  start : locals["start"]? = some (.address (AccountAddress.ofNat start.toNat))
  pageSize : locals["pageSize"]? = some (.int (Int.ofNat pageSize.toNat))
  count : locals["moduleCount"]? = some (.int (Int.ofNat index))
  next : locals["next"]? = some (.address (AccountAddress.ofNat current.toNat))
  last : locals["last"]? = some (.address (AccountAddress.ofNat last.toNat))
  modules : locals["modules"]? = none

theorem safeModulesCountCondition (evm : EVM.State) {locals start pageSize index current last}
    (hl : ModulesCountLocals locals start pageSize index current last)
    (hc : current.toNat < EVM.addressModulus) :
    evalExpr? config { contract := contract, locals := locals } evm modulesCountCondition =
      .ok (.bool (decide (current ≠ ⟨0⟩ ∧ current ≠ ⟨1⟩ ∧ index < pageSize.toNat))) := by
  have he := evalLocalValue (cfg := config) (evm := evm)
    (frame := { contract := contract, locals := locals }) hl.next
  have haddr := evalAddressMembership hc hc he he
  have hlt : evalExpr? config { contract := contract, locals := locals } evm
      (ltE (.var "moduleCount") (.var "pageSize")) =
      .ok (.bool (decide (index < pageSize.toNat))) := by
    rw [ltE, evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue hl.count,
      evalLocalValue hl.pageSize]
    simp [EvalResult.bind, bind, pure, evalBinaryOp_lt_int_ok]
  simpa [modulesCountCondition, andE, addressMembership, Bool.and_assoc, and_assoc] using
    evalBoolAnd haddr hlt

def modulesCountNextLocals (evm : EVM.State) (locals : Store) (index : Nat)
    (current : UInt256) : Store :=
  ((locals.insert "last" (.address (AccountAddress.ofNat current.toNat))).insert
    "next" (.address (AccountAddress.ofNat (moduleLink evm current).toNat))).insert
      "moduleCount" (.int (Int.ofNat (index + 1)))

theorem safeModulesCountNextLocals (evm : EVM.State) {locals start pageSize index current last}
    (hl : ModulesCountLocals locals start pageSize index current last) :
    ModulesCountLocals (modulesCountNextLocals evm locals index current) start pageSize
      (index + 1) (moduleLink evm current) current := by
  constructor
  · simpa [modulesCountNextLocals, Std.HashMap.getElem?_insert] using hl.start
  · simpa [modulesCountNextLocals, Std.HashMap.getElem?_insert] using hl.pageSize
  · simp [modulesCountNextLocals, Std.HashMap.getElem_insert]
  · simp [modulesCountNextLocals, Std.HashMap.getElem_insert]
  · simp [modulesCountNextLocals, Std.HashMap.getElem_insert]
  · simpa [modulesCountNextLocals, Std.HashMap.getElem?_insert] using hl.modules

theorem safeModulesCountStep (evm : EVM.State) {locals start pageSize index current last}
    (hl : ModulesCountLocals locals start pageSize index current last)
    (hc : current.toNat < EVM.addressModulus) (hfit : index + 1 < UInt256.size) :
    ExecBlock config { contract := contract, locals := locals } evm modulesCountBody
      (.ok { contract := contract, locals := modulesCountNextLocals evm locals index current }
        evm) := by
  let ls₁ := locals.insert "last" (.address (AccountAddress.ofNat current.toNat))
  let ls₂ := ls₁.insert "next" (.address (AccountAddress.ofNat (moduleLink evm current).toNat))
  have hnext₁ : ls₁["next"]? = some (.address (AccountAddress.ofNat current.toNat)) := by
    simpa [ls₁, Std.HashMap.getElem?_insert] using hl.next
  have hcount₂ : ls₂["moduleCount"]? = some (.int (Int.ofNat index)) := by
    simpa [ls₂, ls₁, Std.HashMap.getElem?_insert] using hl.count
  have hn := safeEvalModuleLink evm ls₁ (.var "next") current
    (by simpa [ls₁, Std.HashMap.getElem?_insert] using hl.modules) hc (evalLocalValue hnext₁)
  exact .consNormal (.assign (evalLocalValue hl.next) (assignLocalVarBase_ok hl.last))
    (.consNormal (.assign hn (assignLocalVarBase_ok hnext₁))
      (.consNormal (.assign (evalNatIncrement (evalLocalValue hcount₂) hfit)
        (assignLocalVarBase_ok hcount₂)) .nil))

theorem safeModulesCountLoop (evm : EVM.State) {locals start pageSize index current last fuel
  words next}
    (hl : ModulesCountLocals locals start pageSize index current last)
    (hc : current.toNat < EVM.addressModulus)
    (hf : index + fuel = pageSize.toNat)
    (hp : LinkedPage (moduleLink evm) fuel current words next) :
    ∃ locals', ExecStmt config { contract := contract, locals := locals } evm modulesCountLoop
        (.ok { contract := contract, locals := locals' } evm) ∧
      ModulesCountLocals locals' start pageSize (index + words.length) next (words.getLastD last)
        := by
  induction hp generalizing locals index last with
  | @stop fuel current hstop =>
      have hcond := safeModulesCountCondition evm hl hc
      have hfalse : ¬(current ≠ ⟨0⟩ ∧ current ≠ ⟨1⟩ ∧ index < pageSize.toNat) := by
        rcases hstop with hfuel | hz | hs
        · omega
        · simp [hz]
        · simp [hs]
      exact ⟨locals, .whileFalse (by simpa only [hfalse, decide_false] using hcond),
        by simpa only [List.length_nil, Nat.add_zero, List.getLastD_nil] using hl⟩
  | @step fuel current words next hz hs hp ih =>
      have hfit : index + 1 < UInt256.size := by
        have hsize : pageSize.toNat < UInt256.size := pageSize.val.isLt
        omega
      obtain ⟨locals', hloop, hl'⟩ := ih (safeModulesCountNextLocals evm hl)
        (solcAddrMask_result_canonical _) (by omega)
      have hcond := safeModulesCountCondition evm hl hc
      have htrue : current ≠ ⟨0⟩ ∧ current ≠ ⟨1⟩ ∧ index < pageSize.toNat :=
        ⟨hz, hs, by omega⟩
      refine ⟨locals', .whileTrue (by simpa only [hz, hs, htrue.2.2,
          ne_eq, not_false_eq_true, and_self, decide_true] using hcond)
        (safeModulesCountStep evm hl hc hfit) hloop, ?_⟩
      simpa only [List.length_cons, List.getLastD_cons, Nat.add_assoc,
        Nat.add_comm 1 words.length] using hl'

end Benchmarks.Safe
