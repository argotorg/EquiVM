import Benchmarks.Safe.LocalArrayRead
import Benchmarks.Safe.OwnerCount
import Benchmarks.Safe.OwnerGuards
import Benchmarks.Safe.InternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

structure SetupOwnersInput where
  owners : List UInt256
  threshold : UInt256

namespace SetupOwnersInput

def args (p : SetupOwnersInput) : Store :=
  ((∅ : Store).insert "_threshold" (uint256Value p.threshold)).insert
    "_owners" (.array (p.owners.map addressArrayValue))

def frame (p : SetupOwnersInput) : Frame := { contract := contract, locals := p.args }

def loopLocals (p : SetupOwnersInput) : Store :=
  ((p.args.insert "currentOwner" (addressArrayValue ⟨1⟩)).insert
    "ownersLength" (.int (Int.ofNat p.owners.length))).insert "i" (.int 0)

end SetupOwnersInput

def setupOwnersLoopCondition : Expr := ltE (.var "i") (.var "ownersLength")

def setupOwnersLoopBody : List Stmt :=
  [ .letDecl "owner" (some addr) (arrGet "_owners" (.var "i")),
    .require (neE (.var "owner") (.var "currentOwner")),
    .internalCall "requireCanAddOwner" [.var "owner"] "_ok",
    .assign .storage (ownersRef (.var "currentOwner")) (.var "owner"),
    .assign .localVar (varRef "currentOwner") (.var "owner"),
    .assign .localVar (varRef "i") (inc256 (.var "i")) ]

structure SetupOwnersLocals (p : SetupOwnersInput) (locals : Store) (i : Nat)
    (current : UInt256) : Prop where
  array : locals["_owners"]? = some (.array (p.owners.map addressArrayValue))
  threshold : locals["_threshold"]? = some (uint256Value p.threshold)
  length : locals["ownersLength"]? = some (.int (Int.ofNat p.owners.length))
  index : locals["i"]? = some (.int (Int.ofNat i))
  current : locals["currentOwner"]? = some (addressArrayValue current)
  ownersAbsent : locals["owners"]? = none
  countAbsent : locals["ownerCount"]? = none
  thresholdAbsent : locals["threshold"]? = none

theorem SetupOwnersLocals.initial (p : SetupOwnersInput) :
    SetupOwnersLocals p p.loopLocals 0 ⟨1⟩ := by
  constructor <;> simp [SetupOwnersInput.loopLocals, SetupOwnersInput.args,
    Std.HashMap.getElem_insert]

theorem SetupOwnersLocals.set {p locals i current}
    (h : SetupOwnersLocals p locals i current) (name : Ident) (value : Value)
    (hn : name ∉ ["_owners", "_threshold", "ownersLength", "i", "currentOwner", "owners",
      "ownerCount", "threshold"]) : SetupOwnersLocals p (locals.insert name value) i current := by
  simp only [List.mem_cons, List.mem_singleton, not_or] at hn
  constructor <;> simp [Std.HashMap.getElem?_insert, hn, h.array, h.threshold, h.length,
    h.index, h.current, h.ownersAbsent, h.countAbsent, h.thresholdAbsent]

def setupOwnersCheckedLocals (locals : Store) (owner : UInt256) : Store :=
  (locals.insert "owner" (addressArrayValue owner)).insert "_ok" .unit

def setupOwnersNextLocals (locals : Store) (owner : UInt256) (i : Nat) : Store :=
  ((setupOwnersCheckedLocals locals owner).insert "currentOwner" (addressArrayValue owner)).insert
    "i" (.int (Int.ofNat (i + 1)))

theorem SetupOwnersLocals.checked {p locals i current}
    (h : SetupOwnersLocals p locals i current) (owner : UInt256) :
    SetupOwnersLocals p (setupOwnersCheckedLocals locals owner) i current :=
  (h.set _ _ (by decide)).set _ _ (by decide)

theorem SetupOwnersLocals.next {p locals i current}
    (h : SetupOwnersLocals p locals i current) (owner : UInt256) :
    SetupOwnersLocals p (setupOwnersNextLocals locals owner i) (i + 1) owner := by
  have hc := h.checked owner
  constructor <;> simp [setupOwnersNextLocals, Std.HashMap.getElem?_insert,
    Std.HashMap.getElem_insert, hc.array, hc.threshold, hc.length, hc.ownersAbsent,
    hc.countAbsent, hc.thresholdAbsent]

theorem safeSetupOwnersCondition (evm : EVM.State) {p locals i current}
    (h : SetupOwnersLocals p locals i current) :
    evalExpr? config { contract := contract, locals := locals } evm setupOwnersLoopCondition =
      .ok (.bool (decide (i < p.owners.length))) := by
  rw [setupOwnersLoopCondition, ltE, evalExpr_binary_nonshort (by decide) (by decide),
    evalLocalValue h.index, evalLocalValue h.length]
  simp [EvalResult.bind, bind, evalBinaryOp?, Int.ofNat_eq_natCast, pure]

theorem safeSetupOwnersIndex (evm : EVM.State) {p locals i current}
    (h : SetupOwnersLocals p locals i current) (hi : i < p.owners.length) :
    evalExpr? config { contract := contract, locals := locals } evm (arrGet "_owners" (.var "i")) =
      .ok (addressArrayValue p.owners[i]) := by
  have he := evalLocalArrayIndex (cfg := config) (evm := evm)
      (frame := { contract := contract, locals := locals })
      h.array (evalLocalValue h.index) (by simpa using hi)
  rw [List.getElem_map] at he
  exact he

theorem safeInternalCanAddOwner {caller : Frame} {evm : EVM.State} {expr : Expr}
    {owner : UInt256} {retVar : Ident} {result : ExecResult}
    (hc : caller.contract = contract) (him : caller.immutables = ∅)
    (he : evalExpr? config caller evm expr = .ok (addressArrayValue owner))
    (hb : ExecFuncBody config (canAddOwnerFrame owner) evm requireCanAddOwnerFunction.body result) :
    ExecStmt config caller evm (.internalCall "requireCanAddOwner" [expr] retVar)
      (internalCallResult caller retVar result) := by
  apply internalCallFunctionResult (callee := requireCanAddOwnerFunction)
    (locals := canAddOwnerArgs owner) (evalExprs?_singleton he)
  · rw [hc]; rfl
  · rfl
  · simpa only [hc, him] using hb

end Benchmarks.Safe
