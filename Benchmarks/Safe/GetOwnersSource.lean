import Benchmarks.Safe.OwnerCount
import Benchmarks.Safe.LocalArrays

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def getOwnersLoopBody : List Stmt :=
  [ arrSet "array" (.var "index") (.var "currentOwner"),
    .assign .localVar (varRef "currentOwner") (.storage (ownersRef (.var "currentOwner"))),
    .assign .localVar (varRef "index") (inc256 (.var "index")) ]

def getOwnersLoop : Stmt :=
  .while (neE (.var "currentOwner") sentinelAddr) getOwnersLoopBody

structure GetOwnersLocals (locals : Store) (words : List UInt256) (i : Nat)
    (current : UInt256) : Prop where
  array : locals["array"]? = some (.array (words.map addressArrayValue))
  index : locals["index"]? = some (.int (Int.ofNat i))
  currentOwner : locals["currentOwner"]? = some (addressArrayValue current)
  owners : locals["owners"]? = none

def getOwnersInitialLocals (evm : EVM.State) : Store :=
  (((∅ : Store).insert "array"
    (.array ((List.replicate (ownerCount evm).toNat ⟨0⟩).map addressArrayValue))).insert
      "index" (.int 0)).insert "currentOwner" (addressArrayValue (ownerLink evm ⟨1⟩))

theorem safeGetOwnersInitialLocals (evm : EVM.State) :
    GetOwnersLocals (getOwnersInitialLocals evm)
      (List.replicate (ownerCount evm).toNat ⟨0⟩) 0 (ownerLink evm ⟨1⟩) := by
  constructor <;> simp [getOwnersInitialLocals, Std.HashMap.getElem_insert]

theorem safeGetOwnersCountGuard (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := ∅ } evm
      (leE (.storage ownerCountRef) maxMemoryLength) =
      .ok (.bool (decide ((ownerCount evm).toNat ≤ 2 ^ 64 - 1))) := by
  rw [leE, evalExpr_binary_nonshort (by decide) (by decide), safeEvalOwnerCount evm ∅ (by simp)]
  simp [maxMemoryLength, evalExpr?, evalBinaryOp?, EvalResult.bind, bind, pure]

theorem safeGetOwnersPrefix (evm : EVM.State) {result : ExecResult}
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : (ownerCount evm).toNat ≤ 2 ^ 64 - 1)
    (htail : ExecBlock config { contract := contract, locals := getOwnersInitialLocals evm }
      evm [getOwnersLoop, .return [.var "array"]] result) :
    ExecBlock config { contract := contract, locals := ∅ } evm getownersTransition.body
      result := by
  have hnew : evalExpr? config { contract := contract, locals := ∅ } evm
      (.newArray addrSt (.storage ownerCountRef)) =
      .ok (.array ((List.replicate (ownerCount evm).toNat ⟨0⟩).map addressArrayValue)) := by
    rw [evalExpr?, safeEvalOwnerCount evm ∅ (by simp)]
    simp [EvalResult.bind, bind, pure, defaultValue?, addrSt, addressArrayValue]
  refine .consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by
      simpa only [hlen, decide_true] using safeGetOwnersCountGuard evm))
      (.consNormal (.letDecl hnew) (.consNormal (.letDecl (by simp [evalExpr?, pure]))
        (.consNormal (.letDecl ?_) htail))))
  exact safeEvalOwnerLink evm _ sentinelAddr ⟨1⟩ (by simp [Std.HashMap.getElem_insert])
    (by decide) (safeEvalOwnerSentinel evm _)

theorem safeGetOwnersCountRevert (evm : EVM.State)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : ¬(ownerCount evm).toNat ≤ 2 ^ 64 - 1) :
    ExecTransitionBody config contract evm ∅ getownersTransition.body .reverted :=
  .execBlockRevert (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consRevert (.requireFalse (by
      simpa only [hlen, decide_false] using safeGetOwnersCountGuard evm))))

theorem safeGetOwnersCondition (evm : EVM.State) {locals words i current}
    (hl : GetOwnersLocals locals words i current)
    (hc : current.toNat < EVM.addressModulus) :
    evalExpr? config { contract := contract, locals := locals } evm
      (neE (.var "currentOwner") sentinelAddr) =
      .ok (.bool (decide (current ≠ ⟨1⟩))) :=
  evalAddressNe hc (by decide) (evalLocalValue hl.currentOwner)
    (safeEvalModuleSentinel evm locals)

def getOwnersNextLocals (evm : EVM.State) (locals : Store) (words : List UInt256)
    (i : Nat) (current : UInt256) : Store :=
  ((locals.insert "array" (.array ((words.set i current).map addressArrayValue))).insert
    "currentOwner" (addressArrayValue (ownerLink evm current))).insert
      "index" (.int (Int.ofNat (i + 1)))

theorem safeGetOwnersNextLocals (evm : EVM.State) {locals words i current}
    (hl : GetOwnersLocals locals words i current) :
    GetOwnersLocals (getOwnersNextLocals evm locals words i current)
      (words.set i current) (i + 1) (ownerLink evm current) := by
  constructor
  · simp [getOwnersNextLocals, Std.HashMap.getElem_insert]
  · simp [getOwnersNextLocals, Std.HashMap.getElem_insert]
  · simp [getOwnersNextLocals, Std.HashMap.getElem_insert]
  · simpa [getOwnersNextLocals, Std.HashMap.getElem_insert] using hl.owners

theorem safeGetOwnersLoopStep (evm : EVM.State) {locals words i current}
    (hl : GetOwnersLocals locals words i current)
    (hc : current.toNat < EVM.addressModulus) (hi : i < words.length)
    (hfit : i + 1 < UInt256.size) :
    ExecBlock config { contract := contract, locals := locals } evm getOwnersLoopBody
      (.ok { contract := contract, locals := getOwnersNextLocals evm locals words i current } evm)
        := by
  let locals₁ := locals.insert "array" (.array ((words.set i current).map addressArrayValue))
  let locals₂ := locals₁.insert "currentOwner" (addressArrayValue (ownerLink evm current))
  have hi₁ : locals₁["index"]? = some (.int (Int.ofNat i)) := by
    simpa [locals₁, Std.HashMap.getElem?_insert] using hl.index
  have hi₂ : locals₂["index"]? = some (.int (Int.ofNat i)) := by
    simpa [locals₂, Std.HashMap.getElem?_insert] using hi₁
  have hc₁ : locals₁["currentOwner"]? = some (addressArrayValue current) := by
    simpa [locals₁, Std.HashMap.getElem?_insert] using hl.currentOwner
  have hfirst := assignLocalArray (cfg := config) (evm := evm) (expr := .var "index")
    (frame := { contract := contract, locals := locals }) (addressArrayValue current)
    hl.array (evalLocalValue hl.index) (by simpa using hi)
  simp only [← List.map_set] at hfirst
  have hnext := safeEvalOwnerLink evm locals₁ (.var "currentOwner") current
    (by simpa [locals₁, Std.HashMap.getElem?_insert] using hl.owners) hc (evalLocalValue hc₁)
  have hinc : evalExpr? config { contract := contract, locals := locals₂ } evm
      (inc256 (.var "index")) = .ok (.int (Int.ofNat (i + 1))) := by
    exact evalNatIncrement (evalLocalValue hi₂) hfit
  refine .consNormal (.assign (evalLocalValue hl.currentOwner) hfirst)
    (.consNormal (.assign hnext (assignLocalVarBase_ok hc₁))
      (.consNormal (.assign hinc (assignLocalVarBase_ok hi₂)) .nil))

theorem safeGetOwnersLoopBounds (evm : EVM.State) {locals words i current}
    (hl : GetOwnersLocals locals words i current) (hi : words.length ≤ i) :
    ExecBlock config { contract := contract, locals := locals } evm getOwnersLoopBody
      .reverted :=
  .consRevert (.assignStoreRevert (evalLocalValue hl.currentOwner)
    (assignLocalArrayRevert (addressArrayValue current) hl.array
      (evalLocalValue hl.index) (by simpa using hi)))

theorem safeGetOwnersReturn (evm : EVM.State) {locals words i current}
    (hl : GetOwnersLocals locals words i current) :
    ExecBlock config { contract := contract, locals := locals } evm [.return [.var "array"]]
      (.returned { contract := contract, locals := locals } evm
        (some [.array (words.map addressArrayValue)])) :=
  .consReturn (.return (evalExprs?_singleton (evalLocalValue hl.array)))

end Benchmarks.Safe
