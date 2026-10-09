import Benchmarks.Safe.ModulesCountSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def modulesFillBody : List Stmt :=
  [ arrSet "array" (.var "fill") (.var "current"),
    .assign .localVar (varRef "current") (.storage (modulesRef (.var "current"))),
    .assign .localVar (varRef "fill") (inc256 (.var "fill")) ]

def modulesFillLoop : Stmt :=
  .while (ltE (.var "fill") (.var "moduleCount")) modulesFillBody

structure ModulesFillLocals (locals : Store) (words : List UInt256) (index count : Nat)
    (current next : UInt256) : Prop where
  array : locals["array"]? = some (.array (words.map addressArrayValue))
  fill : locals["fill"]? = some (.int (Int.ofNat index))
  count : locals["moduleCount"]? = some (.int (Int.ofNat count))
  current : locals["current"]? = some (addressArrayValue current)
  next : locals["next"]? = some (addressArrayValue next)
  modules : locals["modules"]? = none

theorem safeModulesFillCondition (evm : EVM.State) {locals words index count current next}
    (hl : ModulesFillLocals locals words index count current next) :
    evalExpr? config { contract := contract, locals := locals } evm
      (ltE (.var "fill") (.var "moduleCount")) = .ok (.bool (decide (index < count))) := by
  rw [ltE, evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue hl.fill,
    evalLocalValue hl.count]
  simp [EvalResult.bind, bind, pure, evalBinaryOp_lt_int_ok]

def modulesFillNextLocals (evm : EVM.State) (locals : Store) (words : List UInt256)
    (index : Nat) (current : UInt256) : Store :=
  ((locals.insert "array" (.array ((words.set index current).map addressArrayValue))).insert
    "current" (addressArrayValue (moduleLink evm current))).insert
      "fill" (.int (Int.ofNat (index + 1)))

theorem safeModulesFillNextLocals (evm : EVM.State) {locals words index count current next}
    (hl : ModulesFillLocals locals words index count current next) :
    ModulesFillLocals (modulesFillNextLocals evm locals words index current)
      (words.set index current) (index + 1) count (moduleLink evm current) next := by
  constructor
  · simp [modulesFillNextLocals, Std.HashMap.getElem_insert]
  · simp [modulesFillNextLocals, Std.HashMap.getElem_insert]
  · simpa [modulesFillNextLocals, Std.HashMap.getElem?_insert] using hl.count
  · simp [modulesFillNextLocals, Std.HashMap.getElem_insert]
  · simpa [modulesFillNextLocals, Std.HashMap.getElem?_insert] using hl.next
  · simpa [modulesFillNextLocals, Std.HashMap.getElem?_insert] using hl.modules

theorem safeModulesFillStep (evm : EVM.State) {locals words index count current next}
    (hl : ModulesFillLocals locals words index count current next)
    (hc : current.toNat < EVM.addressModulus) (hi : index < words.length)
    (hfit : index + 1 < UInt256.size) :
    ExecBlock config { contract := contract, locals := locals } evm modulesFillBody
      (.ok { contract := contract, locals :=
        modulesFillNextLocals evm locals words index current } evm) := by
  let ls₁ := locals.insert "array" (.array ((words.set index current).map addressArrayValue))
  let ls₂ := ls₁.insert "current" (addressArrayValue (moduleLink evm current))
  have hi₁ : ls₁["fill"]? = some (.int (Int.ofNat index)) := by
    simpa [ls₁, Std.HashMap.getElem?_insert] using hl.fill
  have hi₂ : ls₂["fill"]? = some (.int (Int.ofNat index)) := by
    simpa [ls₂, Std.HashMap.getElem?_insert] using hi₁
  have hc₁ : ls₁["current"]? = some (addressArrayValue current) := by
    simpa [ls₁, Std.HashMap.getElem?_insert] using hl.current
  have hwrite := assignLocalArray (cfg := config) (evm := evm) (expr := .var "fill")
    (frame := { contract := contract, locals := locals }) (addressArrayValue current)
    hl.array (evalLocalValue hl.fill) (by simpa using hi)
  simp only [← List.map_set] at hwrite
  have hnext := safeEvalModuleLink evm ls₁ (.var "current") current
    (by simpa [ls₁, Std.HashMap.getElem?_insert] using hl.modules) hc (evalLocalValue hc₁)
  exact .consNormal (.assign (evalLocalValue hl.current) hwrite)
    (.consNormal (.assign hnext (assignLocalVarBase_ok hc₁))
      (.consNormal (.assign (evalNatIncrement (evalLocalValue hi₂) hfit)
        (assignLocalVarBase_ok hi₂)) .nil))

theorem safeModulesFillLoop (evm : EVM.State) {locals doneWords fuel current words last next count}
    (hp : LinkedPage (moduleLink evm) fuel current words last)
    (hl : ModulesFillLocals locals (doneWords ++ List.replicate words.length ⟨0⟩)
      doneWords.length count current next)
    (hc : current.toNat < EVM.addressModulus)
    (hlen : doneWords.length + words.length = count) (hfit : count < UInt256.size) :
    ∃ locals', ExecStmt config { contract := contract, locals := locals } evm modulesFillLoop
        (.ok { contract := contract, locals := locals' } evm) ∧
      ModulesFillLocals locals' (doneWords ++ words) count count last next := by
  induction hp generalizing locals doneWords with
  | stop =>
      have hindex : doneWords.length = count := by simpa using hlen
      refine ⟨locals, .whileFalse ?_, ?_⟩
      · simpa only [hindex, lt_self_iff_false, decide_false] using
          safeModulesFillCondition evm hl
      · simpa only [List.length_nil, List.replicate_zero, hindex] using hl
  | @step fuel current words last hz hs hp ih =>
      have hi : doneWords.length <
          (doneWords ++ List.replicate (current :: words).length (⟨0⟩ : UInt256)).length := by
        simp
      have hinc : doneWords.length + 1 < UInt256.size := by
        simp only [List.length_cons] at hlen
        omega
      have hset : (doneWords ++ List.replicate (current :: words).length (⟨0⟩ : UInt256)).set
          doneWords.length current = (doneWords ++ [current]) ++ List.replicate words.length ⟨0⟩
            := by
        simp [List.set_append_right, List.replicate_succ, List.append_assoc]
      have hl' := safeModulesFillNextLocals evm hl
      rw [hset] at hl'
      obtain ⟨locals', hloop, hout⟩ := ih
        (doneWords := doneWords ++ [current]) (by simpa using hl')
        (solcAddrMask_result_canonical _) (by
          simp only [List.length_append, List.length_singleton]
          simp only [List.length_cons] at hlen
          omega)
      refine ⟨locals', .whileTrue ?_ (safeModulesFillStep evm hl hc hi hinc) hloop, ?_⟩
      · have hlt : doneWords.length < count := by simp only [List.length_cons] at hlen; omega
        simpa only [hlt, decide_true] using safeModulesFillCondition evm hl
      · simpa only [List.append_assoc, List.singleton_append] using hout

end Benchmarks.Safe
