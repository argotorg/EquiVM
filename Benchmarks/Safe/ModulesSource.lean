import Benchmarks.Safe.ModulesFillSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def modulesArgs (start pageSize : UInt256) : Store :=
  ((∅ : Store).insert "start" (addressArrayValue start)).insert
    "pageSize" (.int (Int.ofNat pageSize.toNat))

def modulesInitialLocals (evm : EVM.State) (start pageSize : UInt256) : Store :=
  (((modulesArgs start pageSize).insert "moduleCount" (.int 0)).insert
    "next" (addressArrayValue (moduleLink evm start))).insert "last" (addressArrayValue ⟨0⟩)

theorem safeModulesInitialLocals (evm : EVM.State) (start pageSize : UInt256) :
    ModulesCountLocals (modulesInitialLocals evm start pageSize) start pageSize 0
      (moduleLink evm start) ⟨0⟩ := by
  constructor <;> simp [modulesInitialLocals, modulesArgs, addressArrayValue,
    Std.HashMap.getElem_insert]

theorem safeModulesStartGuard (evm : EVM.State) (start pageSize : UInt256)
    (hc : start.toNat < EVM.addressModulus) :
    evalExpr? config { contract := contract, locals := modulesArgs start pageSize } evm
      (orE (eqE (.var "start") sentinelAddr) (moduleEnabledExpr (.var "start"))) =
      .ok (.bool (decide (start = ⟨1⟩ ∨ moduleLink evm start ≠ ⟨0⟩))) := by
  have he : evalExpr? config { contract := contract, locals := modulesArgs start pageSize } evm
      (.var "start") = .ok (addressArrayValue start) := by
    apply evalLocalValue
    simp [modulesArgs, Std.HashMap.getElem_insert]
  have heq := evalAddressEq hc (by decide) he (safeEvalModuleSentinel evm _)
  have hm := evalAddressMembership hc (solcAddrMask_result_canonical _) he
    (safeEvalModuleLink evm _ _ start (by simp [modulesArgs]) hc he)
  have h := evalBoolOr heq hm
  change evalExpr? _ _ _ _ = .ok (.bool
    (decide (start = ⟨1⟩) || decide (moduleLink evm start ≠ ⟨0⟩ ∧ start ≠ ⟨1⟩))) at h
  by_cases hs : start = ⟨1⟩ <;> simpa [orE, moduleEnabledExpr, hs] using h

theorem safeModulesSizeGuard (evm : EVM.State) (start pageSize : UInt256) :
    evalExpr? config { contract := contract, locals := modulesArgs start pageSize } evm
      (leE (.var "pageSize") maxMemoryLength) =
      .ok (.bool (decide (pageSize.toNat ≤ 2 ^ 64 - 1))) := by
  rw [leE, evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue (by
    show (modulesArgs start pageSize)["pageSize"]? = some (.int (Int.ofNat pageSize.toNat))
    simp [modulesArgs])]
  simp [maxMemoryLength, evalExpr?, evalBinaryOp?, EvalResult.bind, bind, pure]

theorem safeModulesNonzeroGuard (evm : EVM.State) (start pageSize : UInt256) :
    evalExpr? config { contract := contract, locals := modulesArgs start pageSize } evm
      (neE (.var "pageSize") (.intLit 0)) = .ok (.bool (decide (pageSize ≠ ⟨0⟩))) := by
  rw [neE, evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue (by
    show (modulesArgs start pageSize)["pageSize"]? = some (.int (Int.ofNat pageSize.toNat))
    simp [modulesArgs])]
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind, pure]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.int.injEq, Int.ofNat_eq_zero, decide_eq_true_eq]
  constructor
  · intro h
    exact u256_inj h
  · intro h
    exact congrArg UInt256.toNat h

def modulesSelectNext : Stmt :=
  .ite (neE (.var "next") sentinelAddr)
    [.require (gtE (.var "moduleCount") (.intLit 0)),
      .assign .localVar (varRef "next") (.var "last")] []

def modulesFillSuffix : List Stmt :=
  [.letDecl "array" (some (.dynamicArray addr)) (.newArray addrSt (.var "moduleCount")),
    .letDecl "fill" (some uint256) (.intLit 0),
    .letDecl "current" (some addr) (.storage (modulesRef (.var "start"))),
    modulesFillLoop, .return [.var "array", .var "next"]]

theorem safeModulesPrefix (evm : EVM.State) (start pageSize : UInt256) {result : ExecResult}
    (hc : start.toNat < EVM.addressModulus) (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hs : start = ⟨1⟩ ∨ moduleLink evm start ≠ ⟨0⟩) (hz : pageSize ≠ ⟨0⟩)
    (hn : pageSize.toNat ≤ 2 ^ 64 - 1)
    (htail : ExecBlock config
      { contract := contract, locals := modulesInitialLocals evm start pageSize } evm
      (modulesCountLoop :: modulesSelectNext :: modulesFillSuffix) result) :
    ExecBlock config { contract := contract, locals := modulesArgs start pageSize } evm
      getmodulespaginatedTransition.body result := by
  have hstart := safeModulesStartGuard evm start pageSize hc
  have hzero := safeModulesNonzeroGuard evm start pageSize
  have hbound := safeModulesSizeGuard evm start pageSize
  refine .consNormal (.requireTrue (evalCallvalueEq_true hv))
    (.consNormal (.requireTrue (by simpa only [hs, decide_true] using hstart))
      (.consNormal (.requireTrue (by simpa [hz] using hzero))
        (.consNormal (.requireTrue (by simpa only [hn, decide_true] using hbound))
          (.consNormal (.letDecl (by simp [evalExpr?, pure]))
            (.consNormal (.letDecl ?_) (.consNormal (.letDecl ?_) htail))))))
  · apply safeEvalModuleLink evm _ _ start (by simp [modulesArgs]) hc
    apply evalLocalValue
    simp [modulesArgs, Std.HashMap.getElem_insert, addressArrayValue]
  · simp [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.bind, bind, pure,
      EvalResult.ofOption, addressArrayValue]

theorem safeModulesSelectNextCondition (evm : EVM.State) {locals start pageSize index current last}
    (hl : ModulesCountLocals locals start pageSize index current last)
    (hc : current.toNat < EVM.addressModulus) :
    evalExpr? config { contract := contract, locals := locals } evm
      (neE (.var "next") sentinelAddr) = .ok (.bool (decide (current ≠ ⟨1⟩))) :=
  evalAddressNe hc (by decide) (evalLocalValue hl.next) (safeEvalModuleSentinel evm locals)

theorem safeModulesPositiveCondition (evm : EVM.State) {locals start pageSize index current last}
    (hl : ModulesCountLocals locals start pageSize index current last) :
    evalExpr? config { contract := contract, locals := locals } evm
      (gtE (.var "moduleCount") (.intLit 0)) = .ok (.bool (decide (0 < index))) := by
  rw [gtE, evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue hl.count]
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind, pure]

theorem safeModulesSelectNext (evm : EVM.State) {locals start pageSize index current last}
    (hl : ModulesCountLocals locals start pageSize index current last)
    (hc : current.toNat < EVM.addressModulus) (hg : current = ⟨1⟩ ∨ 0 < index) :
    ∃ locals', ExecStmt config { contract := contract, locals := locals } evm modulesSelectNext
        (.ok { contract := contract, locals := locals' } evm) ∧
      ModulesCountLocals locals' start pageSize index (if current = ⟨1⟩ then current else last)
        last := by
  have he := safeModulesSelectNextCondition evm hl hc
  by_cases hs : current = ⟨1⟩
  · exact ⟨locals, .iteFalse (by simpa [hs] using he) .nil, by simpa [hs] using hl⟩
  · have hi : 0 < index := hg.resolve_left hs
    have hpositive := safeModulesPositiveCondition evm hl
    refine ⟨locals.insert "next" (addressArrayValue last),
      .iteTrue (by simpa [hs] using he)
        (.consNormal (.requireTrue (by simpa only [hi, decide_true] using hpositive))
          (.consNormal (.assign (evalLocalValue hl.last) (assignLocalVarBase_ok hl.next)) .nil)),
            ?_⟩
    simp only [hs, if_false]
    constructor
    · simpa [Std.HashMap.getElem?_insert] using hl.start
    · simpa [Std.HashMap.getElem?_insert] using hl.pageSize
    · simpa [Std.HashMap.getElem?_insert] using hl.count
    · simp [addressArrayValue]
    · simpa [Std.HashMap.getElem?_insert] using hl.last
    · simpa [Std.HashMap.getElem?_insert] using hl.modules

theorem safeModulesFillSuffix (evm : EVM.State) {locals start pageSize words next last fuel current}
    (hl : ModulesCountLocals locals start pageSize words.length next last)
    (hp : LinkedPage (moduleLink evm) fuel (moduleLink evm start) words current)
    (hc : start.toNat < EVM.addressModulus) (hfit : words.length < UInt256.size) :
    ∃ locals', ExecBlock config { contract := contract, locals := locals } evm modulesFillSuffix
      (.returned { contract := contract, locals := locals' } evm
        (some [.array (words.map addressArrayValue), addressArrayValue next])) := by
  let ls₁ := locals.insert "array"
    (.array ((List.replicate words.length (⟨0⟩ : UInt256)).map addressArrayValue))
  let ls₂ := ls₁.insert "fill" (.int 0)
  let ls₃ := ls₂.insert "current" (addressArrayValue (moduleLink evm start))
  have hf : ModulesFillLocals ls₃ (List.replicate words.length ⟨0⟩) 0 words.length
      (moduleLink evm start) next := by
    constructor
    · simp [ls₃, ls₂, ls₁, Std.HashMap.getElem_insert]
    · simp [ls₃, ls₂, Std.HashMap.getElem_insert]
    · simpa [ls₃, ls₂, ls₁, Std.HashMap.getElem?_insert] using hl.count
    · simp [ls₃]
    · simpa [ls₃, ls₂, ls₁, Std.HashMap.getElem?_insert] using hl.next
    · simpa [ls₃, ls₂, ls₁, Std.HashMap.getElem?_insert] using hl.modules
  obtain ⟨locals', hloop, hout⟩ := safeModulesFillLoop evm (doneWords := []) hp
    (by simpa using hf) (solcAddrMask_result_canonical _) (by simp) hfit
  have hnew : evalExpr? config { contract := contract, locals := locals } evm
      (.newArray addrSt (.var "moduleCount")) =
      .ok (.array ((List.replicate words.length (⟨0⟩ : UInt256)).map addressArrayValue)) := by
    rw [evalExpr?, evalLocalValue hl.count]
    simp [EvalResult.bind, bind, pure, defaultValue?, addrSt, addressArrayValue]
  have hcurrent := safeEvalModuleLink evm ls₂ (.var "start") start
    (by simpa [ls₂, ls₁, Std.HashMap.getElem?_insert] using hl.modules) hc
    (evalLocalValue (by simpa [ls₂, ls₁, Std.HashMap.getElem?_insert] using hl.start))
  refine ⟨locals', .consNormal (.letDecl hnew)
    (.consNormal (.letDecl (by simp [evalExpr?, pure]))
      (.consNormal (.letDecl hcurrent) (.consNormal hloop (.consReturn (.return ?_)))))⟩
  simp [evalExprs?, evalExpr?, hout.array, hout.next, EvalResult.ofOption,
    EvalResult.bind, bind, pure]

def modulesPageNext (words : List UInt256) (next : UInt256) : UInt256 :=
  if next = ⟨1⟩ then next else words.getLastD ⟨0⟩

theorem safeModulesSourceSuccess (evm : EVM.State) (start pageSize : UInt256) {words next}
    (hc : start.toNat < EVM.addressModulus) (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hs : start = ⟨1⟩ ∨ moduleLink evm start ≠ ⟨0⟩) (hz : pageSize ≠ ⟨0⟩)
    (hn : pageSize.toNat ≤ 2 ^ 64 - 1)
    (hp : LinkedPage (moduleLink evm) pageSize.toNat (moduleLink evm start) words next)
    (hg : next = ⟨1⟩ ∨ 0 < words.length) :
    ∃ locals', ExecTransitionBody config contract evm (modulesArgs start pageSize)
      getmodulespaginatedTransition.body
      (.returned { contract := contract, locals := locals' } evm
        (some [.array (words.map addressArrayValue), addressArrayValue (modulesPageNext words
          next)])) := by
  obtain ⟨ls₁, hcount, hl₁⟩ := safeModulesCountLoop evm (safeModulesInitialLocals evm start
    pageSize)
    (solcAddrMask_result_canonical _) (by simp) hp
  simp only [Nat.zero_add] at hl₁
  obtain ⟨ls₂, hselect, hl₂⟩ := safeModulesSelectNext evm hl₁
    (hp.canonical (solcAddrMask_result_canonical _) (fun _ ↦ solcAddrMask_result_canonical _)).2 hg
  obtain ⟨locals', hfill⟩ := safeModulesFillSuffix evm hl₂ hp hc (by
    have := hp.length_le
    change words.length < 2 ^ 256
    omega)
  exact ⟨locals', .execBlockRet (safeModulesPrefix evm start pageSize hc hv hs hz hn
    (.consNormal hcount (.consNormal hselect hfill)))⟩

theorem safeModulesSourceEmpty (evm : EVM.State) (start pageSize : UInt256) {next}
    (hc : start.toNat < EVM.addressModulus) (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hs : start = ⟨1⟩ ∨ moduleLink evm start ≠ ⟨0⟩) (hz : pageSize ≠ ⟨0⟩)
    (hn : pageSize.toNat ≤ 2 ^ 64 - 1)
    (hp : LinkedPage (moduleLink evm) pageSize.toNat (moduleLink evm start) [] next)
    (hg : next ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (modulesArgs start pageSize)
      getmodulespaginatedTransition.body .reverted := by
  obtain ⟨locals, hcount, hl⟩ := safeModulesCountLoop evm (safeModulesInitialLocals evm start
    pageSize)
    (solcAddrMask_result_canonical _) (by simp) hp
  have he := safeModulesSelectNextCondition evm hl
    (hp.canonical (solcAddrMask_result_canonical _) (fun _ ↦ solcAddrMask_result_canonical _)).2
  have hpositive := safeModulesPositiveCondition evm hl
  exact .execBlockRevert (safeModulesPrefix evm start pageSize hc hv hs hz hn
    (.consNormal hcount (.consRevert (.iteTrue (by simpa [hg] using he)
      (.consRevert (.requireFalse (by simpa using hpositive)))))))

theorem safeModulesSourceInvalid (evm : EVM.State) (start pageSize : UInt256)
    (hc : start.toNat < EVM.addressModulus) (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hs : ¬(start = ⟨1⟩ ∨ moduleLink evm start ≠ ⟨0⟩)) :
    ExecTransitionBody config contract evm (modulesArgs start pageSize)
      getmodulespaginatedTransition.body .reverted := by
  have he := safeModulesStartGuard evm start pageSize hc
  exact .execBlockRevert (.consNormal (.requireTrue (evalCallvalueEq_true hv))
    (.consRevert (.requireFalse (by simpa only [hs, decide_false] using he))))

theorem safeModulesSourceZero (evm : EVM.State) (start pageSize : UInt256)
    (hc : start.toNat < EVM.addressModulus) (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hs : start = ⟨1⟩ ∨ moduleLink evm start ≠ ⟨0⟩) (hz : pageSize = ⟨0⟩) :
    ExecTransitionBody config contract evm (modulesArgs start pageSize)
      getmodulespaginatedTransition.body .reverted := by
  have he := safeModulesStartGuard evm start pageSize hc
  have hzero := safeModulesNonzeroGuard evm start pageSize
  exact .execBlockRevert (.consNormal (.requireTrue (evalCallvalueEq_true hv))
    (.consNormal (.requireTrue (by simpa only [hs, decide_true] using he))
      (.consRevert (.requireFalse (by simpa [hz] using hzero)))))

theorem safeModulesSourceLarge (evm : EVM.State) (start pageSize : UInt256)
    (hc : start.toNat < EVM.addressModulus) (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hs : start = ⟨1⟩ ∨ moduleLink evm start ≠ ⟨0⟩) (hz : pageSize ≠ ⟨0⟩)
    (hn : ¬pageSize.toNat ≤ 2 ^ 64 - 1) :
    ExecTransitionBody config contract evm (modulesArgs start pageSize)
      getmodulespaginatedTransition.body .reverted := by
  have he := safeModulesStartGuard evm start pageSize hc
  have hzero := safeModulesNonzeroGuard evm start pageSize
  have hbound := safeModulesSizeGuard evm start pageSize
  exact .execBlockRevert (.consNormal (.requireTrue (evalCallvalueEq_true hv))
    (.consNormal (.requireTrue (by simpa only [hs, decide_true] using he))
      (.consNormal (.requireTrue (by simpa [hz] using hzero))
        (.consRevert (.requireFalse (by simpa only [hn, decide_false] using hbound))))))

end Benchmarks.Safe
