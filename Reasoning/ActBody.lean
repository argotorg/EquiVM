import Reasoning.Theory

/-!
# ActBody — compositional lemmas for the Act contract body

The Act-side analogue of the EVM trace: facts about `ExecContractBody` / `ExecStmt`.  The piece
shared across every solc contract is the **non-payable guard** `require(callvalue == 0)` that opens
each transition body — its evaluation (both directions) and the body-revert it produces under
non-zero call value.  Statement-level combinators for the success path / loops can be added here as
more contracts need them.
-/

open Act ABI Ethereum

namespace Reasoning.Theory

/-- The non-payable guard `callvalue == 0` evaluates to `true` when the call value is zero. -/
theorem evalCallvalueEq_true {cfg : Config} {act : Frame} {evm : EVM.State}
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    evalExpr? cfg act evm (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) := by
  have hval : (Value.int (Int.ofNat evm.executionEnv.weiValue.val) == Value.int 0) = true := by
    rw [h]; rfl
  simp only [evalExpr?, EvalResult.bind, bind, pure, envValue, evalBinaryOp?, hval]

/-- The non-payable guard `callvalue == 0` evaluates to `false` when the call value is non-zero. -/
theorem evalCallvalueEq_false {cfg : Config} {act : Frame} {evm : EVM.State}
    (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    evalExpr? cfg act evm (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool false) := by
  have hval : (Value.int (Int.ofNat evm.executionEnv.weiValue.val) == Value.int 0) = false := by
    rw [beq_eq_false_iff_ne]; intro hh; rw [Value.int.injEq] at hh
    exact h (uint256_toNat_eq_zero (Int.ofNat.inj hh))
  simp only [evalExpr?, EvalResult.bind, bind, pure, envValue, evalBinaryOp?, hval]

/-- **The non-payable guard reverts the body.**  Any transition whose body opens with
    `require(callvalue == 0)` reverts when the call value is non-zero — independent of the rest of
    the body.  Shared by every contract's `callvalue ≠ 0` case. -/
theorem bodyReverts_nonPayable {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {locals : Store} {rest : List Stmt}
    (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecContractBody cfg contract evm locals
      (.require (.binary .eq (.env .callvalue) (.intLit 0)) :: rest) .reverted :=
  ExecFuncBody.execBlockRevert (ExecBlock.consRevert (ExecStmt.requireFalse (evalCallvalueEq_false h)))

/-- **Hoare while-rule for the Act semantics** — the loop analog of the EVM `RD.loop`.

    A variant-indexed invariant `P : ℕ → Store → Prop` (`P v L` = "invariant holds with `v`
    iterations to go") that
    * makes the loop condition **false** at variant `0` (`hfalse`),
    * makes it **true** at `v+1` (`htrue`), and
    * carries one body iteration from `P (v+1)` to `P v`, leaving the EVM state and contract fixed
      (`hstep`),
    drives the `while` to a final store satisfying `P 0`, from any starting variant.  The EVM state
    and contract are loop-invariant; only the locals change (an Act loop touches no EVM state). -/
theorem execWhile_var {cfg : Config} {C : ContractDecl} {evm : EVM.State}
    {cond : Expr} {body : List Stmt} (P : ℕ → Act.Store → Prop)
    (hfalse : ∀ L, P 0 L →
        evalExpr? cfg { contract := C, locals := L } evm cond = .ok (.bool false))
    (htrue : ∀ v L, P (v + 1) L →
        evalExpr? cfg { contract := C, locals := L } evm cond = .ok (.bool true))
    (hstep : ∀ v L, P (v + 1) L →
        ∃ L', ExecBlock cfg { contract := C, locals := L } evm body
                (.ok { contract := C, locals := L' } evm) ∧ P v L') :
    ∀ v L, P v L → ∃ L',
      ExecStmt cfg { contract := C, locals := L } evm (.while cond body)
        (.ok { contract := C, locals := L' } evm) ∧ P 0 L' := by
  intro v
  induction v with
  | zero => intro L hP; exact ⟨L, ExecStmt.whileFalse (hfalse L hP), hP⟩
  | succ v ih =>
    intro L hP
    obtain ⟨L1, hbody, hP1⟩ := hstep v L hP
    obtain ⟨L', hwhile, hP'⟩ := ih L1 hP1
    exact ⟨L', ExecStmt.whileTrue (htrue v L hP) hbody hwhile, hP'⟩

/-! ## Forward block builder

`ExecBlock` is built tail-first (`consNormal` needs the rest), so a straight-line body reads
inside-out.  `ABlock` is the difference-list/CPS view that lets it read **left-to-right** like
`evm_run`: `ABlock cfg evm act₀ stmts₀ act stmts` transforms a continuation from the cursor
`(act, stmts)` into the whole block from `(act₀, stmts₀)`.  Chain with `start |>.requireStep …
|>.letStep … |>.whileStep …` and close with a terminal (`returns` / `requireRevert`); wrap the
result with `ExecFuncBody.execBlockRet` / `.execBlockRevert` to get an `ExecContractBody`. -/

/-- A straight-line `ExecBlock` builder, cursor `(act, stmts)` over fixed entry `(act₀, stmts₀)`.
    (A one-field structure so the combinators chain by dot-notation.) -/
structure ABlock (cfg : Config) (evm : EVM.State) (act₀ : Frame) (stmts₀ : List Stmt)
    (act : Frame) (stmts : List Stmt) : Prop where
  run : ∀ {result}, ExecBlock cfg act evm stmts result → ExecBlock cfg act₀ evm stmts₀ result

/-- Open a builder at the entry frame. -/
theorem ABlock.start {cfg evm act stmts} : ABlock cfg evm act stmts act stmts := ⟨fun h => h⟩

/-- A passing `require` (frame unchanged). -/
theorem ABlock.requireStep {cfg evm act₀ stmts₀ act rest} {cond : Expr}
    (prev : ABlock cfg evm act₀ stmts₀ act (.require cond :: rest))
    (heval : evalExpr? cfg act evm cond = .ok (.bool true)) :
    ABlock cfg evm act₀ stmts₀ act rest :=
  ⟨fun h => prev.run (ExecBlock.consNormal (ExecStmt.requireTrue heval) h)⟩

/-- A `let` binding (advances the cursor's locals). -/
theorem ABlock.letStep {cfg evm act₀ stmts₀ act rest} {name ty expr value}
    (prev : ABlock cfg evm act₀ stmts₀ act (.letDecl name ty expr :: rest))
    (heval : evalExpr? cfg act evm expr = .ok value) :
    ABlock cfg evm act₀ stmts₀ { act with locals := act.locals.insert name value } rest :=
  ⟨fun h => prev.run (ExecBlock.consNormal (ExecStmt.letDecl heval) h)⟩

/-- A `while` loop that runs to `.ok` at frame `act'` (supply the loop fact, e.g. `execWhile_var`). -/
theorem ABlock.whileStep {cfg evm act₀ stmts₀ act act' rest} {cond body}
    (prev : ABlock cfg evm act₀ stmts₀ act (.while cond body :: rest))
    (hwhile : ExecStmt cfg act evm (.while cond body) (.ok act' evm)) :
    ABlock cfg evm act₀ stmts₀ act' rest :=
  ⟨fun h => prev.run (ExecBlock.consNormal hwhile h)⟩

/-- Close with a `return` ⇒ the block returns `value`. -/
theorem ABlock.returns {cfg evm act₀ stmts₀ act rest} {expr value}
    (prev : ABlock cfg evm act₀ stmts₀ act (.return expr :: rest))
    (heval : evalExpr? cfg act evm expr = .ok value) :
    ExecBlock cfg act₀ evm stmts₀ (.returned act evm (some value)) :=
  prev.run (ExecBlock.consReturn (ExecStmt.return heval))

/-- Close with a failing `require` ⇒ the block reverts. -/
theorem ABlock.requireRevert {cfg evm act₀ stmts₀ act rest} {cond : Expr}
    (prev : ABlock cfg evm act₀ stmts₀ act (.require cond :: rest))
    (heval : evalExpr? cfg act evm cond = .ok (.bool false)) :
    ExecBlock cfg act₀ evm stmts₀ .reverted :=
  prev.run (ExecBlock.consRevert (ExecStmt.requireFalse heval))

/-! ## `Act.Store` (locals) lookup -/

/-- Reading the key just inserted. -/
theorem store_get_self (L : Act.Store) (k : Ident) (v : Value) :
    (L.insert k v).get? k = some v := by simp

/-- Reading a key untouched by an insert of a different key. -/
theorem store_get_ne (L : Act.Store) {k a : Ident} (v : Value) (h : (k == a) = false) :
    (L.insert k v).get? a = L.get? a := by
  simp [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, h]

end Reasoning.Theory
