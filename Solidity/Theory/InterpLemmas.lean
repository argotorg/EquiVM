import Solidity.Interp

/-!
# Interpreter monad lemmas and result conversions

`IM = ExceptT ByteArray Option`: `run` of the monadic operations, and the conversions from
interpreter results to the relational result types (`Res`, `ExecResult`, `FnResult`).
-/

namespace Solidity

open Interp

/-! ## `run` of the monad operations -/

@[simp] theorem IM.run_pure {α} (a : α) : (pure a : IM α).run = some (.ok a) := rfl

@[simp] theorem IM.run_throw {α} (d : ByteArray) : (throw d : IM α).run = some (.error d) := rfl

@[simp] theorem IM.run_failure {α} : (failure : IM α).run = none := rfl

@[simp] theorem IM.run_bind {α β} (x : IM α) (f : α → IM β) :
    (x >>= f).run =
      match x.run with
      | none => none
      | some (.error d) => some (.error d)
      | some (.ok a) => (f a).run := by
  rcases x with _ | (d | a) <;> rfl

@[simp] theorem liftOp_run {α} (x : Op α) :
    (liftOp x).run =
      match x with
      | none => none
      | some (.error p) => some (.error p.data)
      | some (.ok a) => some (.ok a) := by
  rcases x with _ | (p | a) <;> rfl

@[simp] theorem liftOpt_run {α} (x : Option α) :
    (liftOpt x).run = match x with | none => none | some a => some (.ok a) := by
  cases x <;> rfl

@[simp] theorem guard'_run (b : Bool) : (guard' b).run = if b then some (.ok ()) else none := by
  cases b <;> rfl

/-! ## The EVM bridges: the interpreter's functions satisfy the relational bridges -/

theorem callViaEVM_sound (o : Oracle) (m : Machine) (t : EVM.Address) (v : Nat) (cd : EVM.Bytes) (perm : Bool)
    (gas : Ethereum.UInt256) : callViaEVM o m t v cd perm gas (Interp.callViaEVM o m t v cd perm gas) := by
  dsimp only [Interp.callViaEVM]
  split
  · rename_i hc
    rcases hΘ : Ethereum.EVM.Θ m.evm.executionEnv.blobVersionedHashes m.evm.createdAccounts
        m.evm.genesisBlockHeader m.evm.blocks m.evm.accountMap m.evm.σ₀ (subInput o m) m.this
        m.evm.executionEnv.sender t (Ethereum.toExecute m.evm.accountMap t) gas
        (.ofNat m.evm.executionEnv.gasPrice) (EVM.Word.ofNat v) (EVM.Word.ofNat v) cd
        (m.evm.executionEnv.depth + 1) m.evm.executionEnv.header perm with ⟨cA', σ', g', A', z, out⟩
    exact .callMade rfl hc.1 hc.2 hΘ.symm
  · rename_i hc
    refine .callNotMade rfl ?_
    rcases Decidable.em (EVM.Word.ofNat v ≤ (m.evm.accountMap.find? m.this |>.getD default).balance) with h1 | h1
    · exact Or.inr (by_contra fun h2 => hc ⟨h1, h2⟩)
    · exact Or.inl (lt_of_not_ge (α := Fin Ethereum.UInt256.size) h1)

theorem delegateCallViaEVM_sound (o : Oracle) (m : Machine) (t : EVM.Address) (cd : EVM.Bytes)
    (gas : Ethereum.UInt256) : delegateCallViaEVM o m t cd gas (Interp.delegateCallViaEVM o m t cd gas) := by
  dsimp only [Interp.delegateCallViaEVM]
  split
  · rename_i hc
    rcases hΘ : Ethereum.EVM.Θ m.evm.executionEnv.blobVersionedHashes m.evm.createdAccounts
        m.evm.genesisBlockHeader m.evm.blocks m.evm.accountMap m.evm.σ₀ (subInput o m)
        m.evm.executionEnv.source m.evm.executionEnv.sender m.this
        (Ethereum.toExecute m.evm.accountMap t) gas
        (.ofNat m.evm.executionEnv.gasPrice) ⟨0⟩ m.evm.executionEnv.weiValue cd
        (m.evm.executionEnv.depth + 1) m.evm.executionEnv.header m.evm.executionEnv.perm with ⟨cA', σ', g', A', z, out⟩
    exact .callMade hc hΘ.symm
  · rename_i hc
    exact .callNotMade (by_contra hc)

theorem newViaEVM_sound (cfg : Config) (o : Oracle) (m : Machine) (c : Ident) (v : Nat) (args : List Solm.Value)
    (salt : Option ByteArray) {r} (h : Interp.newViaEVM cfg o m c v args salt = some r) :
    newViaEVM cfg o m c v args salt r := by
  dsimp only [Interp.newViaEVM] at h
  split at h
  · cases h
  · rename_i initCode hcc
    split at h
    · rename_i hc
      cases h
      exact .created hcc rfl rfl hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 rfl rfl
    · rename_i hc
      cases h
      refine .notCreated hcc rfl rfl ?_
      rcases Decidable.em (EVM.Word.ofNat v ≤ ((m.evm.accountMap.find? m.this).getD default).balance) with h1 | h1
      · rcases Decidable.em (m.evm.executionEnv.depth = 1024) with h2 | h2
        · exact Or.inr (Or.inl h2)
        · rcases Decidable.em (((m.evm.accountMap.find? m.this).getD default).nonce.toNat < 2 ^ 64 - 1) with h3 | h3
          · rcases Decidable.em (initCode.size ≤ 49152) with h4 | h4
            · exact absurd ⟨h1, h2, h3, h4⟩ hc
            · exact Or.inr (Or.inr (Or.inr (Nat.lt_of_not_le h4)))
          · exact Or.inr (Or.inr (Or.inl (Nat.le_of_not_lt h3)))
      · exact Or.inl (lt_of_not_ge (α := Fin Ethereum.UInt256.size) h1)

/-- `abiArgsAbi` never panics. -/
theorem abiArgsAbi_ne_error (cfg : Config) (env : TypeEnv) (m : Machine) (tys : List ABI.ABIType) (vs : List Value) (p : Panic) :
    abiArgsAbi cfg env m tys vs ≠ some (.error p) := by
  intro h
  unfold abiArgsAbi at h
  cases hm : vs.mapM (toAbi m.heap fuelDefault) <;>
    simp [hm, Op.ofOpt, bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, pure, ExceptT.pure] at h <;>
    try cases h

/-! ## Result conversions -/

/-- `Res α` of an interpreter result. -/
def resOf {α} : Except ByteArray (α × Frame × Machine) → Res α
  | .ok (a, fr, m) => .ok a fr m
  | .error d => .reverted d

/-- `Res Unit` of a frame/machine result (tuple assignment / declaration). -/
def unitResOf : Except ByteArray (Frame × Machine) → Res Unit
  | .ok (fr, m) => .ok () fr m
  | .error d => .reverted d

def execOf : Except ByteArray ExecResult → ExecResult
  | .ok r => r
  | .error d => .reverted d

def fnOf : Except ByteArray (List Value × Machine) → FnResult
  | .ok (rets, m) => .ok rets m
  | .error d => .reverted d

@[simp] theorem resOf_ok {α} (a : α) (fr : Frame) (m : Machine) : resOf (.ok (a, fr, m)) = .ok a fr m := rfl
@[simp] theorem resOf_error {α} (d : ByteArray) : (resOf (.error d) : Res α) = .reverted d := rfl
@[simp] theorem unitResOf_ok (fr : Frame) (m : Machine) : unitResOf (.ok (fr, m)) = .ok () fr m := rfl
@[simp] theorem unitResOf_error (d : ByteArray) : unitResOf (.error d) = .reverted d := rfl
@[simp] theorem execOf_ok (r : ExecResult) : execOf (.ok r) = r := rfl
@[simp] theorem execOf_error (d : ByteArray) : execOf (.error d) = .reverted d := rfl
@[simp] theorem fnOf_ok (rets : List Value) (m : Machine) : fnOf (.ok (rets, m)) = .ok rets m := rfl
@[simp] theorem fnOf_error (d : ByteArray) : fnOf (.error d) = .reverted d := rfl

/-! ## Soundness at a fuel level: the induction hypothesis -/

variable (cfg : Config) (o : Oracle) (fc : FlatContract)

/-- Every member of the interpreter agrees with its family at fuel `n`. -/
structure SoundAt (n : Nat) : Prop where
  expr : ∀ fr m e r, (evalExpr cfg o fc n fr m e).run = some r → EvalExpr cfg o fc fr m e (resOf r)
  member : ∀ fr m e f r, directMember fc fr e = false → (evalMember cfg o fc n fr m e f).run = some r →
    EvalExpr cfg o fc fr m (.member e f) (resOf r)
  builtin : ∀ fr m f args r, (evalBuiltin cfg o fc n fr m f args).run = some r →
    EvalExpr cfg o fc fr m (.call (.ident f) [] args) (resOf r)
  call : ∀ fr m callee opts args r, (evalCall cfg o fc n fr m callee opts args).run = some r →
    EvalExpr cfg o fc fr m (.call callee opts args) (resOf r)
  namedCall : ∀ fr m f args r, isBuiltinFn f = false → (evalNamedCall cfg o fc n fr m f [] args).run = some r →
    EvalExpr cfg o fc fr m (.call (.ident f) [] args) (resOf r)
  abi : ∀ fr m f es r, (evalAbi cfg o fc n fr m f es).run = some r →
    EvalExpr cfg o fc fr m (.call (.member (.ident "abi") f) [] (.positional es)) (resOf r)
  memberCall : ∀ fr m recv f opts args r, (evalMemberCall cfg o fc n fr m recv f opts args).run = some r →
    EvalExpr cfg o fc fr m (.call (.member recv f) opts args) (resOf r)
  valueOpt : ∀ fr m e r, (evalValueOpt cfg o fc n fr m e).run = some r → EvalValueOpt cfg o fc fr m e (resOf r)
  saltOpt : ∀ fr m e r, (evalSaltOpt cfg o fc n fr m e).run = some r → EvalSaltOpt cfg o fc fr m e (resOf r)
  gasOpt : ∀ fr m e r, (evalGasOpt cfg o fc n fr m e).run = some r → EvalGasOpt cfg o fc fr m e (resOf r)
  exprs : ∀ fr m es r, (evalExprs cfg o fc n fr m es).run = some r → EvalExprs cfg o fc fr m es (resOf r)
  lvalue : ∀ fr m e r, (evalLValue cfg o fc n fr m e).run = some r → EvalLValue cfg o fc fr m e (resOf r)
  assignTuple : ∀ fr m ls vs r, (assignTuple cfg o fc n fr m ls vs).run = some r →
    AssignTuple cfg o fc fr m ls vs (unitResOf r)
  declareTuple : ∀ fr m bs vs r, (declareTuple cfg o fc n fr m bs vs).run = some r →
    DeclareTuple cfg o fc fr m bs vs (unitResOf r)
  stmt : ∀ fr m s r, (execStmt cfg o fc n fr m s).run = some r → ExecStmt cfg o fc fr m s (execOf r)
  loop : ∀ fr m c post body r, (execLoop cfg o fc n fr m c post body).run = some r →
    ExecLoop cfg o fc fr m c post body (execOf r)
  loopBody : ∀ fr m c post body fr1 m1 r, EvalCond cfg o fc fr m c (.ok true fr1 m1) →
    (execLoopBody cfg o fc n fr1 m1 c post body).run = some r → ExecLoop cfg o fc fr m c post body (execOf r)
  block : ∀ fr m ss r, (execBlock cfg o fc n fr m ss).run = some r → ExecBlock cfg o fc fr m ss (execOf r)
  chain : ∀ fr m mods body r, (execChain cfg o fc n fr m mods body).run = some r →
    ExecChain cfg o fc fr m mods body (execOf r)
  mods : ∀ fr m mis r, (evalMods cfg o fc n fr m mis).run = some r → EvalMods cfg o fc fr m mis (resOf r)
  callFn : ∀ fr m fn args r, (callFn cfg o fc n fr m fn args).run = some r → CallFn cfg o fc fr m fn args (fnOf r)

/-- At fuel `0` every member fails. -/
theorem soundAt_zero : SoundAt cfg o fc 0 where
  expr := by intros; simp [evalExpr] at *
  member := by intros; simp [evalMember] at *
  builtin := by intros; simp [evalBuiltin] at *
  call := by intros; simp [evalCall] at *
  namedCall := by intros; simp [evalNamedCall] at *
  abi := by intros; simp [evalAbi] at *
  memberCall := by intros; simp [evalMemberCall] at *
  valueOpt := by intros; simp [evalValueOpt] at *
  saltOpt := by intros; simp [evalSaltOpt] at *
  gasOpt := by intros; simp [evalGasOpt] at *
  exprs := by intros; simp [evalExprs] at *
  lvalue := by intros; simp [evalLValue] at *
  assignTuple := by intros; simp [assignTuple] at *
  declareTuple := by intros; simp [declareTuple] at *
  stmt := by intros; simp [execStmt] at *
  loop := by intros; simp [execLoop] at *
  loopBody := by intros; simp [execLoopBody] at *
  block := by intros; simp [execBlock] at *
  chain := by intros; simp [execChain] at *
  mods := by intros; simp [evalMods] at *
  callFn := by intros; simp [callFn] at *

end Solidity

namespace Solidity

/-- Inversion of a successful `bind`. -/
theorem IM.bind_some {α β} {x : IM α} {f : α → IM β} {r} (h : (x >>= f).run = some r) :
    (∃ d, x.run = some (.error d) ∧ r = .error d) ∨ (∃ a, x.run = some (.ok a) ∧ (f a).run = some r) := by
  rw [IM.run_bind] at h
  split at h
  · exact absurd h (by simp)
  · rename_i d hd; exact Or.inl ⟨d, hd, (Option.some.inj h).symm⟩
  · rename_i a ha; exact Or.inr ⟨a, ha, h⟩

theorem IM.pure_some {α} {a : α} {r} (h : (pure a : IM α).run = some r) : r = .ok a :=
  (Option.some.inj h).symm


theorem IM.throw_some {α} {d : ByteArray} {r : Except ByteArray α} (h : (throw d : IM α).run = some r) :
    r = .error d :=
  (Option.some.inj h).symm

theorem IM.failure_some {α} {r : Except ByteArray α} (h : (failure : IM α).run = some r) : False := by
  simp at h

/-- A `pure` step in a `do` block. -/
theorem IM.pure_bind_some {α β} {a : α} {f : α → IM β} {r} (h : ((pure a : IM α) >>= f).run = some r) :
    (f a).run = some r := by
  rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨b, hb, h⟩
  · cases (IM.pure_some hd)
  · cases (IM.pure_some hb); exact h

/-- A `throw` inside a `do` block ends it. -/
theorem IM.throw_bind_some {α β} {d : ByteArray} {f : α → IM β} {r} (h : ((throw d : IM α) >>= f).run = some r) :
    r = .error d := by
  rcases IM.bind_some h with ⟨d', hd, rfl⟩ | ⟨b, hb, _⟩
  · cases (IM.throw_some hd); rfl
  · cases (IM.throw_some hb)

theorem liftOp_some {α} {x : Op α} {r} (h : (Interp.liftOp x).run = some r) :
    (∃ p, x = some (.error p) ∧ r = .error p.data) ∨ (∃ a, x = some (.ok a) ∧ r = .ok a) := by
  rcases x with _ | (p | a)
  · simp at h
  · exact Or.inl ⟨p, rfl, (Option.some.inj h).symm⟩
  · exact Or.inr ⟨a, rfl, (Option.some.inj h).symm⟩

theorem liftOpt_some {α} {x : Option α} {r} (h : (Interp.liftOpt x).run = some r) :
    ∃ a, x = some a ∧ r = .ok a := by
  rcases x with _ | a
  · simp at h
  · exact ⟨a, rfl, (Option.some.inj h).symm⟩

theorem guard'_some {b : Bool} {r} (h : (Interp.guard' b).run = some r) : b = true ∧ r = .ok () := by
  cases b
  · simp at h
  · exact ⟨rfl, (Option.some.inj h).symm⟩

end Solidity

namespace Solidity

theorem liftOpt_ok {α} {x : Option α} {a : α} (h : (Interp.liftOpt x).run = some (.ok a)) : x = some a := by
  obtain ⟨b, hb, hr⟩ := liftOpt_some h
  cases hr; exact hb

theorem liftOpt_error {α} {x : Option α} {d : ByteArray} (h : (Interp.liftOpt x).run = some (.error d)) : False := by
  obtain ⟨_, _, hr⟩ := liftOpt_some h
  cases hr

theorem liftOp_ok {α} {x : Op α} {a : α} (h : (Interp.liftOp x).run = some (.ok a)) : x = some (.ok a) := by
  rcases liftOp_some h with ⟨_, _, hr⟩ | ⟨b, hb, hr⟩
  · cases hr
  · cases hr; exact hb

theorem liftOp_error {α} {x : Op α} {d : ByteArray} (h : (Interp.liftOp x).run = some (.error d)) :
    ∃ p, x = some (.error p) ∧ d = p.data := by
  rcases liftOp_some h with ⟨p, hp, hr⟩ | ⟨_, _, hr⟩
  · cases hr; exact ⟨p, hp, rfl⟩
  · cases hr

theorem guard'_ok {b : Bool} {u : Unit} (h : (Interp.guard' b).run = some (.ok u)) : b = true :=
  (guard'_some h).1

theorem guard'_error {b : Bool} {d : ByteArray} (h : (Interp.guard' b).run = some (.error d)) : False := by
  obtain ⟨_, hr⟩ := guard'_some h
  cases hr

end Solidity
