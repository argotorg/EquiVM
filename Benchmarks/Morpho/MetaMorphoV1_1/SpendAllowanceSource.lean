import Benchmarks.Morpho.MetaMorphoV1_1.AllowanceInternalSource
import Benchmarks.Morpho.MetaMorphoV1_1.ApprovalCalls
import Benchmarks.Morpho.MetaMorphoV1_1.BalanceMutation
import Benchmarks.Morpho.MetaMorphoV1_1.MarketBalancesSource

/-! Source execution of the allowance reader, guard, and finite allowance debit. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false
set_option maxRecDepth 2000

def spendAllowanceFunction : FunctionDecl := contract.functions[43]!

def unlimitedAllowance : UInt256 := UInt256.lnot ⟨0⟩

def spendAllowanceFrame (imms : Store) (owner spender : AccountAddress) (value : UInt256) :
    Frame := approveFrame imms owner spender value

def spendAllowanceReadFrame (imms : Store) (owner spender : AccountAddress)
    (value allowed : UInt256) : Frame :=
  { spendAllowanceFrame imms owner spender value with
    locals := (spendAllowanceFrame imms owner spender value).locals.insert "currentAllowance"
      (uint256Value allowed) }

def spendAllowanceArgs : List Expr :=
  [.var "owner", .var "spender", .cast (.binary .sub (.var "currentAllowance") (.var "value"))
    (.elem (.int (.uint ⟨256, by decide⟩))), .boolLit false]

def spendAllowanceFiniteBody : List Stmt :=
  [.require (.binary .ge (.var "currentAllowance") (.var "value")),
    .internalCall "_approve_address_address_uint256_bool" spendAllowanceArgs "__c1"]

def spendAllowanceTail : List Stmt :=
  [.ite (.binary .ne (.var "currentAllowance") (.intLit (Int.ofNat (UInt256.size - 1))))
    spendAllowanceFiniteBody []]

theorem spendAllowanceFunction_body :
    spendAllowanceFunction.body =
      [.internalCall "allowance_body" [.var "owner", .var "spender"] "currentAllowance"] ++
      spendAllowanceTail := by decide +kernel

theorem spendAllowanceRead (imms : Store) (evm : State)
    (owner spender : AccountAddress) (value : UInt256) :
    ABlock config evm (spendAllowanceFrame imms owner spender value) spendAllowanceFunction.body
      (spendAllowanceReadFrame imms owner spender value (allowanceWord evm owner spender))
      spendAllowanceTail := by
  rw [spendAllowanceFunction_body]
  refine ⟨fun h ↦ ExecBlock.consNormal (allowanceInternalCall ?_) h⟩
  simp [evalExprs?, evalExpr?, Std.HashMap.getElem_insert,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem spendAllowanceFiniteCondition (imms : Store) (evm : State)
    (owner spender : AccountAddress) (value allowed : UInt256) :
    evalExpr? config (spendAllowanceReadFrame imms owner spender value allowed) evm
      (.binary .ne (.var "currentAllowance") (.intLit (Int.ofNat (UInt256.size - 1)))) =
      .ok (.bool (decide (allowed ≠ unlimitedAllowance))) := by
  apply SourceMemory.wordNeSource
  · simp only [evalExpr?, spendAllowanceReadFrame, store_get_self, EvalResult.ofOption]
  · simp only [evalExpr?, uint256Value, unlimitedAllowance, u256_lnot_zero_toNat, pure]

theorem spendAllowanceEnough (imms : Store) (evm : State)
    (owner spender : AccountAddress) (value allowed : UInt256) :
    evalExpr? config (spendAllowanceReadFrame imms owner spender value allowed) evm
      (.binary .ge (.var "currentAllowance") (.var "value")) =
      .ok (.bool (decide (value.toNat ≤ allowed.toNat))) := by
  apply naturalGeSource
  · simp only [evalExpr?, spendAllowanceReadFrame, store_get_self, EvalResult.ofOption]
  · simp [evalExpr?, spendAllowanceReadFrame, spendAllowanceFrame, approveFrame,
      Std.HashMap.getElem_insert, EvalResult.ofOption]

theorem spendAllowanceArgsSource (imms : Store) (evm : State)
    (owner spender : AccountAddress) (value allowed : UInt256) :
    evalExprs? config (spendAllowanceReadFrame imms owner spender value allowed) evm
      spendAllowanceArgs =
      .ok [.address owner, .address spender, uint256Value (UInt256.sub allowed value),
        .bool false] := by
  have hsub := wrappingSubSource (cfg := config)
    (frame := spendAllowanceReadFrame imms owner spender value allowed) (evm := evm)
    (lhs := .var "currentAllowance") (rhs := .var "value") (a := allowed) (b := value)
    (by simp only [evalExpr?, spendAllowanceReadFrame, store_get_self, EvalResult.ofOption])
    (by simp [evalExpr?, spendAllowanceReadFrame, spendAllowanceFrame, approveFrame,
      Std.HashMap.getElem_insert, EvalResult.ofOption])
  simp only [spendAllowanceArgs, evalExprs?, hsub]
  simp [evalExpr?, spendAllowanceReadFrame,
    spendAllowanceFrame, approveFrame, Std.HashMap.getElem_insert,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem spendAllowanceUnlimitedBody (imms : Store) (evm : State)
    (owner spender : AccountAddress) (value : UInt256)
    (hmax : allowanceWord evm owner spender = unlimitedAllowance) :
    ExecFuncBody config (spendAllowanceFrame imms owner spender value) evm
      spendAllowanceFunction.body
      (.returned
        (spendAllowanceReadFrame imms owner spender value (allowanceWord evm owner spender))
        evm none) := by
  apply ExecFuncBody.execBlockOK
  apply (spendAllowanceRead imms evm owner spender value).run
  exact ExecBlock.consNormal (ExecStmt.iteFalse
    (by rw [spendAllowanceFiniteCondition, decide_eq_false (not_ne_iff.mpr hmax)]) ExecBlock.nil)
    ExecBlock.nil

theorem spendAllowanceFinitePrefix (imms : Store) (evm : State)
    (owner spender : AccountAddress) (value : UInt256)
    (hle : value.toNat ≤ (allowanceWord evm owner spender).toNat) :
    ABlock config evm
      (spendAllowanceReadFrame imms owner spender value (allowanceWord evm owner spender))
      spendAllowanceFiniteBody
      (spendAllowanceReadFrame imms owner spender value (allowanceWord evm owner spender))
      [.internalCall "_approve_address_address_uint256_bool" spendAllowanceArgs "__c1"] := by
  apply ABlock.requireStep ABlock.start
  rw [spendAllowanceEnough, decide_eq_true hle]

theorem spendAllowanceFiniteBodyReturns (imms : Store) (evm : State)
    (owner spender : AccountAddress) (value : UInt256)
    (hfinite : allowanceWord evm owner spender ≠ unlimitedAllowance)
    (hle : value.toNat ≤ (allowanceWord evm owner spender).toNat)
    (ho : owner ≠ ⟨0, by decide⟩) (hs : spender ≠ ⟨0, by decide⟩) :
    ExecFuncBody config (spendAllowanceFrame imms owner spender value) evm
      spendAllowanceFunction.body
      (.returned
        { spendAllowanceReadFrame imms owner spender value (allowanceWord evm owner spender) with
          locals := (spendAllowanceReadFrame imms owner spender value
            (allowanceWord evm owner spender)).locals.insert "__c1" .unit }
        (approvalState evm owner spender (UInt256.sub (allowanceWord evm owner spender) value))
        none) := by
  apply ExecFuncBody.execBlockOK
  apply (spendAllowanceRead imms evm owner spender value).run
  apply ExecBlock.consNormal (ExecStmt.iteTrue
    (by rw [spendAllowanceFiniteCondition, decide_eq_true hfinite]) ?_) ExecBlock.nil
  apply (spendAllowanceFinitePrefix imms evm owner spender value hle).run
  exact ExecBlock.consNormal (approvalCall
    (spendAllowanceArgsSource imms evm owner spender value _) ho hs) ExecBlock.nil

theorem spendAllowanceFiniteBodyReverts (imms : Store) (evm : State)
    (owner spender : AccountAddress) (value : UInt256)
    (hfinite : allowanceWord evm owner spender ≠ unlimitedAllowance)
    (hbad : ¬ (value.toNat ≤ (allowanceWord evm owner spender).toNat ∧
      owner ≠ ⟨0, by decide⟩ ∧ spender ≠ ⟨0, by decide⟩)) :
    ExecFuncBody config (spendAllowanceFrame imms owner spender value) evm
      spendAllowanceFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply (spendAllowanceRead imms evm owner spender value).run
  apply ExecBlock.consRevert (ExecStmt.iteTrue
    (by rw [spendAllowanceFiniteCondition, decide_eq_true hfinite]) ?_)
  by_cases hle : value.toNat ≤ (allowanceWord evm owner spender).toNat
  · apply (spendAllowanceFinitePrefix imms evm owner spender value hle).run
    exact ExecBlock.consRevert (approvalCallReverts
      (spendAllowanceArgsSource imms evm owner spender value _) (fun hg ↦ hbad ⟨hle, hg⟩))
  · exact ABlock.start.requireRevert (by rw [spendAllowanceEnough, decide_eq_false hle])

theorem spendAllowanceFiniteBodyStatic (imms : Store) (evm : State)
    (owner spender : AccountAddress) (value : UInt256)
    (hfinite : allowanceWord evm owner spender ≠ unlimitedAllowance)
    (hle : value.toNat ≤ (allowanceWord evm owner spender).toNat)
    (ho : owner ≠ ⟨0, by decide⟩) (hs : spender ≠ ⟨0, by decide⟩)
    (hperm : evm.executionEnv.perm = false) :
    ExecFuncBody config (spendAllowanceFrame imms owner spender value) evm
      spendAllowanceFunction.body .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  apply (spendAllowanceRead imms evm owner spender value).run
  apply ExecBlock.consStatic (ExecStmt.iteTrue
    (by rw [spendAllowanceFiniteCondition, decide_eq_true hfinite]) ?_)
  apply (spendAllowanceFinitePrefix imms evm owner spender value hle).run
  exact ExecBlock.consStatic (approvalCallStatic
    (spendAllowanceArgsSource imms evm owner spender value _) ho hs hperm)

end Benchmarks.Morpho.MetaMorphoV1_1
