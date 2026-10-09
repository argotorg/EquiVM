import Benchmarks.Safe.SetupCalldata
import Benchmarks.Safe.SetupOwnersTrace
import Benchmarks.Safe.SetupModulesTrace
import Benchmarks.Safe.InternalSetFallbackHandler
import Benchmarks.Safe.PaymentTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def SetupInput.ownersInput (p : SetupInput) : SetupOwnersInput := ⟨p.owners, p.threshold⟩

def SetupInput.modulesInput (p : SetupInput) : SetupModulesInput := ⟨p.target, p.payload⟩

def SetupInput.paymentInput (p : SetupInput) : PaymentInput :=
  ⟨p.payment, ⟨0⟩, ⟨1⟩, AccountAddress.ofNat p.paymentToken.toNat,
    AccountAddress.ofNat p.paymentReceiver.toNat⟩

structure SetupLocals (p : SetupInput) (locals : Store) : Prop where
  owners : locals["_owners"]? = some (.array (p.owners.map addressArrayValue))
  threshold : locals["_threshold"]? = some (uint256Value p.threshold)
  target : locals["to"]? = some (addressArrayValue p.target)
  payload : locals["data"]? = some (.bytes p.payload)
  fallbackHandler : locals["fallbackHandler"]? = some (addressArrayValue p.fallbackHandler)
  paymentToken : locals["paymentToken"]? = some (addressArrayValue p.paymentToken)
  payment : locals["payment"]? = some (uint256Value p.payment)
  paymentReceiver : locals["paymentReceiver"]? = some (addressArrayValue p.paymentReceiver)

theorem SetupLocals.initial (p : SetupInput) : SetupLocals p p.args := by
  constructor <;> simp [SetupInput.args, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]

theorem SetupLocals.set {p locals} (h : SetupLocals p locals) (name : Ident) (value : Value)
    (hn : name ∉ setupNames) : SetupLocals p (locals.insert name value) := by
  simp only [setupNames, List.mem_cons, List.mem_singleton, not_or] at hn
  constructor <;> simp [Std.HashMap.getElem?_insert, hn, h.owners, h.threshold, h.target,
    h.payload, h.fallbackHandler, h.paymentToken, h.payment, h.paymentReceiver]

theorem safeInternalSetupFallback {caller : Frame} {evm : EVM.State} {expr : Expr}
    {handler : UInt256} {retVar : Ident} {result : ExecResult}
    (hc : caller.contract = contract) (him : caller.immutables = ∅)
    (he : evalExpr? config caller evm expr = .ok (addressArrayValue handler))
    (hb : ExecFuncBody config (fallbackHandlerFrame handler) evm
      internalSetFallbackHandlerFunction.body result) :
    ExecStmt config caller evm (.internalCall "internalSetFallbackHandler" [expr] retVar)
      (internalCallResult caller retVar result) := by
  apply internalCallFunctionResult (callee := internalSetFallbackHandlerFunction)
    (locals := fallbackHandlerArgs handler) (evalExprs?_singleton he)
  · rw [hc]; rfl
  · rfl
  · simpa only [hc, him] using hb

theorem safeSetupFallbackCondition (evm : EVM.State) {p locals}
    (hl : SetupLocals p locals) (hc : p.fallbackHandler.toNat < EVM.addressModulus) :
    evalExpr? config { contract := contract, locals := locals } evm
      (neE (.var "fallbackHandler") zeroAddr) =
      .ok (.bool (decide (p.fallbackHandler ≠ ⟨0⟩))) :=
  evalAddressNonzero hc (evalLocalValue hl.fallbackHandler)

theorem safeSetupPaymentCondition (evm : EVM.State) {p locals} (hl : SetupLocals p locals) :
    evalExpr? config { contract := contract, locals := locals } evm
      (gtE (.var "payment") (.intLit 0)) = .ok (.bool (decide (p.payment ≠ ⟨0⟩))) := by
  rw [gtE, evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue hl.payment]
  simp only [evalExpr?, uint256Value, EvalResult.bind, bind, pure, evalBinaryOp?]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  have hz : p.payment.toNat = 0 ↔ p.payment = ⟨0⟩ := by
    constructor
    · intro he; apply u256_inj; exact he
    · intro he; rw [he]; rfl
  simp only [Int.ofNat_eq_natCast]
  constructor
  · intro hp he
    have hh := hz.mpr he
    omega
  · intro hp
    have hh : p.payment.toNat ≠ 0 := fun he ↦ hp (hz.mp he)
    omega

end Benchmarks.Safe
