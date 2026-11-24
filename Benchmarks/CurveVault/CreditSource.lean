import Benchmarks.CurveVault.CreditMemory
import Reasoning.ExternalCall
import Reasoning.SteleArithmetic

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

abbrev vaultCreditFunction (isDeposit : Bool) : FunctionDecl :=
  if isDeposit then contract.functions[10]! else contract.functions[13]!

def vaultCreditAssetsName (isDeposit : Bool) : Ident := if isDeposit then "_assets" else "assets"
def vaultCreditSharesName (isDeposit : Bool) : Ident := if isDeposit then "to_mint" else "_shares"
def vaultCreditResultName (isDeposit : Bool) : Ident := if isDeposit then "to_mint" else "assets"

def vaultCreditReturnBody (isDeposit : Bool) : List Stmt :=
  [.emit "Deposit" [.env .caller, .var "_receiver", .var (vaultCreditAssetsName isDeposit),
      .var (vaultCreditSharesName isDeposit)],
    .return [.var (vaultCreditResultName isDeposit)]]

def vaultCreditFinishBody (isDeposit : Bool) : List Stmt :=
  [.internalCall "_mint" [.var "_receiver", .var (vaultCreditSharesName isDeposit)] "__c2",
    .require (.binary .gt (.extCodeSize (.var "controller")) (.intLit 0)),
    .externalCall (.var "controller") "save_rate" (.intLit 0) [] "__c3"] ++
    vaultCreditReturnBody isDeposit

theorem vaultCreditFinishBody_eq (isDeposit : Bool) :
    (vaultCreditFunction isDeposit).body.drop 11 = vaultCreditFinishBody isDeposit := by
  cases isDeposit <;> rfl

theorem vaultCreditReturnSource (isDeposit : Bool) {s0 evm : State} {I : ExecutionEnv} {σ : AccountMap}
    {locals : Store} {receiver assets shares : UInt256}
    (hs : SourceState s0 I σ evm)
    (hr : locals.get? "_receiver" = some (.address (AccountAddress.ofNat receiver.toNat)))
    (ha : locals.get? (vaultCreditAssetsName isDeposit) = some (.int (Int.ofNat assets.toNat)))
    (hv : locals.get? (vaultCreditSharesName isDeposit) = some (.int (Int.ofNat shares.toNat)))
    (hperm : I.perm = true) :
    ExecBlock fork config {contract := contract, locals := locals} evm (vaultCreditReturnBody isDeposit)
      (.returned {contract := contract, locals := locals} evm
        (some [.int (Int.ofNat (vaultCreditResult isDeposit assets shares).toNat)])) := by
  have hresult : locals.get? (vaultCreditResultName isDeposit) =
      some (.int (Int.ofNat (vaultCreditResult isDeposit assets shares).toNat)) := by
    cases isDeposit
    · exact ha
    · exact hv
  exact ExecBlock.consNormal (ExecStmt.emit (fork := fork) (hperm := by simpa only [hs.env] using hperm) (by
    simp only [evalExprs?, evalExpr?, envValue, hs.env, hr, ha, hv, EvalResult.ofOption,
      EvalResult.bind, bind, pure]
    rfl)) (ExecBlock.consReturn (ExecStmt.return (by
    simp only [evalExprs?, evalExpr?, hresult, EvalResult.ofOption, EvalResult.bind, bind, pure])))

end Benchmarks.CurveVault
