import Benchmarks.CurveVault.MutationSites
import Reasoning.ExternalCall
import Reasoning.SteleArithmetic

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

abbrev vaultDebitFunction (isWithdraw : Bool) : FunctionDecl :=
  if isWithdraw then contract.functions[16]! else contract.functions[19]!

def vaultDebitFlow (isWithdraw : Bool) : VaultFlow := if isWithdraw then .withdraw else .redeem
def vaultDebitResult (isWithdraw : Bool) (assets shares : UInt256) : UInt256 := if isWithdraw then shares else assets
def vaultDebitInput (isWithdraw : Bool) (assets shares : UInt256) : UInt256 := if isWithdraw then assets else shares
def vaultDebitAssetsName (isWithdraw : Bool) : Ident := if isWithdraw then "_assets" else "assets_to_redeem"
def vaultDebitSharesName (isWithdraw : Bool) : Ident := if isWithdraw then "shares" else "_shares"
def vaultDebitResultName (isWithdraw : Bool) : Ident := if isWithdraw then "shares" else "assets_to_redeem"

def vaultDebitReturnBody (isWithdraw : Bool) : List Stmt :=
  [.emit "Withdraw" [.env .caller, .var "_receiver", .var "_owner", .var (vaultDebitAssetsName isWithdraw),
      .var (vaultDebitSharesName isWithdraw)],
    .return [.var (vaultDebitResultName isWithdraw)]]

def vaultDebitFinishBody (isWithdraw : Bool) : List Stmt :=
  [.require (.binary .gt (.extCodeSize (.var "controller")) (.intLit 0)),
    .externalCall (.var "controller") "save_rate" (.intLit 0) [] "__c4"] ++
    vaultDebitReturnBody isWithdraw

theorem vaultDebitReturnSource (isWithdraw : Bool) {s0 evm : State} {I : ExecutionEnv} {σ : AccountMap}
    {locals : Store} {receiver owner assets shares : UInt256}
    (hs : SourceState s0 I σ evm)
    (hr : locals.get? "_receiver" = some (.address (AccountAddress.ofNat receiver.toNat)))
    (ho : locals.get? "_owner" = some (.address (AccountAddress.ofNat owner.toNat)))
    (ha : locals.get? (vaultDebitAssetsName isWithdraw) = some (.int (Int.ofNat assets.toNat)))
    (hv : locals.get? (vaultDebitSharesName isWithdraw) = some (.int (Int.ofNat shares.toNat)))
    (hperm : I.perm = true) :
    ExecBlock fork config {contract := contract, locals := locals} evm (vaultDebitReturnBody isWithdraw)
      (.returned {contract := contract, locals := locals} evm
        (some [.int (Int.ofNat (vaultDebitResult isWithdraw assets shares).toNat)])) := by
  have hresult : locals.get? (vaultDebitResultName isWithdraw) =
      some (.int (Int.ofNat (vaultDebitResult isWithdraw assets shares).toNat)) := by
    cases isWithdraw
    · exact ha
    · exact hv
  exact ExecBlock.consNormal (ExecStmt.emit (fork := fork) (hperm := by simpa only [hs.env] using hperm) (by
    simp only [evalExprs?, evalExpr?, envValue, hs.env, hr, ho, ha, hv, EvalResult.ofOption,
      EvalResult.bind, bind, pure]
    rfl)) (ExecBlock.consReturn (ExecStmt.return (by
    simp only [evalExprs?, evalExpr?, hresult, EvalResult.ofOption, EvalResult.bind, bind, pure])))

end Benchmarks.CurveVault
