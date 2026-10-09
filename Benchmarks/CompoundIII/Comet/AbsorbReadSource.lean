import Benchmarks.CompoundIII.Comet.AbsorbReadModel
import Benchmarks.CompoundIII.Comet.UserBasicRead
import Benchmarks.CompoundIII.Comet.UserBasicLocal
import Benchmarks.CompoundIII.Comet.SignedPresentValueSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

theorem absorbRead_source (frame : Frame) (evm : State) (account : AccountAddress)
    (hc : frame.contract = contract) (ha : frame.locals.get? "account" = some (.address account))
    (hu : frame.locals.get? "userBasic" = none) :
    ExecBlock config frame evm absorbReadBlock (.ok (absorbOldPrincipalFrame frame evm account) evm) := by
  have hr : evalExpr? config frame evm (.storage ⟨"userBasic", [.mindex (.var "account")]⟩) =
      .ok (userBasicValue (absorbBasic evm account)) := by
    rw [absorbBasic, userBasicValue_normalized]
    exact evalUserBasic frame evm account (.var "account") hc hu
      (by simp only [evalExpr?, ha, EvalResult.ofOption])
  apply ExecBlock.consNormal (ExecStmt.letDecl hr)
  apply ExecBlock.consNormal (ExecStmt.letDecl (evalBasicPrincipal ?_)) .nil
  simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
    EvalResult.ofOption]
  rfl

theorem absorbPresent_source (frame : Frame) (evm : State) (account : AccountAddress)
    (hc : frame.contract = contract) :
    ExecStmt config (absorbOldPrincipalFrame frame evm account) evm
      (.internalCall "presentValue" [.var "oldPrincipal"] "oldBalance")
      (if -(2^103 : Int) < signed104 (absorbBasic evm account).principal then
        .ok (absorbPresentFrame frame evm account) evm else .reverted) := by
  have hr := signedPresent_call (absorbOldPrincipalFrame frame evm account) evm
    (absorbBasic evm account).principal (.var "oldPrincipal") "oldBalance" hc
    (by simp only [evalExpr?, absorbOldPrincipalFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl)
  by_cases hm : -(2^103 : Int) < signed104 (absorbBasic evm account).principal
  · simpa only [if_pos hm, absorbPresentFrame, absorbOldBalance,
      signedPresentValueWord_int evm _ hm] using hr
  · simpa only [if_neg hm] using hr

theorem absorbBits_source (frame : Frame) (evm : State) (account : AccountAddress) :
    ExecBlock config (absorbPresentFrame frame evm account) evm absorbBitsBlock
      (.ok (absorbBitsFrame frame evm account) evm) := by
  have ha := evalBasicAssets (cfg := config) (frame := absorbPresentFrame frame evm account)
    (evm := evm) (expr := .var "accountUser") (basic := absorbBasic evm account) (by
      simp only [evalExpr?, absorbPresentFrame, absorbOldPrincipalFrame, absorbReadFrame,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
      rfl)
  have hr := evalBasicReserved (cfg := config)
    (frame := { absorbPresentFrame frame evm account with
      locals := (absorbPresentFrame frame evm account).locals.insert "assetsIn"
        (.int (absorbBasic evm account).assets.toNat) })
    (evm := evm) (expr := .var "accountUser") (basic := absorbBasic evm account) (by
    simp only [evalExpr?, absorbPresentFrame, absorbOldPrincipalFrame, absorbReadFrame,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl)
  exact ExecBlock.consNormal (ExecStmt.letDecl ha)
    (ExecBlock.consNormal (ExecStmt.letDecl hr) .nil)

end Benchmarks.CompoundIII.Comet
