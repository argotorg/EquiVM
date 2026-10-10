import Benchmarks.UniswapV3.Pool.FlashGrowthSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def flashUpdateStmt (second : Bool) : Stmt :=
  .ite (.binary .gt (.var (flashPaidName second)) (.intLit 0))
    (flashProtocolStmts second ++ flashGrowthStmts second) []

theorem flashUpdateStmt_eq (second : Bool) :
    flashUpdateStmt second = flashTransition.body[if second then 24 else 23]! := by
  cases second <;> rfl

theorem evalFlashUpdateGuard (locals imms : Store) (evm : EVM.State)
    (second : Bool) (paid : UInt256)
    (hp : locals.get? (flashPaidName second) = some (.int (Int.ofNat paid.toNat))) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.binary .gt (.var (flashPaidName second)) (.intLit 0)) =
      .ok (.bool (decide (0 < paid.toNat))) :=
  evalExpr_word_gt (a := paid) (b := ⟨0⟩) (evalExpr_var_get hp)
    (by simp only [evalExpr?, pure]; rfl)

theorem flashUpdateSkip (locals imms : Store) (evm : EVM.State) (second : Bool)
    (hp : locals.get? (flashPaidName second) = some (.int 0)) :
    ExecStmt config {contract := contract, locals := locals, immutables := imms} evm
      (flashUpdateStmt second) (.ok {contract := contract, locals := locals, immutables := imms} evm) := by
  refine ExecStmt.iteFalse ?_ ExecBlock.nil
  simpa only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.lt_irrefl, decide_false] using
    evalFlashUpdateGuard locals imms evm second ⟨0⟩ hp

def FlashUpdatePreserves (second : Bool) (before after : Store) : Prop :=
  ∀ name, name ≠ flashProtocolName second → name ≠ flashProtocolFeesName second →
    name ≠ flashGrowthCallName second → after.get? name = before.get? name

theorem flashUpdatePreserves_refl (second : Bool) (locals : Store) :
    FlashUpdatePreserves second locals locals := fun _ _ _ _ ↦ rfl

theorem flashUpdatePreserves_frames (locals imms : Store) (second : Bool)
    (paid divisor liquidity : UInt256) :
    FlashUpdatePreserves second locals
      (flashGrowthFrame (flashProtocolFrame locals imms second paid divisor).locals imms second
        paid (poolProtocolFees paid divisor) liquidity).locals := by
  intro name h0 h1 h2
  simp [flashGrowthFrame, flashProtocolFrame, Std.HashMap.getElem?_insert,
    Ne.symm h0, Ne.symm h1, Ne.symm h2]

end Benchmarks.UniswapV3.Pool
