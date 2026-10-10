import Benchmarks.UniswapV3.Pool.MintAmountsSource
import Benchmarks.UniswapV3.Pool.BalanceCaller
import Benchmarks.UniswapV3.Pool.FlashTransferSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def mintBalancesInitFrame (v : UniswapV3PoolImmutables) (a : MintArgs) (a0 a1 : Int) : Frame :=
  let frame := mintAmountsFrame v a a0 a1
  {frame with locals := (frame.locals.insert "balance0Before" (.int 0)).insert "balance1Before" (.int 0)}

theorem mintBalancesInitSource (v : UniswapV3PoolImmutables) (a : MintArgs)
    (a0 a1 : Int) (evm : EVM.State) :
    ExecBlock config (mintAmountsFrame v a a0 a1) evm (mintTransition.body.drop 12 |>.take 2)
      (.ok (mintBalancesInitFrame v a a0 a1) evm) := by
  unfold mintBalancesInitFrame
  generalize mintAmountsFrame v a a0 a1 = frame
  refine ExecBlock.consNormal
    (solm' := {frame with locals := frame.locals.insert "balance0Before" (.int 0)}) (evm' := evm)
    (ExecStmt.letDecl (name := "balance0Before") (value := .int 0)
      (by simp only [evalExpr?, pure])) ?_
  exact ExecBlock.consNormal (ExecStmt.letDecl (name := "balance1Before") (value := .int 0)
    (by simp only [evalExpr?, pure])) ExecBlock.nil

def mintBeforeBalanceName (second : Bool) : Ident :=
  if second then "balance1Before" else "balance0Before"

def mintBeforeBalanceTemp (second : Bool) : Ident := if second then "__c3" else "__c2"

def mintBeforeBalanceStmt (second : Bool) : Stmt :=
  .ite (.binary .gt (.var (poolAmountName second)) (.intLit 0))
    [.internalCall (if second then "balance1" else "balance0") [] (mintBeforeBalanceTemp second),
      .assign .localVar ⟨mintBeforeBalanceName second, []⟩ (.var (mintBeforeBalanceTemp second))] []

theorem mintBeforeBalanceStmt_eq (second : Bool) :
    mintBeforeBalanceStmt second = mintTransition.body[if second then 15 else 14]! := by
  cases second <;> rfl

def mintBeforeBalanceLocals (locals : Store) (second : Bool) (amount balance : UInt256) : Store :=
  if amount = ⟨0⟩ then locals else
    (locals.insert (mintBeforeBalanceTemp second) (.int (Int.ofNat balance.toNat))).insert
      (mintBeforeBalanceName second) (.int (Int.ofNat balance.toNat))

def mintBeforeBalanceFrame (v : UniswapV3PoolImmutables) (locals : Store)
    (second : Bool) (amount balance : UInt256) : Frame :=
  {contract := contract, locals := mintBeforeBalanceLocals locals second amount balance,
    immutables := immStore v}

theorem mintBeforeBalanceSkip (v : UniswapV3PoolImmutables) (locals : Store)
    (evm : EVM.State) (second : Bool)
    (ha : locals.get? (poolAmountName second) = some (.int 0)) :
    ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
      (mintBeforeBalanceStmt second) (.ok (mintBeforeBalanceFrame v locals second ⟨0⟩ ⟨0⟩) evm) := by
  refine ExecStmt.iteFalse ?_ ExecBlock.nil
  simpa only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.lt_irrefl, decide_false] using
    evalFlashTransferGuard v locals evm second ⟨0⟩ ha

theorem mintBeforeBalanceReturns (v : UniswapV3PoolImmutables) (locals : Store)
    (evm evm' : EVM.State) (second : Bool) (amount balance : UInt256) (calleeFrame : Frame)
    (ha : locals.get? (poolAmountName second) = some (.int (Int.ofNat amount.toNat)))
    (hb : locals.get? (mintBeforeBalanceName second) = some (.int 0))
    (hp : 0 < amount.toNat)
    (hcall : ExecFuncBody config {contract := contract, locals := ∅, immutables := immStore v} evm
      (balanceFunction second).body
      (.returned calleeFrame evm' (some [.int (Int.ofNat balance.toNat)]))) :
    ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
      (mintBeforeBalanceStmt second)
      (.ok (mintBeforeBalanceFrame v locals second amount balance) evm') := by
  have hz : amount ≠ ⟨0⟩ := by intro h; subst amount; cases hp
  have hn : mintBeforeBalanceTemp second ≠ mintBeforeBalanceName second := by
    cases second <;> decide
  simp only [mintBeforeBalanceFrame, mintBeforeBalanceLocals, if_neg hz]
  refine ExecStmt.iteTrue ?_ (ExecBlock.consNormal
    (poolBalanceReturns v locals (mintBeforeBalanceTemp second) evm evm' second balance
      calleeFrame hcall) (ExecBlock.consNormal
        (ExecStmt.assign (value := .int (Int.ofNat balance.toNat)) ?_ ?_) ExecBlock.nil))
  · simpa only [hp, decide_true] using evalFlashTransferGuard v locals evm second amount ha
  · exact evalExpr_var_get (by simp)
  · apply assignLocalVarBase_frame (old := .int 0)
    simpa [Std.HashMap.getElem?_insert, hn] using hb

theorem mintBeforeBalanceReverts (v : UniswapV3PoolImmutables) (locals : Store)
    (evm : EVM.State) (second : Bool) (amount : UInt256)
    (ha : locals.get? (poolAmountName second) = some (.int (Int.ofNat amount.toNat)))
    (hp : 0 < amount.toNat)
    (hcall : ExecFuncBody config {contract := contract, locals := ∅, immutables := immStore v} evm
      (balanceFunction second).body .reverted) :
    ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
      (mintBeforeBalanceStmt second) .reverted := by
  refine ExecStmt.iteTrue ?_ (ExecBlock.consRevert
    (poolBalanceReverts v locals (mintBeforeBalanceTemp second) evm second hcall))
  simpa only [hp, decide_true] using evalFlashTransferGuard v locals evm second amount ha

end Benchmarks.UniswapV3.Pool
