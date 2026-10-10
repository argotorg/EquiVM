import Benchmarks.UniswapV3.Pool.SourceWordArithmetic
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_044
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_051

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def safeAddFunction : FunctionDecl := contract.functions[13]!

theorem safeAddLookup :
    lookupCallable? contract "LowGasSafeMath_add" = some safeAddFunction.toCallable := rfl

def safeAddLocals (x y : UInt256) : Store :=
  ((∅ : Store).insert "y" (.int (Int.ofNat y.toNat))).insert "x" (.int (Int.ofNat x.toNat))

def safeAddFrame (imms : Store) (x y : UInt256) : Frame :=
  {contract := contract, locals := safeAddLocals x y, immutables := imms}

theorem safeAddBind (x y : UInt256) :
    bindParams? safeAddFunction.params [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)] =
      some (safeAddLocals x y) := rfl

def safeAddZeroFrame (imms : Store) (x y : UInt256) : Frame :=
  {safeAddFrame imms x y with locals := (safeAddLocals x y).insert "z" (.int 0)}

def safeAddResultFrame (imms : Store) (x y : UInt256) : Frame :=
  {safeAddZeroFrame imms x y with
    locals := (safeAddZeroFrame imms x y).locals.insert "z" (.int (Int.ofNat (x + y).toNat))}

theorem safeAddPrefix (imms : Store) (evm : EVM.State) (x y : UInt256) :
    ExecBlock config (safeAddFrame imms x y) evm (safeAddFunction.body.take 2)
      (.ok (safeAddResultFrame imms x y) evm) := by
  refine ExecBlock.consNormal (solm' := safeAddZeroFrame imms x y) (evm' := evm)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (value := .int (Int.ofNat (x + y).toNat)) ?_ ?_)
    ExecBlock.nil
  · apply evalExpr_word_add
    · exact evalExpr_var_get (by simp [safeAddZeroFrame, safeAddLocals, Std.HashMap.getElem_insert])
    · exact evalExpr_var_get (by simp [safeAddZeroFrame, safeAddLocals, Std.HashMap.getElem_insert])
  · have hs := assignLocalVarBase_frame (cfg := config) (evm := evm)
      (frame := safeAddZeroFrame imms x y) (name := "z") (old := .int 0)
      (value := .int (Int.ofNat (x + y).toNat)) (by simp [safeAddZeroFrame])
    exact hs

theorem evalSafeAddGuard (imms : Store) (evm : EVM.State) (x y : UInt256) :
    evalExpr? config (safeAddResultFrame imms x y) evm
      (.binary .ge (.var "z") (.var "x")) =
      .ok (.bool (decide (x.toNat ≤ (x + y).toNat))) := by
  simp [evalExpr?, safeAddResultFrame, safeAddZeroFrame, safeAddFrame, safeAddLocals,
    Std.HashMap.getElem_insert, EvalResult.ofOption, evalBinaryOp?, bind, EvalResult.bind]

theorem safeAddReturns (imms : Store) (evm : EVM.State) (x y : UInt256)
    (h : x.toNat ≤ (x + y).toNat) :
    ExecFuncBody config (safeAddFrame imms x y) evm safeAddFunction.body
      (.returned (safeAddResultFrame imms x y) evm (some [.int (Int.ofNat (x + y).toNat)])) := by
  apply ExecFuncBody.execBlockRet
  rw [← List.take_append_drop 2 safeAddFunction.body]
  apply execBlock_append_ok (safeAddPrefix imms evm x y)
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [h, decide_true] using evalSafeAddGuard imms evm x y
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp [evalExprs?, evalExpr?, safeAddResultFrame, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem safeAddReverts (imms : Store) (evm : EVM.State) (x y : UInt256)
    (h : ¬ x.toNat ≤ (x + y).toNat) :
    ExecFuncBody config (safeAddFrame imms x y) evm safeAddFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 2 safeAddFunction.body]
  apply execBlock_append_ok (safeAddPrefix imms evm x y)
  apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
  simpa only [h, decide_false] using evalSafeAddGuard imms evm x y

theorem safeAddX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret x y : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨15885⟩ (y :: x :: ret :: R) mem aw rdata σ k C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 6 ≤ 1024) :
    (¬ x.toNat ≤ (x + y).toNat ∧ RDrev (deployedRuntime v) g s0) ∨
    (x.toNat ≤ (x + y).toNat ∧ ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) ee g s0 ret
      ((x + y) :: R) mem aw rdata σ k' C') := by
  by_cases h : x.toNat ≤ (x + y).toNat
  · have r1 := uniswapV3Pool_block_15885_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [ult_zero h]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have r2 := uniswapV3Pool_block_12989 (immWords := wordsOf (immStore v)) (by evm_ov) hret r1
    exact Or.inr ⟨h, k + 10 + 6, C + 35 + 19, by omega, r2⟩
  · have r1 := uniswapV3Pool_block_15885_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [ult_one (Nat.lt_of_not_ge h)]; rfl) rd
    simp only [uniswapV3Pool_block_15885_fallthrough_stack] at r1
    exact Or.inl ⟨h, uniswapV3Pool_block_15897 (immWords := wordsOf (immStore v)) (by evm_ov) r1⟩

end Benchmarks.UniswapV3.Pool
