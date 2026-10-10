import Benchmarks.UniswapV3.Pool.SourceExpressions
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_034

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def noDelegateCallFunction : FunctionDecl := contract.functions[1]!

theorem noDelegateCallLookup :
    lookupCallable? contract "checkNotDelegateCall" = some noDelegateCallFunction.toCallable := rfl

def noDelegateCallFrame (v : UniswapV3PoolImmutables) : Frame :=
  { contract := contract, locals := ∅, immutables := immStore v }

theorem evalNoDelegateCall (v : UniswapV3PoolImmutables) (evm : EVM.State) :
    evalExpr? config (noDelegateCallFrame v) evm
      (.binary .eq (.env .this) (.immutable "original")) =
      .ok (.bool (decide (evm.executionEnv.codeOwner = v.original))) := by
  have hi := evalImmutable_original config contract ∅ evm v
  simp [evalExpr?, hi, bind, EvalResult.bind, pure, evalBinaryOp?, envValue, noDelegateCallFrame]
  apply Bool.eq_iff_iff.mpr
  simp

theorem noDelegateCallReturns (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (h : evm.executionEnv.codeOwner = v.original) :
    ExecFuncBody config (noDelegateCallFrame v) evm noDelegateCallFunction.body
      (.returned (noDelegateCallFrame v) evm none) := by
  apply ExecFuncBody.execBlockOK
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ExecBlock.nil
  simpa only [h, decide_true] using evalNoDelegateCall v evm

theorem noDelegateCallReverts (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (h : evm.executionEnv.codeOwner ≠ v.original) :
    ExecFuncBody config (noDelegateCallFrame v) evm noDelegateCallFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
  simpa only [h, decide_false] using evalNoDelegateCall v evm

theorem noDelegateCallX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨11248⟩ (ret :: R) mem aw rdata σ k C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 5 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ ee.codeOwner ≠ v.original) ∨
      (ee.codeOwner = v.original ∧
        ∃ k' C', RD (deployedRuntime v) ee g s0 ret R mem aw rdata σ k' C') := by
  have hclean : UInt256.land (wordsOf (immStore v) "original")
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) =
      EVM.word v.original.val := by
    rw [wordsOf_immStore_original]
    change UInt256.land (EVM.word v.original.val) solcAddrMask = _
    rw [← word_of_addressOfNat_eq_mask, accountAddress_of_word_val]
  by_cases heq : ee.codeOwner = v.original
  · have hr := uniswapV3Pool_block_11248_taken (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [hclean]; change UInt256.eq (EVM.word v.original.val) (EVM.word ee.codeOwner.val) ≠ ⟨0⟩
          rw [heq, uInt256_eq_self]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    exact Or.inr ⟨heq, _, _, uniswapV3Pool_block_11301 (immWords := wordsOf (immStore v)) (by evm_ov) hret hr⟩
  · have hne : EVM.word v.original.val ≠ EVM.word ee.codeOwner.val := by
      intro hw
      have ha := congrArg (fun w : UInt256 => AccountAddress.ofNat w.toNat) hw
      exact heq (by simpa only [accountAddress_of_word_val] using ha.symm)
    have hr := uniswapV3Pool_block_11248_fallthrough (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [hclean]; exact u256_eq_of_ne hne) rd
    exact Or.inl ⟨uniswapV3Pool_block_11297 (immWords := wordsOf (immStore v)) (by evm_ov) hr, heq⟩

end Benchmarks.UniswapV3.Pool
