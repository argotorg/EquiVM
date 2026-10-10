import Benchmarks.UniswapV3.Pool.Routines
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_034

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def blockTimestampFunction : FunctionDecl := contract.functions[3]!

theorem blockTimestampLookup :
    lookupCallable? contract "_blockTimestamp" = some blockTimestampFunction.toCallable := rfl

def blockTimestampWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.ofNat I.header.timestamp) (UInt256.ofNat (2 ^ 32 - 1))

theorem blockTimestampWord_lt (I : ExecutionEnv) : (blockTimestampWord I).toNat < 2 ^ 32 :=
  u256LandMaskToNatLtOfToNat _ _ (by decide)

theorem blockTimestampReturns (imms : Store) (evm : EVM.State) :
    ExecFuncBody config {contract := contract, locals := ∅, immutables := imms} evm
      blockTimestampFunction.body
      (.returned {contract := contract, locals := ∅, immutables := imms} evm
        (some [.int (Int.ofNat (blockTimestampWord evm.executionEnv).toNat)])) := by
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp only [evalExprs?, evalExpr?, envValue, bind, EvalResult.bind, pure, castValue?]
  rw [normalizeUIntWord_mask ⟨32, by decide⟩ _ (UInt256.ofNat (2 ^ 32 - 1)) (by decide)]
  rfl

theorem blockTimestampX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨11303⟩ (ret :: R) mem aw rdata σ k C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 2 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (UInt256.ofNat ee.header.timestamp :: R) mem aw rdata σ k' C' :=
  ⟨_, _, uniswapV3Pool_block_11303 (immWords := wordsOf (immStore v)) hov hret rd⟩

end Benchmarks.UniswapV3.Pool
