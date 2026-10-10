import Benchmarks.UniswapV3.Pool.PoolLiquidityStorage
import Benchmarks.UniswapV3.Pool.TickLiquidityStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def storePoolLiquidity (evm : EVM.State) (word : UInt256) : EVM.State :=
  EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩
    (protocolFeeUpdateWord false (EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩) word)

theorem assignPoolLiquidity (locals imms : Store) (evm : EVM.State) (value : Int)
    (hbase : locals.get? "liquidity" = none) :
    assignStorageRef? config {contract := contract, locals := locals, immutables := imms} evm .storage
      ⟨"liquidity", []⟩ (.int value) =
      .ok ({contract := contract, locals := locals, immutables := imms},
        storePoolLiquidity evm (EVM.wordOfInt value)) := by
  apply assignStorageRef_storage_scalar_value (ty := .elem (.int (.uint ⟨128, by decide⟩)))
    (er := ⟨"liquidity", []⟩)
    (loc := {slot := ⟨4⟩, offset := 0, size := 16, type := .int (.uint ⟨128, by decide⟩), hbound := by decide}) hbase
    (by simp only [evalStorageRef, evalStorageRefSteps, bind, EvalResult.bind, pure])
    rfl poolStorageBackend_eq rfl (Or.inl ⟨_, rfl⟩)
  exact storageLocStore_pair128Value evm ⟨4⟩ false _ (.int value) (EVM.wordOfInt value) rfl

end Benchmarks.UniswapV3.Pool
