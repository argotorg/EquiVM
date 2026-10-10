import Benchmarks.UniswapV4PoolManager.CallCostTrace
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: retain the concrete gas witnesses for an opaque zero-value CALL.
structure ZeroCallGasEvidence (evm : EVM.State) (target : AccountAddress) (data : ByteArray)
    (evm' : EVM.State) (z : Bool) (out : ByteArray) where
  inputGas : UInt256
  returnedGas : UInt256
  inputSubstate : Substate
  theta : (evm'.accountMap, returnedGas, evm'.substate, z, out) =
    Ethereum.EVM.Θ evm.accountMap evm.σ₀ inputSubstate evm.executionEnv.codeOwner evm.executionEnv.sender
      target (toExecute evm.accountMap target) inputGas (UInt256.ofNat evm.executionEnv.gasPrice)
      ⟨0⟩ ⟨0⟩ data (evm.executionEnv.depth+1) evm.executionEnv.header
      evm.executionEnv.blobVersionedHashes evm.executionEnv.blocks evm.executionEnv.perm

def ZeroCallGasEvidence.spent {evm evm' target data z out}
    (w : ZeroCallGasEvidence evm target data evm' z out) : Nat := w.inputGas.toNat-w.returnedGas.toNat

theorem ZeroCallGasEvidence.returned_le {evm evm' target data z out}
    (w : ZeroCallGasEvidence evm target data evm' z out) : w.returnedGas.toNat ≤ w.inputGas.toNat := by
  have h := congrArg (fun p => p.2.1.toNat) w.theta
  dsimp only at h
  rw [h]
  exact Theta_returnedGas_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

end Benchmarks.UniswapV4PoolManager
