import Benchmarks.UniswapV3.Pool.UpdatePositionPositionTrace
import Benchmarks.UniswapV3.Pool.UpdatePositionTailTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def updatePositionFeeInputMemory (mem : ByteArray) (p : UInt256) (v : UniswapV3PoolImmutables)
    (a : UpdatePositionArgs) (evm : EVM.State) : ByteArray :=
  updatePositionChangedMemory (updatePositionPrefixMemory a mem p) (p + ⟨58⟩) v a evm

def updatePositionFeeFree (p : UInt256) (a : UpdatePositionArgs) (evm : EVM.State) : UInt256 :=
  updatePositionChangedFree (p + ⟨58⟩) a evm

def updatePositionMemory (mem : ByteArray) (p : UInt256) (v : UniswapV3PoolImmutables)
    (a : UpdatePositionArgs) (evm : EVM.State) : ByteArray :=
  updatePositionTailMemory
    (updatePositionPositionMemory
      (tickFeeMemory (updatePositionFeeInputMemory mem p v a evm) (updatePositionFeeArgs a evm))
      (updatePositionFeeFree p a evm) v a evm) v a evm

def updatePositionFree (p : UInt256) (a : UpdatePositionArgs) (evm : EVM.State) : UInt256 :=
  updatePositionFeeFree p a evm + ⟨160⟩

theorem updatePositionFeeFree_bound (p : UInt256) (a : UpdatePositionArgs) (evm : EVM.State)
    (hb : p.toNat + 442 ≤ 2 ^ 200) :
    (updatePositionFeeFree p a evm).toNat ≤ p.toNat + 442 := by
  have h1 : (p + (⟨58⟩ : UInt256)).toNat = p.toNat + 58 :=
    uadd_word_ofNat_toNat p 58 (by change _ < 2 ^ 256; omega)
  have h2 := updatePositionChangedFree_bound (p + ⟨58⟩) a evm (by rw [h1]; omega)
  rw [h1] at h2
  exact h2

theorem updatePositionFree_bound (p : UInt256) (a : UpdatePositionArgs) (evm : EVM.State)
    (hb : p.toNat + 602 ≤ 2 ^ 200) :
    (updatePositionFree p a evm).toNat ≤ p.toNat + 602 := by
  have h1 := updatePositionFeeFree_bound p a evm (by omega)
  have h2 : (updatePositionFeeFree p a evm + (⟨160⟩ : UInt256)).toNat =
      (updatePositionFeeFree p a evm).toNat + 160 :=
    uadd_word_ofNat_toNat _ 160 (by change _ < 2 ^ 256; omega)
  unfold updatePositionFree
  rw [h2]
  omega

end Benchmarks.UniswapV3.Pool
