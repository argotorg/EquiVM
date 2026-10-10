import Benchmarks.UniswapV3.Pool.UpdatePositionMemory
import Benchmarks.UniswapV3.Pool.HashMemoryPrefix
import Benchmarks.UniswapV3.Pool.OracleObserveZeroPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem updatePositionBitmapMemory_prefix (mem : ByteArray) (v : UniswapV3PoolImmutables)
    (a : UpdatePositionArgs) (evm : EVM.State) (upper : Bool) (limit : Nat) :
    MemoryPrefix mem (updatePositionBitmapMemory mem v a evm upper) limit := by
  unfold updatePositionBitmapMemory
  split_ifs <;> first | exact twoWordHashMem_prefix mem _ _ limit | exact .refl _ _

theorem updatePositionChangedMemory_prefix (mem : ByteArray) (p : UInt256)
    (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs) (evm : EVM.State)
    (hb : p.toNat + 384 ≤ 2 ^ 200) :
    MemoryPrefix mem (updatePositionChangedMemory mem p v a evm) p.toNat := by
  unfold updatePositionChangedMemory
  split_ifs
  · exact .refl _ _
  · apply (oracleObserveZeroMemory_prefix mem p _ _ _ _ hb).trans
    apply (twoWordHashMem_prefix _ (EVM.wordOfInt a.lower) ⟨5⟩ p.toNat).trans
    apply (twoWordHashMem_prefix _ (EVM.wordOfInt a.upper) ⟨5⟩ p.toNat).trans
    exact (updatePositionBitmapMemory_prefix _ v a evm false p.toNat).trans
      (updatePositionBitmapMemory_prefix _ v a evm true p.toNat)

theorem tickFeeMemory_prefix (mem : ByteArray) (a : TickFeeArgs) (limit : Nat) :
    MemoryPrefix mem (tickFeeMemory mem a) limit :=
  (twoWordHashMem_prefix mem (EVM.wordOfInt a.lower) ⟨5⟩ limit).trans
    (wordAt0Mem_prefix _ (EVM.wordOfInt a.upper) limit)

theorem updatePositionClearMemory_prefix (mem : ByteArray) (v : UniswapV3PoolImmutables)
    (a : UpdatePositionArgs) (evm : EVM.State) (upper : Bool) (limit : Nat) :
    MemoryPrefix mem (updatePositionClearMemory mem v a evm upper) limit := by
  unfold updatePositionClearMemory
  split_ifs <;> first | exact twoWordHashMem_prefix mem _ _ limit | exact .refl _ _

theorem updatePositionTailMemory_prefix (mem : ByteArray) (v : UniswapV3PoolImmutables)
    (a : UpdatePositionArgs) (evm : EVM.State) (limit : Nat) :
    MemoryPrefix mem (updatePositionTailMemory mem v a evm) limit := by
  unfold updatePositionTailMemory
  split_ifs
  · exact (updatePositionClearMemory_prefix mem v a evm false limit).trans
      (updatePositionClearMemory_prefix _ v a evm true limit)
  · exact .refl _ _

theorem updatePositionFeeFree_lower (p : UInt256) (a : UpdatePositionArgs) (evm : EVM.State)
    (hb : p.toNat + 442 ≤ 2 ^ 200) :
    p.toNat ≤ (updatePositionFeeFree p a evm).toNat := by
  have h1 : (p + (⟨58⟩ : UInt256)).toNat = p.toNat + 58 :=
    uadd_word_ofNat_toNat p 58 (by change _ < 2 ^ 256; omega)
  unfold updatePositionFeeFree updatePositionChangedFree
  split_ifs
  · rw [h1]; omega
  · have h2 := oracleObserveZeroFree_lower (p + ⟨58⟩)
      (oracleStoredObservation (slot0FieldWord 23 2 evm.accountMap evm.executionEnv)
        evm.accountMap evm.executionEnv) (blockTimestampWord evm.executionEnv) (by rw [h1]; omega)
    exact le_trans (by rw [h1]; omega) h2

theorem updatePositionMemory_prefix (mem : ByteArray) (p : UInt256) (v : UniswapV3PoolImmutables)
    (a : UpdatePositionArgs) (evm : EVM.State) (hb : p.toNat + 442 ≤ 2 ^ 200) :
    MemoryPrefix mem (updatePositionMemory mem p v a evm) p.toNat := by
  have h1 : (p + (⟨58⟩ : UInt256)).toNat = p.toNat + 58 :=
    uadd_word_ofNat_toNat p 58 (by change _ < 2 ^ 256; omega)
  have hprefix := positionGetMem_prefix mem p a.owner (EVM.wordOfInt a.lower)
    (EVM.wordOfInt a.upper) ⟨7⟩
  have hchange := (updatePositionChangedMemory_prefix (updatePositionPrefixMemory a mem p)
    (p + ⟨58⟩) v a evm (by rw [h1]; omega)).mono (show p.toNat ≤ (p + (⟨58⟩ : UInt256)).toNat by
      rw [h1]; omega)
  have hfee := tickFeeMemory_prefix (updatePositionFeeInputMemory mem p v a evm)
    (updatePositionFeeArgs a evm) p.toNat
  have hpos := (wordArrayAllocMem_prefix
    (tickFeeMemory (updatePositionFeeInputMemory mem p v a evm) (updatePositionFeeArgs a evm))
    (updatePositionFeeFree p a evm)
    (positionSnapshotWords (updatePositionKey a) (updatePositionChangedState v a evm).accountMap
      (updatePositionChangedState v a evm).executionEnv)).mono (updatePositionFeeFree_lower p a evm hb)
  exact hprefix.trans (hchange.trans (hfee.trans (hpos.trans
    (updatePositionTailMemory_prefix _ v a evm p.toNat))))

theorem updatePositionFree_lower (p : UInt256) (a : UpdatePositionArgs) (evm : EVM.State)
    (hb : p.toNat + 602 ≤ 2 ^ 200) :
    p.toNat ≤ (updatePositionFree p a evm).toNat := by
  have hlo := updatePositionFeeFree_lower p a evm (by omega)
  have hhi := updatePositionFeeFree_bound p a evm (by omega)
  unfold updatePositionFree
  change p.toNat ≤ (updatePositionFeeFree p a evm + UInt256.ofNat 160).toNat
  rw [uadd_word_ofNat_toNat _ 160 (by change _ < 2 ^ 256; omega)]
  omega

end Benchmarks.UniswapV3.Pool
