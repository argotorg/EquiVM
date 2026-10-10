import Benchmarks.UniswapV3.Pool.BurnModel
import Benchmarks.UniswapV3.Pool.ModifyPositionMemory
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_031

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def burnCastMemory (mem : ByteArray) (p : UInt256) (a : BurnArgs) (evm : EVM.State) : ByteArray :=
  writeWordArray (writeWord mem 64 (p + UInt256.ofNat 128)) p.toNat
    [EVM.word evm.executionEnv.source.val, EVM.wordOfInt a.lower, EVM.wordOfInt a.upper]

theorem burnDeltaWord (a : BurnArgs) (evm : EVM.State) :
    UInt256.signextend (UInt256.ofNat 15) (UInt256.sub (UInt256.ofNat 0) a.amount) =
      EVM.wordOfInt (burnModifyArgs a evm).delta := by
  have hw : UInt256.sub (UInt256.ofNat 0) a.amount = EVM.wordOfInt (0 - Int.ofNat a.amount.toNat) := by
    rw [wordOfInt_sub, wordOfInt_ofNat_toNat]
    rfl
  rw [hw, signextend_wordOfInt ⟨128, by decide⟩ _ _ (by decide) (by decide)]
  rfl

theorem burnCastMemory_eq {mem : ByteArray} {aw p : UInt256} {ee : ExecutionEnv}
    (a : BurnArgs) (evm : EVM.State) (ha : a.Fits) (hm : HeapMemory mem aw p)
    (he : evm.executionEnv = ee) (hb : p.toNat + 128 ≤ 2 ^ 200) :
    uniswapV3Pool_block_9648_memory (ee := ee) (mem := mem)
      (x3 := EVM.wordOfInt a.upper) (x4 := EVM.wordOfInt a.lower) = burnCastMemory mem p a evm := by
  have hadd (n : Nat) (hn : n ≤ 128) : (p + UInt256.ofNat n).toNat = p.toNat + n :=
    uadd_word_ofNat_toNat p n (by change _ < 2 ^ 256; omega)
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  rw [uniswapV3Pool_block_9648_memory, hload,
    signextend_wordOfInt ⟨24, by decide⟩ (UInt256.ofNat 2) a.lower (by decide) (by decide),
    signextend_wordOfInt ⟨24, by decide⟩ (UInt256.ofNat 2) a.upper (by decide) (by decide),
    normalizeSint_eq_self ⟨24, by decide⟩ _ ha.1.1 ha.1.2,
    normalizeSint_eq_self ⟨24, by decide⟩ _ ha.2.1.1 ha.2.1.2,
    hadd 32 (by decide), hadd 64 (by decide)]
  simp only [burnCastMemory, writeWordArray, Reasoning.Theory.writeWord, he, Nat.add_assoc]
  rfl

theorem burnModifyMemory_eq (mem : ByteArray) (p : UInt256) (a : BurnArgs) (evm : EVM.State)
    (hb : p.toNat + 128 ≤ 2 ^ 200) :
    uniswapV3Pool_block_9724_memory (mem := burnCastMemory mem p a evm)
      (x0 := a.amount) (x1 := p + UInt256.ofNat 96) =
      wordArrayAllocMem mem p (burnModifyArgs a evm).words := by
  have hp96 := uadd_word_ofNat_toNat p 96 (show p.toNat + 96 < UInt256.size by change _ < 2 ^ 256; omega)
  simp only [uniswapV3Pool_block_9724_memory, burnDeltaWord a evm, hp96,
    burnCastMemory, wordArrayAllocMem, ModifyPositionArgs.words, burnModifyArgs,
    writeWordArray, Reasoning.Theory.writeWord, List.length_cons, List.length_nil, Nat.add_assoc]

theorem burnModifyArgs_locked (a : BurnArgs) (evm : EVM.State) :
    burnModifyArgs a (storeSlot0Unlocked evm false) = burnModifyArgs a evm := by
  simp only [burnModifyArgs, storeSlot0Unlocked_executionEnv]

end Benchmarks.UniswapV3.Pool
