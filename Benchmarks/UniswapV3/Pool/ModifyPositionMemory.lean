import Benchmarks.UniswapV3.Pool.ModifyPositionModel
import Benchmarks.UniswapV3.Pool.Slot0Memory
import Benchmarks.UniswapV3.Pool.SnapshotInside
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_052

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def ModifyPositionParamsMemory (mem : ByteArray) (p : UInt256) (a : ModifyPositionArgs) : Prop :=
  WordArrayMemory mem p a.words

theorem ModifyPositionParamsMemory.load_owner {mem : ByteArray} {p : UInt256} {a : ModifyPositionArgs}
    (hm : ModifyPositionParamsMemory mem p a) (hb : p.toNat + 128 < UInt256.size) :
    memLoad p mem = EVM.word a.owner.val := by
  have h := WordArrayMemory.load hm 0 (by change 0 < 4; decide) hb
  simpa only [ModifyPositionArgs.words, List.getElem_cons_zero, Nat.mul_zero,
    show p + UInt256.ofNat 0 = p from u256_add_zero p] using h

theorem ModifyPositionParamsMemory.load_lower {mem : ByteArray} {p : UInt256} {a : ModifyPositionArgs}
    (hm : ModifyPositionParamsMemory mem p a) (hb : p.toNat + 128 < UInt256.size) :
    memLoad (p + UInt256.ofNat 32) mem = EVM.wordOfInt a.lower :=
  WordArrayMemory.load hm 1 (by change 1 < 4; decide) hb

theorem ModifyPositionParamsMemory.load_upper {mem : ByteArray} {p : UInt256} {a : ModifyPositionArgs}
    (hm : ModifyPositionParamsMemory mem p a) (hb : p.toNat + 128 < UInt256.size) :
    memLoad (p + UInt256.ofNat 64) mem = EVM.wordOfInt a.upper :=
  WordArrayMemory.load hm 2 (by change 2 < 4; decide) hb

theorem ModifyPositionParamsMemory.load_delta {mem : ByteArray} {p : UInt256} {a : ModifyPositionArgs}
    (hm : ModifyPositionParamsMemory mem p a) (hb : p.toNat + 128 < UInt256.size) :
    memLoad (p + UInt256.ofNat 96) mem = EVM.wordOfInt a.delta :=
  WordArrayMemory.load hm 3 (by change 3 < 4; decide) hb

theorem modifyPositionUpdateArgs_fits (a : ModifyPositionArgs) (evm : EVM.State) (ha : a.Fits) :
    (modifyPositionUpdateArgs a evm).Fits := by
  refine ⟨ha.1, ha.2.1, ha.2.2, ?_⟩
  dsimp only [modifyPositionUpdateArgs]
  exact slot0TickValue_bounds evm.accountMap evm.executionEnv

theorem modifyPositionSlotHeadMem_eq {mem : ByteArray} {aw p : UInt256}
    (σ : AccountMap) (I : ExecutionEnv) (hm : HeapMemory mem aw p)
    (hb : p.toNat + 224 ≤ 2 ^ 200) :
    uniswapV3Pool_block_16264_memory (ee := I) (σ := σ) (mem := mem) =
      slot0ReadHeadMem mem p σ I := by
  rw [← slot0ReadHeadMem_eq σ I hm hb]
  simp only [uniswapV3Pool_block_16264_memory, uniswapV3Pool_block_10148_memory,
    u256_add_comm (UInt256.ofNat 64) (memLoad (UInt256.ofNat 64) mem),
    signextend_idem ⟨24, by decide⟩ (UInt256.ofNat 2) _ (by decide) (by decide)]

theorem modifyPositionSlotTailMem_eq (mem : ByteArray) (p : UInt256)
    (σ : AccountMap) (I : ExecutionEnv) (hb : p.toNat + 224 ≤ 2 ^ 200) :
    uniswapV3Pool_block_16345_memory (mem := slot0ReadHeadMem mem p σ I)
      (x0 := slot0FieldWord 25 2 σ I) (x2 := p + UInt256.ofNat 96)
      (x3 := UInt256.ofNat 65535) (x6 := solcSlotWordAt ⟨0⟩ σ I) (x7 := p) =
      wordArrayAllocMem mem p (slot0StructWords σ I) := by
  exact slot0ReadTailMem_eq mem p σ I hb

end Benchmarks.UniswapV3.Pool
