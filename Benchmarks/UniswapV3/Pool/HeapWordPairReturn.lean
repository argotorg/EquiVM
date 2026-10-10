import Benchmarks.UniswapV3.Pool.HeapTupleReturn
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_005

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem RD.poolReturnWordPair_heap {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {v : UniswapV3PoolImmutables} {a b aw p : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : AccountMap}
    (rd : RD (deployedRuntime v) ee g s0 ⟨621⟩ (b :: a :: R) mem aw rdata acc k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 64 ≤ 2 ^ 200) (hov : R.length + 5 ≤ 1024) :
    RDret (deployedRuntime v) g s0 acc (a.toByteArray ++ b.toByteArray) := by
  have rr := uniswapV3Pool_block_621 (immWords := wordsOf (immStore v)) hov rd
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have hp32 : (p + UInt256.ofNat 32).toNat = p.toNat + 32 :=
    uadd_word_ofNat_toNat p 32 (by change _ < 2 ^ 256; omega)
  have hfold : b.toByteArray.write 0 (a.toByteArray.write 0 mem p.toNat 32) (p.toNat + 32) 32 =
      pairEventMem mem p a b := rfl
  have hnewload : memLoad (UInt256.ofNat 64) (pairEventMem mem p a b) = p :=
    (pairEventHeap hm.cursor hb).load64
  simpa only [hload, hp32, hfold, hnewload, u256_sub_self, u256_zero_add,
    show (UInt256.ofNat 64).toNat = 64 from rfl, pairEventMem_read] using rr

end Benchmarks.UniswapV3.Pool
