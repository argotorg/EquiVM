import Benchmarks.UniswapV3.Pool.ProtocolFeeStorage
import Benchmarks.UniswapV3.Pool.TupleReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: two adjacent word writes at an arbitrary heap pointer.
theorem pairEventMem_size (mem : ByteArray) (ptr first second : UInt256) :
    (pairEventMem mem ptr first second).size = max mem.size (ptr.toNat + 64) := by
  rw [pairEventMem, writeWord_sparse_size, writeWord_sparse_size]
  omega

theorem pairEventMem_read (mem : ByteArray) (ptr first second : UInt256) :
    (pairEventMem mem ptr first second).readWithPadding ptr.toNat 64 =
      first.toByteArray ++ second.toByteArray := by
  rw [show 64 = 32 + 32 from rfl, byteArray_readWithPadding_split_unbounded _ _ 32 32
    (by decide) (by decide) (by rw [pairEventMem_size]; omega)]
  unfold pairEventMem
  rw [writeWord_sparse_read_preserved _ _ _ _
    (Or.inl ⟨le_refl _, by rw [writeWord_sparse_size]; omega⟩),
    writeWord_sparse_read_back, writeWord_sparse_read_back]

theorem RD.poolReturnUint128Pair_heap {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {v : UniswapV3PoolImmutables} {a b aw p : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : AccountMap}
    (rd : RD (deployedRuntime v) ee g s0 ⟨690⟩ (b :: a :: R) mem aw rdata acc k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 64 ≤ 2 ^ 200)
    (ha : a.toNat < 2 ^ 128) (hb' : b.toNat < 2 ^ 128) (hov : R.length + 8 ≤ 1024) :
    RDret (deployedRuntime v) g s0 acc (a.toByteArray ++ b.toByteArray) := by
  have hret := uniswapV3Pool_block_690 (immWords := wordsOf (immStore v)) hov rd
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have hca : UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) a = a := uint128Word_clean ha
  have hcb : UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) b = b := uint128Word_clean hb'
  simp only [solcMask128, hca, hcb, hload] at hret
  have hp32 : ((UInt256.ofNat 32) + p).toNat = p.toNat + 32 := by
    rw [u256_add_comm]
    exact uadd_word_ofNat_toNat p 32 (by change _ < 2 ^ 256; omega)
  have hfold : b.toByteArray.write 0 (a.toByteArray.write 0 mem p.toNat 32) (p.toNat + 32) 32 =
      pairEventMem mem p a b := rfl
  have hnewload : memLoad (UInt256.ofNat 64) (pairEventMem mem p a b) = p :=
    (pairEventHeap hm.cursor hb).load64
  have hlen : UInt256.sub ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + p)) p = ⟨64⟩ := by
    rw [← uadd_assoc, show (UInt256.ofNat 32) + (UInt256.ofNat 32) = (⟨64⟩ : UInt256) from by decide,
      u256_add_comm (⟨64⟩ : UInt256) p, word_add_sub_left]
  simp only [hp32, hfold, hnewload, hlen, show (⟨64⟩ : UInt256).toNat = 64 from rfl,
    pairEventMem_read] at hret
  exact hret


end Benchmarks.UniswapV3.Pool
