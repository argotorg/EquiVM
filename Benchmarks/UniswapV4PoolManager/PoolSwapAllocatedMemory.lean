import Benchmarks.UniswapV4PoolManager.PoolSwapResultMemory
import Benchmarks.UniswapV4PoolManager.PoolSwapStepMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def poolSwapAllocatedMem (mem : ByteArray) (evm : State) (id state : UInt256) : ByteArray :=
  poolSwapLoadedMem (writeWord mem 64 (state+UInt256.ofNat 96)) evm id state

def poolSwapPreludeMem (mem : ByteArray) (evm : State) (id state : UInt256) (zeroForOne : Bool) : ByteArray :=
  poolSwapStepInitMem (poolSwapAllocatedMem mem evm id state) evm id (state+UInt256.ofNat 96) zeroForOne

theorem poolSwapAllocatedMemory_params {mem : ByteArray} {params state : UInt256} {p : PoolSwapParamsWords}
    (h : WordStructView mem params (poolSwapParamsWordList p)) (evm : State) (id : UInt256)
    (hl : 128 ≤ params.toNat) (hb : params.toNat+160 ≤ state.toNat) (hf : state.toNat+96 < UInt256.size) :
    WordStructView (poolSwapAllocatedMem mem evm id state) params (poolSwapParamsWordList p) := by
  have h0 := h.write_disjoint 64 (state+UInt256.ofNat 96) (.inr (by omega))
  have h1 := poolSwapResultZeroMem_preserves h0 hf hb
  exact poolSwapResultInitMem_preserves h1 (poolSlot0Word evm id) (poolLiquidityWord evm id) hf hb

theorem poolSwapAllocatedMemory_result (mem : ByteArray) (evm : State) (id state : UInt256)
    (hf : state.toNat+96 < UInt256.size) :
    WordStructView (poolSwapAllocatedMem mem evm id state) state
      (poolSwapResultWordList (poolSwapInitialResult (poolSlot0Word evm id) (poolLiquidityWord evm id))) :=
  poolSwapResultInitMem_view _ _ _ _ hf

theorem poolSwapAllocatedMemory_free (mem : ByteArray) (evm : State) (id state : UInt256)
    (hl : 96 ≤ state.toNat) (hf : state.toNat+96 < UInt256.size) :
    memLoad (UInt256.ofNat 64) (poolSwapAllocatedMem mem evm id state) = state+UInt256.ofNat 96 := by
  unfold poolSwapAllocatedMem poolSwapLoadedMem
  have hi : 96 ≤ (writeWord mem 64 (state+UInt256.ofNat 96)).size := by rw [writeWord_sparse_size]; omega
  have hz : 96 ≤ (poolSwapResultZeroMem (writeWord mem 64 (state+UInt256.ofNat 96)) state).size := by
    simp only [poolSwapResultZeroMem, writeWord_sparse_size]
    omega
  rw [poolSwapResultInitMem_free _ _ _ _ hz hl hf, poolSwapResultZeroMem_free _ _ hi hl hf]
  exact writeWord_sparse_load_back mem (UInt256.ofNat 64) _

theorem poolSwapPreludeMemory_view {mem : ByteArray} {params state : UInt256} {p : PoolSwapParamsWords}
    (h : WordStructView mem params (poolSwapParamsWordList p)) (evm : State) (id : UInt256)
    (hl : 128 ≤ params.toNat) (hb : params.toNat+160 ≤ state.toNat) (hf : state.toNat+352 < UInt256.size) :
    PoolSwapMemoryView (poolSwapPreludeMem mem evm id state p.zeroForOne) (state+UInt256.ofNat 96) state params
      (poolSwapInitialStep evm id p.zeroForOne)
      (poolSwapInitialResult (poolSlot0Word evm id) (poolLiquidityWord evm id)) p := by
  have h96 := uadd_word_ofNat_toNat state 96 (by omega)
  have hparams := poolSwapAllocatedMemory_params h evm id hl hb (by omega)
  have hresult := poolSwapAllocatedMemory_result mem evm id state (by omega)
  have hparams' := hparams.write_disjoint 64 (state+UInt256.ofNat 96+UInt256.ofNat 256) (.inr (by omega))
  have hresult' := hresult.write_disjoint 64 (state+UInt256.ofNat 96+UInt256.ofNat 256) (.inr (by omega))
  refine ⟨⟨by rw [h96]; omega, by omega, hl, .inr (by rw [h96]), .inr (by rw [h96]; omega), .inr hb⟩,
    ?_, ?_, ?_⟩
  · exact wordStructView_sequence _ _ _ (by intro hh; cases hh) (by
      change (state+UInt256.ofNat 96).toNat+256 < UInt256.size
      rw [h96]; omega)
  · exact hresult'.write_sequence _ _ (.inl (by
      change state.toNat+96 ≤ (state+UInt256.ofNat 96).toNat
      rw [h96]))
  · exact hparams'.write_sequence _ _ (.inl (by
      change params.toNat+160 ≤ (state+UInt256.ofNat 96).toNat
      rw [h96]; omega))

end Benchmarks.UniswapV4PoolManager
