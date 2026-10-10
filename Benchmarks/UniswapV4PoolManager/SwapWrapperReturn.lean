import Benchmarks.UniswapV4PoolManager.SwapWrapperTailTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

structure SwapWrapperMemory (before after : ByteArray) (state free : UInt256) : Prop where
  freeLoad : memLoad (UInt256.ofNat 64) after = free
  lower : state.toNat+96 ≤ free.toNat
  upper : free.toNat ≤ state.toNat+352
  size : after.size = max before.size (free.toNat+192)
  saved : ∀ base data, MemorySlice before base data → 96 ≤ base → base+data.size ≤ state.toNat →
    MemorySlice after base data

theorem swapWrapperMemory_of_pool {before mem : ByteArray} {state free : UInt256} {r : PoolSwapResultWords}
    (h : PoolSwapReturnMemory before mem state free r) (delta fee amount : UInt256) (currency : AccountAddress)
    (hl : 96 ≤ state.toNat) (hf : state.toNat+352 < UInt256.size) :
    SwapWrapperMemory before (swapWrapperTailMemory mem free delta fee amount currency r) state free := by
  have h96 := uadd_word_ofNat_toNat state 96 (by omega)
  have h352 := uadd_word_ofNat_toNat state 352 hf
  have hbounds : state.toNat+96 ≤ free.toNat ∧ free.toNat ≤ state.toNat+352 := by
    rcases h.freeChoice with hh | hh <;> rw [hh] <;> omega
  have hm : 96 ≤ mem.size := by
    have hh := h.result.inBounds
    change state.toNat+96 ≤ mem.size at hh
    omega
  refine ⟨(swapWrapperTailMemory_free _ _ _ _ _ _ _ hm (by omega)).trans h.freeLoad,
    hbounds.1, hbounds.2, ?_, ?_⟩
  · rw [swapWrapperTailMemory_size _ _ _ _ _ _ _ (by omega), h.size]
    omega
  · intro base data hs hb he
    exact (h.saved base data hs hb he).swapWrapperTail _ _ _ _ _ _ (by omega) (by omega)

def swapWrapperReturn (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (mem rdata : ByteArray) (state params x8 x9 x10 x11 x12 x13 hookPtr junk : UInt256)
    (R : List UInt256) (post : State) (values : Option (List Value)) : Prop :=
  ∃ delta out free aw k C, post.executionEnv = I ∧ post.σ₀ = s0.σ₀ ∧
    values = some [.int (EVM.signed delta)] ∧ Cₘ aw ≤ C ∧
    RD (deployedRuntime v) I g s0 ⟨1930⟩
      ([memLoad hookPtr out, UInt256.ofNat 1461501637330902918203684832716283019655932542975,
        x12, params, delta, x8, x9, x10, x11, x12, x13, hookPtr, UInt256.ofNat 32, junk]++R)
      out aw rdata post.accountMap k C ∧ SwapWrapperMemory mem out state free

theorem swapWrapperReturn_of_tail {v : PoolManagerImmutables} {I : ExecutionEnv} {g : Sat256}
    {s0 evm post : State} {mem out rdata : ByteArray}
    {state free delta fee amount params x8 x9 x10 x11 x12 x13 hookPtr junk : UInt256}
    {currency : AccountAddress} {r : PoolSwapResultWords} {R : List UInt256} {values : Option (List Value)}
    (hI : evm.executionEnv = I) (hσ : evm.σ₀ = s0.σ₀)
    (hm : PoolSwapReturnMemory mem out state free r) (hl : 96 ≤ state.toNat)
    (hf : state.toNat+352 < UInt256.size)
    (ht : swapWrapperTailReturn v I g s0 evm out rdata free delta fee amount params x8 x9 x10
      x11 x12 x13 hookPtr junk currency r R post values) :
    swapWrapperReturn v I g s0 mem rdata state params x8 x9 x10 x11 x12 x13 hookPtr junk R post values := by
  obtain ⟨rfl, hv, aw, k, C, hp, rd⟩ := ht
  exact ⟨delta, _, free, aw, k, C, (swapWrapperFeePost_executionEnv ..).trans hI,
    (swapWrapperFeePost_σ₀ ..).trans hσ, hv, hp, rd, swapWrapperMemory_of_pool hm delta fee amount currency hl hf⟩

end Benchmarks.UniswapV4PoolManager
