import Benchmarks.UniswapV4PoolManager.PoolSwapLimitBranchTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapLimitTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw packed limit ret params remaining calculated fee protocol amount x0 x1 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (zeroForOne : Bool) (hstack : R.length+14 ≤ 1024)
    (hl : limit.toNat < 2^160) (hm : memLoad (params+UInt256.ofNat 96) mem = limit)
    (h : RD (deployedRuntime v) I g s0 ⟨18978⟩
      ([x0, x1, slot0SqrtPriceWord packed, ret, params, remaining, calculated, fee, protocol, amount,
        UInt256.fromBool (!zeroForOne)]++R) mem aw rdata σ k C) :
    if poolSwapLimitValid packed limit zeroForOne then
      ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨19061⟩
        ([ret, params, remaining, calculated, fee, protocol, amount, UInt256.fromBool (!zeroForOne)]++R)
        mem (poolSwapLimitAW aw params) rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hstart : RD (deployedRuntime v) I g s0 (if zeroForOne then ⟨18985⟩ else ⟨22052⟩)
      ([slot0SqrtPriceWord packed, ret, params, remaining, calculated, fee, protocol, amount,
        UInt256.fromBool (!zeroForOne)]++R) mem aw rdata σ (k+5) (C+20) := by
    cases zeroForOne
    · have rd := poolManagerBlocks.poolManager_block_18978_taken (by change R.length+11 ≤ 1024; omega)
        (by decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
      exact rd
    · exact poolManagerBlocks.poolManager_block_18978_fallthrough (by change R.length+11 ≤ 1024; omega) rfl h
  have ht := poolSwapLimitBranchTrace v zeroForOne (by change R.length+6+8 ≤ 1024; omega) hl hm hstart
  by_cases hv : poolSwapLimitValid packed limit zeroForOne
  · rw [if_pos hv] at ht ⊢
    obtain ⟨k', C', hc, hr⟩ := ht
    exact ⟨k', C', by omega, hr⟩
  · rw [if_neg hv] at ht ⊢
    exact ht

end Benchmarks.UniswapV4PoolManager
