import Benchmarks.UniswapV4PoolManager.HookDeltaReplyTrace
import Benchmarks.UniswapV4PoolManager.HookCallTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem hookDeltaTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem data rdata : ByteArray} {aw ptr ret free : UInt256} {hook : AccountAddress} {parse : Bool}
    {k C : Nat} {R : List UInt256} (f : Frame) (v : PoolManagerImmutables)
    (hstack : R.length+13 ≤ 1024) (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hmem : 96 ≤ mem.size) (hdata : BytesObjectView mem ptr data)
    (hd : 32 ≤ data.size) (hsmall : data.size ≤ Ethereum.EVM.maxReturnDataSizeByGas)
    (hlo : 96 ≤ ptr.toNat+32) (hbefore : ptr.toNat+32+data.size ≤ free.toNat)
    (hfit : free.toNat+64 < UInt256.size) (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨17823⟩
      (accountWord hook :: ptr :: UInt256.fromBool parse :: ret :: R) mem aw rdata evm.accountMap k C) :
    ∃ evm' z out, callViaEVM evm hook 0 data (z, evm', out) ∧
      evm'.executionEnv = I ∧ evm'.σ₀ = s0.σ₀ ∧ out.size < 2^138 ∧
      functionResultTrace (deployedRuntime v) g s0 (fun post values => post = evm' ∧
        values = some [.int (EVM.signed (hookDeltaWord out parse))] ∧ ∃ aw' k' C',
          RD (deployedRuntime v) I g s0 ret (hookDeltaWord out parse :: R)
            (solcReturnDataMem mem free out) aw' out post.accountMap k' C')
        (hookDeltaResult f evm' z data out parse) := by
  have rd0 := poolManagerBlocks.poolManager_block_17823 (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨evm', z, out, hcall, henv, hworld, ho, hr⟩ := hookCallTrace
    (R := UInt256.fromBool parse :: ret :: R) (ret := ⟨17833⟩) v
    (by simp only [List.length_cons]; omega) hI hσ0 hmem hdata hd hsmall hlo hbefore
    (by omega) hfree (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd0
  refine ⟨evm', z, out, hcall, henv, hworld, ho, ?_⟩
  by_cases hv : z = true ∧ hookReplyValid data out
  · rw [if_pos hv] at hr
    rw [hookDeltaResult, if_pos hv]
    obtain ⟨aw1, k1, C1, rd1⟩ := hr
    exact hookDeltaReplyTrace _ v (by omega) (returnDataMemory_view _ _ _ hmem (by omega))
      (lt_trans ho (by decide)) hfit hret rd1
  · rw [if_neg hv] at hr
    rw [hookDeltaResult, if_neg hv]
    exact hr

end Benchmarks.UniswapV4PoolManager
