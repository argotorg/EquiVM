import Benchmarks.UniswapV4PoolManager.HookDeltaReplyTrace
import Benchmarks.UniswapV4PoolManager.HookCallPaidTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

/-- The signed hook reply retains the memory-cost bound established by the callback. -/
theorem hookDeltaPaidTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem data rdata : ByteArray} {aw ptr ret free : UInt256} {hook : AccountAddress} {parse : Bool}
    {k C : Nat} {R : List UInt256} (f : Frame) (v : PoolManagerImmutables)
    (hstack : R.length+13 ≤ 1024) (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hmem : 96 ≤ mem.size) (hdata : BytesObjectView mem ptr data)
    (hd : 32 ≤ data.size) (hsmall : data.size ≤ Ethereum.EVM.maxReturnDataSizeByGas)
    (hlo : 96 ≤ ptr.toNat+32) (hbefore : ptr.toNat+32+data.size ≤ free.toNat)
    (hfit : free.toNat+64 < UInt256.size) (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (hgas : g.toNat < 324518553658429321982441292826060) (hpaid : Cₘ aw ≤ C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨17823⟩
      (accountWord hook :: ptr :: UInt256.fromBool parse :: ret :: R) mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ evm' z out, callViaEVM evm hook 0 data (z, evm', out) ∧
      evm'.executionEnv = I ∧ evm'.σ₀ = s0.σ₀ ∧ out.size < 2^138 ∧
      functionResultTrace (deployedRuntime v) g s0 (fun post values => post = evm' ∧
        values = some [.int (EVM.signed (hookDeltaWord out parse))] ∧ ∃ aw' k' C',
          Cₘ aw' ≤ C' ∧ free.toNat+out.size+4096 ≤ solcMaxU64 ∧
          RD (deployedRuntime v) I g s0 ret (hookDeltaWord out parse :: R)
            (solcReturnDataMem mem free out) aw' out post.accountMap k' C')
        (hookDeltaResult f evm' z data out parse) := by
  have rd0 := poolManagerBlocks.poolManager_block_17823 (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  rcases hookCallPaidTrace
    (R := UInt256.fromBool parse :: ret :: R) (ret := ⟨17833⟩) v
    (by simp only [List.length_cons]; omega) hI hσ0 hmem hdata hd hsmall hlo hbefore
    (by omega) hfree hgas (by omega) (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd0 with
      hog | ⟨evm', z, out, hcall, henv, hworld, ho, hr⟩
  · exact .inl hog
  refine .inr ⟨evm', z, out, hcall, henv, hworld, ho, ?_⟩
  by_cases hv : z = true ∧ hookReplyValid data out
  · rw [if_pos hv] at hr
    rw [hookDeltaResult, if_pos hv]
    obtain ⟨aw1, k1, C1, hpaid1, hroom, rd1⟩ := hr
    have ht := hookDeltaReplyCostTrace {f with locals := f.locals.insert "result" (.bytes out)} v (by omega)
      (returnDataMemory_view _ _ _ hmem (by omega)) (lt_trans ho (by decide)) hfit hret rd1
    exact functionResultTrace_mono ht (fun _ _ ⟨he, hv, aw2, k2, C2, hc, rd2⟩ =>
      ⟨he, hv, aw2, k2, C2, by omega, hroom, rd2⟩)
  · rw [if_neg hv] at hr
    rw [hookDeltaResult, if_neg hv]
    exact hr

end Benchmarks.UniswapV4PoolManager
