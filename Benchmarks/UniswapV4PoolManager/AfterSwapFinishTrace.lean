import Benchmarks.UniswapV4PoolManager.AfterSwapFinishSelectTrace
import Benchmarks.UniswapV4PoolManager.FunctionTraceMono

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def afterSwapFinishHook (p : SwapParamsWords) (specified unspecified : Int) : UInt256 :=
  if unspecified ≠ 0 ∨ specified ≠ 0 then afterSwapPackWord (afterSwapSpecifiedFirst p) specified unspecified else ⟨0⟩
def afterSwapFinishDelta (p : SwapParamsWords) (delta : UInt256) (specified unspecified : Int) : UInt256 :=
  if unspecified ≠ 0 ∨ specified ≠ 0 then
    balanceDeltaCombineWord true delta (afterSwapPackWord (afterSwapSpecifiedFirst p) specified unspecified) else delta

theorem afterSwapFinishTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw ptr delta ret x0 x1 x2 x3 x4 : UInt256} {specified unspecified : Int}
    {k C : Nat} {R : List UInt256} {p : SwapParamsWords}
    (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+10 ≤ 1024)
    (hp : MemorySlice mem ptr.toNat (wordBytes (swapParamsWordList p)))
    (hfit : ptr.toNat+96 < UInt256.size)
    (hs : signedFits ⟨128, by decide⟩ specified) (hu : signedFits ⟨128, by decide⟩ unspecified)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨15800⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: EVM.wordOfInt unspecified :: EVM.wordOfInt specified :: delta :: ret :: ptr :: R)
      mem aw rdata evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0 (fun post values => post = evm ∧
      values = some [.int (EVM.signed (afterSwapFinishDelta p delta specified unspecified)),
        .int (EVM.signed (afterSwapFinishHook p specified unspecified))] ∧
      ∃ aw' k' C', C+Cₘ aw' ≤ C'+Cₘ aw ∧ RD (deployedRuntime v) I g s0 ret
        (afterSwapFinishHook p specified unspecified :: afterSwapFinishDelta p delta specified unspecified :: R)
        mem aw' rdata post.accountMap k' C')
      (afterSwapFinishResult f evm p delta specified unspecified) := by
  have he := afterSwapFinishSelectTrace v hstack hs hu hret h
  by_cases hn : unspecified ≠ 0 ∨ specified ≠ 0
  · rw [if_pos hn] at he
    obtain ⟨k1, C1, hcost1, rd1⟩ := he
    have ht := afterSwapFinishActiveTrace f v hstack hp hfit hn hret rd1
    refine functionResultTrace_mono ht ?_
    rintro post values ⟨rfl, hv, aw', k', C', hcost, rd⟩
    refine ⟨rfl, ?_, aw', k', C', by omega, ?_⟩
    · simpa only [afterSwapFinishDelta, afterSwapFinishHook, if_pos hn] using hv
    · simpa only [afterSwapFinishDelta, afterSwapFinishHook, if_pos hn] using rd
  · rw [if_neg hn] at he
    obtain ⟨k', C', hcost, rd⟩ := he
    rw [afterSwapFinishResult, if_neg hn]
    change _ ∧ _ ∧ _
    exact ⟨rfl, by simp only [afterSwapFinishDelta, afterSwapFinishHook, if_neg hn]; rfl,
      aw, k', C', by omega, by simpa only [afterSwapFinishDelta, afterSwapFinishHook, if_neg hn] using rd⟩

end Benchmarks.UniswapV4PoolManager
