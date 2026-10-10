import Benchmarks.UniswapV4PoolManager.CheckedSignedAmount
import Benchmarks.UniswapV4PoolManager.SignedAmountsTrace
import Benchmarks.UniswapV4PoolManager.SignedWordBounds
import Benchmarks.UniswapV4PoolManager.SafeCast128Trace
import Benchmarks.UniswapV4PoolManager.BlockResultTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem checkedSignedAmountTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw a b amountPC castPC : UInt256} {delta : Int}
    {k C : Nat} {R : List UInt256} (f : Frame) (amountRet castRet : Ident)
    (one : Bool) (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024)
    (ha : a.toNat < 2^160) (hb : b.toNat < 2^160)
    (hdlo : -(2^127 : Int) ≤ delta) (hdhi : delta < 2^127)
    (hamt : (D_J (deployedRuntime v) 0).contains amountPC = true)
    (hcast : (D_J (deployedRuntime v) 0).contains castPC = true)
    (hbridge : ∀ {word : UInt256} {k C : Nat},
      RD (deployedRuntime v) I g s0 amountPC (word :: castPC :: R) mem aw rdata evm.accountMap k C →
      ∃ k' C', RD (deployedRuntime v) I g s0 ⟨14213⟩ (word :: castPC :: R) mem aw rdata evm.accountMap k' C')
    (h : RD (deployedRuntime v) I g s0 (if one then ⟨17610⟩ else ⟨17703⟩)
      (a :: b :: EVM.wordOfInt delta :: amountPC :: castPC :: R) mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun _ post => post = evm ∧ ∃ k' C',
      RD (deployedRuntime v) I g s0 castPC (signedAmountWord one a b delta :: R)
        mem aw rdata post.accountMap k' C') (fun _ _ => False)
      (checkedSignedAmountResult f evm one a b delta amountRet castRet) := by
  have hr := signedAmountTrace one v (by simp only [List.length_cons]; omega) ha hb hdlo hdhi hamt h
  by_cases hs : signedAmountFits one a b delta
  · rw [if_pos hs] at hr
    obtain ⟨k1, C1, rd1⟩ := hr
    obtain ⟨k2, C2, rd2⟩ := hbridge rd1
    have hc := signedToInt128Trace (R := R) (n := EVM.signed (signedAmountWord one a b delta)) v (by omega)
      (signedWord_fits _) hcast (by rw [wordOfInt_signed]; exact rd2)
    simp only [wordOfInt_signed] at hc
    by_cases hf : signedFits ⟨128, by decide⟩ (EVM.signed (signedAmountWord one a b delta))
    · rw [checkedSignedAmountResult, if_pos (show checkedSignedAmountFits one a b delta from ⟨hs, hf⟩)]
      rw [if_pos hf] at hc
      exact ⟨rfl, hc⟩
    · rw [checkedSignedAmountResult, if_neg (show ¬checkedSignedAmountFits one a b delta from fun hh => hf hh.2)]
      rw [if_neg hf] at hc
      exact hc
  · rw [checkedSignedAmountResult, if_neg (show ¬checkedSignedAmountFits one a b delta from fun hh => hs hh.1)]
    rw [if_neg hs] at hr
    exact hr

end Benchmarks.UniswapV4PoolManager
