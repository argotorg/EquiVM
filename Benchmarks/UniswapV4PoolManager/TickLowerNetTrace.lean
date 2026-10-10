import Benchmarks.UniswapV4PoolManager.Int128AddTrace
import Benchmarks.UniswapV4PoolManager.TickNetArithmetic
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_021

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem tickLowerNetTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw packed ret discard x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256}
    {delta : Int} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+17 ≤ 1024) (hd : signedFits ⟨128, by decide⟩ delta)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨7024⟩
      (discard :: packed :: ret :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 ::
        EVM.wordOfInt delta :: R) mem aw rdata σ k C) :
    if signedFits ⟨128, by decide⟩ (tickNetAfter packed delta false) then ∃ k' C',
      RD (deployedRuntime v) I g s0 ret
        (EVM.wordOfInt (tickNetAfter packed delta false) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 ::
          x10 :: x11 :: x12 :: x13 :: EVM.wordOfInt delta :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have rd := poolManagerBlocks.poolManager_block_7024 (by omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  have hd' : UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt delta) = EVM.wordOfInt delta :=
    signextend128_wordOfInt hd.1 hd.2
  simp only [poolManagerBlocks.poolManager_block_7024_stack, hd'] at rd
  have rd' : RD (deployedRuntime v) I g s0 ⟨15674⟩
      (EVM.wordOfInt (EVM.signed (tickNetWord packed)) :: EVM.wordOfInt delta :: ret ::
        x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: EVM.wordOfInt delta :: R)
      mem aw rdata σ (k+10) (C+34) := by simpa only [wordOfInt_signed] using rd
  exact int128AddTrace v (by simp only [List.length_cons]; omega) (tickNetWord_fits packed) hd hret rd'

end Benchmarks.UniswapV4PoolManager
