import Benchmarks.UniswapV3.Pool.BitmapNextPositionTrace
import Benchmarks.UniswapV3.Pool.BitmapNextReadLeftTrace
import Benchmarks.UniswapV3.Pool.BitmapNextReadRightTrace
import Benchmarks.UniswapV3.Pool.BitmapNextResultLeftTrace
import Benchmarks.UniswapV3.Pool.BitmapNextResultRightTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem bitmapNextX {evm : EVM.State} {g : Sat256} {s0 : EVM.State} {k C : Nat}
    {aw ret spacingRaw tickRaw : UInt256} {mem rdata : ByteArray} {R : List UInt256}
    {v : UniswapV3PoolImmutables} (tick spacing : Int) (lte : Bool)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨11307⟩
      ((if lte then ⟨1⟩ else ⟨0⟩) :: spacingRaw :: tickRaw :: ⟨6⟩ :: ret :: R)
      mem aw rdata evm.accountMap k C)
    (htlo : -(2 ^ 23 : Int) ≤ tick) (hthi : tick < 2 ^ 23)
    (hslo : -(2 ^ 23 : Int) ≤ spacing) (hshi : spacing < 2 ^ 23)
    (ht : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick)
    (hs : UInt256.signextend (UInt256.ofNat 2) spacingRaw = EVM.wordOfInt spacing)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 20 ≤ 1024) :
    let compressed := bitmapNextCompressed tick spacing
    let masked := bitmapNextMasked evm compressed lte
    (spacing = 0 ∧ RDinvalid (deployedRuntime v) g s0) ∨
      (spacing ≠ 0 ∧ ∃ k' C', RD (deployedRuntime v) evm.executionEnv g s0 ret
        (bitmapNextFlag masked :: bitmapNextResultRaw compressed spacingRaw lte masked :: R)
        (bitmapNextMemory mem compressed lte)
        (M (M (M aw ⟨0⟩ ⟨32⟩) ⟨32⟩ ⟨32⟩) ⟨0⟩ ⟨64⟩) rdata evm.accountMap k' C') := by
  dsimp only
  rcases bitmapNextPrefixRawX (v := v) tick spacing rd htlo hthi hslo hshi ht hs
      (by omega) with hr | ⟨hn, kp, Cp, rp⟩
  · exact Or.inl hr
  refine Or.inr ⟨hn, ?_⟩
  obtain ⟨kpos, Cpos, rpos⟩ := bitmapNextPositionX (v := v)
    (bitmapNextCompressed tick spacing) lte rp (by evm_ov)
  cases lte
  · obtain ⟨kr, Cr, rr⟩ := bitmapNextReadRightX (v := v) (evm := evm)
      (bitmapNextCompressed tick spacing) rpos (by evm_ov)
    exact bitmapNextResultRightX (v := v) (bitmapNextCompressed tick spacing)
      (bitmapNextMasked evm (bitmapNextCompressed tick spacing) false) rr hret hov
  · obtain ⟨kr, Cr, rr⟩ := bitmapNextReadLeftX (v := v) (evm := evm)
      (bitmapNextCompressed tick spacing) rpos (by evm_ov)
    exact bitmapNextResultLeftX (v := v) (bitmapNextCompressed tick spacing)
      (bitmapNextMasked evm (bitmapNextCompressed tick spacing) true) rr hret (by omega)

end Benchmarks.UniswapV3.Pool
