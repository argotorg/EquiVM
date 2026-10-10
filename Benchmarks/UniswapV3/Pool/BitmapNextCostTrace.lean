import Benchmarks.UniswapV3.Pool.BitmapNextTrace
import Benchmarks.UniswapV3.Pool.ReachRoutineCost
import Benchmarks.UniswapV3.Pool.TickUpdateMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool

theorem bitmapNextMonoX {evm : EVM.State} {g : Sat256} {s0 : EVM.State} {k C : Nat}
    {aw ret spacingRaw tickRaw : UInt256} {mem rdata : ByteArray} {R : List UInt256}
    {v : UniswapV3PoolImmutables} (tick spacing : Int) (lte : Bool)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨11307⟩
      ((if lte then ⟨1⟩ else ⟨0⟩) :: spacingRaw :: tickRaw :: ⟨6⟩ :: ret :: R)
      mem aw rdata evm.accountMap k C)
    (htlo : -(2 ^ 23 : Int) ≤ tick) (hthi : tick < 2 ^ 23)
    (hslo : -(2 ^ 23 : Int) ≤ spacing) (hshi : spacing < 2 ^ 23)
    (ht : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick)
    (hs : UInt256.signextend (UInt256.ofNat 2) spacingRaw = EVM.wordOfInt spacing)
    (ha : ActiveWords aw) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 20 ≤ 1024) :
    let compressed := bitmapNextCompressed tick spacing
    let masked := bitmapNextMasked evm compressed lte
    (¬(spacing ≠ 0) ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (spacing ≠ 0 ∧ ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) evm.executionEnv g s0 ret
        (bitmapNextFlag masked :: bitmapNextResultRaw compressed spacingRaw lte masked :: R)
        (bitmapNextMemory mem compressed lte) aw rdata evm.accountMap k' C') := by
  dsimp only
  apply rdRoutine_mono rd
  intro gas start rr
  rcases bitmapNextX (v := v) tick spacing lte rr htlo hthi hslo hshi ht hs hret hov with
    ⟨hz, hr⟩ | ⟨hn, kr, Cr, rout⟩
  · exact Or.inl ⟨fun h ↦ h hz, Or.inr hr⟩
  · refine Or.inr ⟨hn, kr, Cr, ?_⟩
    change RD (deployedRuntime v) evm.executionEnv gas start ret _ _
      (tickUpdateMemoryWords aw) rdata evm.accountMap kr Cr at rout
    rwa [tickUpdateMemoryWords_eq ha] at rout

end Benchmarks.UniswapV3.Pool
