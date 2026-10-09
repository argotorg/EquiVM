import Benchmarks.Morpho.MorphoBlue.ArithmeticRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoCheckedIncrementOk {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw x ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (hfit : x.toNat + 1 < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13051)
      (x :: ret :: R) mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      ((x + UInt256.ofNat 1) :: R) mem aw out σ k' C' := by
  have hn : x ≠ UInt256.ofNat
      115792089237316195423570985008687907853269984665640564039457584007913129639935 := by
    intro he
    rw [he] at hfit
    change 115792089237316195423570985008687907853269984665640564039457584007913129639935 + 1 < 2 ^ 256 at hfit
    omega
  have rd1 := morphoBlocks.morpho_block_13051_fallthrough (immWords := wordsOf (immStore v))
    (by simp; omega) (u256_eq_of_ne hn) h
  have rd2 := morphoBlocks.morpho_block_13091 (immWords := wordsOf (immStore v))
    (by omega) hvalid rd1
  simpa only [morphoBlocks.morpho_block_13091_stack, u256_add_comm] using
    (show ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      ((UInt256.ofNat 1 + x) :: R) mem aw out σ k' C' from ⟨_, _, rd2⟩)

theorem morphoCheckedIncrementOverflow {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw x ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 8 ≤ 1024)
    (hfit : UInt256.size ≤ x.toNat + 1)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13051)
      (x :: ret :: R) mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  have hx : x = UInt256.ofNat
      115792089237316195423570985008687907853269984665640564039457584007913129639935 := by
    apply u256_inj
    have hx := x.val.isLt
    change x.toNat < 2 ^ 256 at hx
    change 2 ^ 256 ≤ x.toNat + 1 at hfit
    change x.toNat = 115792089237316195423570985008687907853269984665640564039457584007913129639935
    omega
  have rd1 := morphoBlocks.morpho_block_13051_taken (immWords := wordsOf (immStore v))
    (by simp; omega) (by rw [hx]; decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  exact morphoBlocks.morpho_block_3277 (immWords := wordsOf (immStore v))
    (by simp; omega) rd1

end Benchmarks.Morpho.MorphoBlue
