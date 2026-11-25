import Benchmarks.Midnight.TickArithmetic
import Benchmarks.Midnight.TickExpRuntime
import Benchmarks.Midnight.CheckedExtraGas
import Benchmarks.Midnight.RuntimeBlocks_044

variable {fork : Ethereum.Fork}

/-! Runtime tick-to-price arithmetic up to the final fixed-step rounding block. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTickPriceCore {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw tick : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 13 ≤ 1024) (hbound : tick.toNat ≤ 6744)
    (rd : RD fork midnightBytecode I g s0 ⟨11430⟩ (tick :: R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD fork midnightBytecode I g s0 ⟨11514⟩
      (UInt256.div (tickPriceNumerator tick.toNat) (tickPriceDenominator tick.toNat) ::
        UInt256.ofNat 49999999999 :: UInt256.ofNat 100000000000 ::
        UInt256.ofNat 100000000000 :: R) mem aw rdata σ k' C' := by
  have hf := tickArithmeticFacts tick hbound
  have rd1 := midnightBlocks.midnight_block_11430 (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_11430_stack] at rd1
  have hexp : ∃ k2 C2, C + 43 ≤ C2 ∧ RD fork midnightBytecode I g s0 ⟨11467⟩
      (tickExpWord tick.toNat :: UInt256.ofNat 11514 :: UInt256.ofNat 49999999999 ::
        UInt256.ofNat 100000000000 :: UInt256.ofNat 100000000000 :: R)
      mem aw rdata σ k2 C2 := by
    by_cases hn : tickExpArgument tick.toNat < 0
    · have hneg := hf.1 hn
      simp only [u256_ofNat_toNat] at hneg
      obtain ⟨k2, C2, hC2, rd2⟩ := midnightWExp_negative
        (by simp only [List.length_cons]; omega) hneg.1 hneg.2.1 hneg.2.2.1
        (by jump_dest) rd1
      exact ⟨k2, C2, hC2, by simpa only [tickExpWord, if_pos hn, u256_ofNat_toNat] using rd2⟩
    · have hpos := hf.2.1 (by omega)
      simp only [u256_ofNat_toNat] at hpos
      obtain ⟨k2, C2, hC2, rd2⟩ := midnightWExp_nonnegative
        (by simp only [List.length_cons]; omega) hpos (by jump_dest) rd1
      exact ⟨k2, C2, hC2, by simpa only [tickExpWord, if_neg hn, u256_ofNat_toNat] using rd2⟩
  obtain ⟨k2, C2, hC2, rd2⟩ := hexp
  have rd3 := midnightBlocks.midnight_block_11467
    (by simp only [List.length_cons]; omega) (by jump_dest) rd2
  simp only [midnightBlocks.midnight_block_11467_stack] at rd3
  obtain ⟨k4, C4, hC4, rd4⟩ := midnightCheckedDiv_mono
    (by simp only [List.length_cons]; omega) hf.2.2.2.1 (by jump_dest) rd3
  exact ⟨k4, C4, by omega, rd4⟩

end Benchmarks.Midnight
