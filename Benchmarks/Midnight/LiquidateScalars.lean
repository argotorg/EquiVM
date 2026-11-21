import Benchmarks.Midnight.LiquidateDecode
import Benchmarks.Midnight.AddressDecode
import Benchmarks.Midnight.MemoryAccounting
import Benchmarks.Midnight.RuntimeBlocks_022
import Benchmarks.Midnight.RuntimeBlocks_069

/-! The three address guards, boolean guard, and saved callback in liquidation's head. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightLiquidateScalars {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 10 ≤ 1024)
    (ha : MemoryAccounting mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨5029⟩ R mem aw rdata σ k C) :
    (¬ LiquidateScalarsValid I.calldata ∧ RDrev midnightBytecode g s0) ∨
    (LiquidateScalarsValid I.calldata ∧ ∃ aw' k' C', C ≤ C' ∧
      MemoryAccounting (writeWord mem 736 (calldataWord I.calldata 228)) aw' C' ∧
      RD midnightBytecode I g s0 ⟨5095⟩
        (calldataWord I.calldata 132 :: calldataWord I.calldata 196 ::
          calldataWord I.calldata 164 :: R)
        (writeWord mem 736 (calldataWord I.calldata 228)) aw' rdata σ k' C') := by
  have rd1 := midnightBlocks.midnight_block_5029 (by omega) (by jump_dest) rd
  by_cases hu : (calldataWord I.calldata 132).toNat < EVM.addressModulus
  · have rd2 := midnightBlocks.midnight_block_18320_fallthrough (by omega)
      (addressCheck_zero hu) rd1
    have rd3 := midnightBlocks.midnight_block_18341
      (by change R.length + 1 + 1 ≤ 1024; omega) (by jump_dest) rd2
    by_cases hb : calldataWord I.calldata 164 = ⟨0⟩ ∨ calldataWord I.calldata 164 = ⟨1⟩
    · have hc := u256_sub_eq_zero_iff_eq.mpr ((boolWordClean_iff _).mpr hb).symm
      have rd4 := midnightBlocks.midnight_block_5036_fallthrough (by omega) hc rd3
      by_cases hr : (calldataWord I.calldata 196).toNat < EVM.addressModulus
      · have rd5 := midnightBlocks.midnight_block_5050_fallthrough
          (by change R.length + 1 + 5 ≤ 1024; omega) (addressCheck_zero hr) rd4
        by_cases hc : (calldataWord I.calldata 228).toNat < EVM.addressModulus
        · have rd6 := midnightBlocks.midnight_block_5070_fallthrough
            (by change R.length + 3 + 4 ≤ 1024; omega) (addressCheck_zero hc) rd5
          have ha6 := memoryAccountingAt rd6 (by
            simp only [midnightBlocks.midnight_block_5070_fallthrough_memory]
            memory_account ha)
          exact Or.inr ⟨⟨hu, hb, hr, hc⟩, _, _, _, by omega, ha6, rd6⟩
        · have rr := midnightBlocks.midnight_block_5070_taken
            (by change R.length + 3 + 4 ≤ 1024; omega)
            (addressCheck_nonzero hc) (by jump_dest) rd5
          exact Or.inl ⟨fun h ↦ hc h.2.2.2, midnightBlocks.midnight_block_712
            (by change R.length + 3 + 2 ≤ 1024; omega) rr⟩
      · have rr := midnightBlocks.midnight_block_5050_taken
          (by change R.length + 1 + 5 ≤ 1024; omega)
          (addressCheck_nonzero hr) (by jump_dest) rd4
        exact Or.inl ⟨fun h ↦ hr h.2.2.1, midnightBlocks.midnight_block_712
          (by change R.length + 3 + 2 ≤ 1024; omega) rr⟩
    · have hc : UInt256.sub (calldataWord I.calldata 164)
          (UInt256.isZero (UInt256.isZero (calldataWord I.calldata 164))) ≠ ⟨0⟩ := by
        intro h
        exact hb ((boolWordClean_iff _).mp (u256_sub_eq_zero_iff_eq.mp h).symm)
      have rr := midnightBlocks.midnight_block_5036_taken (by omega) hc (by jump_dest) rd3
      exact Or.inl ⟨fun h ↦ hb h.2.1, midnightBlocks.midnight_block_712
        (by change R.length + 2 + 2 ≤ 1024; omega) rr⟩
  · have rr := midnightBlocks.midnight_block_18320_taken (by omega)
      (addressCheck_nonzero hu) (by jump_dest) rd1
    exact Or.inl ⟨fun h ↦ hu h.1, midnightBlocks.midnight_block_6350
      (by change R.length + 2 + 2 ≤ 1024; omega) rr⟩

end Benchmarks.Midnight
