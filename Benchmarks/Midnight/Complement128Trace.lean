import Benchmarks.Midnight.CheckedSubGas
import Benchmarks.Midnight.Uint128Arithmetic

/-! The checked subtraction from the uint128 maximum, with accumulated gas preserved. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightComplement128 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw value ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 5 ≤ 1024) (hvalue : value.toNat < 2 ^ 128)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨19421⟩ (value :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧
      RD midnightBytecode I g s0 ret (complement128 value :: R) mem aw rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_19421_fallthrough hstack
    (by rw [uint128Mask_computed]; exact complement128_guard hvalue) rd
  simp only [midnightBlocks.midnight_block_19421_fallthrough_stack,
    uint128Mask_computed] at rd1
  have rd2 := midnightBlocks.midnight_block_19446
    (by simp only [List.length_cons]; omega) hret rd1
  exact ⟨_, _, by omega, rd2⟩

theorem midnightComplement128Revert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw value ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 5 ≤ 1024) (hvalue : 2 ^ 128 ≤ value.toNat)
    (rd : RD midnightBytecode I g s0 ⟨19421⟩ (value :: ret :: R) mem aw rdata σ k C) :
    RDrev midnightBytecode g s0 := by
  have hlt : uint128Mask.toNat < value.toNat := by
    change 340282366920938463463374607431768211455 < value.toNat
    omega
  have hc : UInt256.gt (complement128 value) uint128Mask = ⟨1⟩ := by
    apply ugt_one
    rw [complement128, usub_toNat_underflow hlt]
    have hv := value.val.isLt
    change value.toNat < UInt256.size at hv
    omega
  have rd1 := midnightBlocks.midnight_block_19421_taken hstack
    (by rw [uint128Mask_computed]; change UInt256.gt (complement128 value) uint128Mask ≠ _
        rw [hc]; decide) (by jump_dest) rd
  exact midnightBlocks.midnight_block_7302
    (by simp only [midnightBlocks.midnight_block_19421_taken_stack, List.length_cons]; omega) rd1

end Benchmarks.Midnight
