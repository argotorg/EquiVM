import Benchmarks.Midnight.CalldataAddressFunding
import Benchmarks.Midnight.Uint128Arithmetic
import Benchmarks.Midnight.RuntimeBlocks_073

/-! Canonical Boolean and uint128 calldata readers used by the offer decoder. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightCalldataBool_funded {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw head ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 4 ≤ 1024)
    (hcanon : calldataWord I.calldata head.toNat = ⟨0⟩ ∨
      calldataWord I.calldata head.toNat = ⟨1⟩)
    (hvalid : (D_J midnightBytecode 0).contains ret = true)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨19003⟩ (head :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ MemoryFunding credit mem aw C' ∧
      RD midnightBytecode I g s0 ret (calldataWord I.calldata head.toNat :: R)
        mem aw rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_19003_fallthrough hstack
    (u256_sub_eq_zero_iff_eq.mpr ((boolWordClean_iff _).mpr hcanon).symm) rd
  have rd2 := midnightBlocks.midnight_block_19015
    (by simp only [List.length_cons]; omega) hvalid rd1
  exact ⟨_, _, by omega, ha.mono (by omega), rd2⟩

theorem midnightCalldataBool_bad {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw head ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 4 ≤ 1024)
    (hcanon : ¬ (calldataWord I.calldata head.toNat = ⟨0⟩ ∨
      calldataWord I.calldata head.toNat = ⟨1⟩))
    (rd : RD midnightBytecode I g s0 ⟨19003⟩ (head :: ret :: R) mem aw rdata σ k C) :
    RDrev midnightBytecode g s0 := by
  have rd1 := midnightBlocks.midnight_block_19003_taken hstack
    (fun he ↦ hcanon ((boolWordClean_iff _).mp (u256_sub_eq_zero_iff_eq.mp he).symm))
    (by jump_dest) rd
  exact midnightBlocks.midnight_block_6350 (by
    simp only [midnightBlocks.midnight_block_19003_taken_stack, List.length_cons]; omega) rd1

theorem uint128Check_eq_zero_iff (word : UInt256) :
    UInt256.sub word (UInt256.land word
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
        (UInt256.ofNat 1))) = ⟨0⟩ ↔ word.toNat < 2^128 := by
  rw [show UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
      (UInt256.ofNat 1) = uint128Mask from by decide +kernel,
    u256_sub_eq_zero_iff_eq]
  change word = low128 word ↔ _
  constructor
  · intro he
    simpa only [← he] using low128_lt word
  · intro hn
    apply u256_inj
    rw [low128_toNat, Nat.mod_eq_of_lt hn]

theorem midnightCalldataUint128_funded {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw head ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 5 ≤ 1024)
    (hcanon : (calldataWord I.calldata head.toNat).toNat < 2^128)
    (hvalid : (D_J midnightBytecode 0).contains ret = true)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨19113⟩ (head :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ MemoryFunding credit mem aw C' ∧
      RD midnightBytecode I g s0 ret (calldataWord I.calldata head.toNat :: R)
        mem aw rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_19113_fallthrough hstack
    ((uint128Check_eq_zero_iff _).mpr hcanon) rd
  have rd2 := midnightBlocks.midnight_block_19132
    (by simp only [List.length_cons]; omega) hvalid rd1
  exact ⟨_, _, by omega, ha.mono (by omega), rd2⟩

theorem midnightCalldataUint128_bad {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw head ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 5 ≤ 1024)
    (hcanon : ¬ (calldataWord I.calldata head.toNat).toNat < 2^128)
    (rd : RD midnightBytecode I g s0 ⟨19113⟩ (head :: ret :: R) mem aw rdata σ k C) :
    RDrev midnightBytecode g s0 := by
  have rd1 := midnightBlocks.midnight_block_19113_taken hstack
    (fun he ↦ hcanon ((uint128Check_eq_zero_iff _).mp he)) (by jump_dest) rd
  exact midnightBlocks.midnight_block_6350 (by
    simp only [midnightBlocks.midnight_block_19113_taken_stack, List.length_cons]; omega) rd1

end Benchmarks.Midnight
