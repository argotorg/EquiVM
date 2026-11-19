import Benchmarks.Midnight.AddressDecode

/-! Canonical address validation for memory ABI decoders at PC 23130. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightMemoryAddress_ok {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw off ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcanon : (memLoad off mem).toNat < EVM.addressModulus)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨23130⟩ (off :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD midnightBytecode I g s0 ret (memLoad off mem :: R) mem aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_23130_fallthrough hstack (addressCheck_zero hcanon) rd
  simp only [midnightBlocks.midnight_block_23130_fallthrough_stack] at rd1
  have rd2 := midnightBlocks.midnight_block_23149 (by simp only [List.length_cons]; omega) hret rd1
  exact ⟨_, _, _, rd2⟩

theorem midnightMemoryAddress_bad {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw off ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcanon : ¬ (memLoad off mem).toNat < EVM.addressModulus)
    (rd : RD midnightBytecode I g s0 ⟨23130⟩ (off :: ret :: R) mem aw rdata σ k C) :
    RDrev midnightBytecode g s0 := by
  have rd1 := midnightBlocks.midnight_block_23130_taken hstack (addressCheck_nonzero hcanon)
    (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_23130_taken_stack] at rd1
  exact midnightBlocks.midnight_block_6350 (by simp only [List.length_cons]; omega) rd1

end Benchmarks.Midnight
