import Benchmarks.Midnight.AddressDecode

variable {fork : Ethereum.Fork}

/-! The address decoder shared by dynamic calldata structures. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightCalldataAddress_ok {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw head ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 5 ≤ 1024)
    (hcanon : (calldataWord I.calldata head.toNat).toNat < EVM.addressModulus)
    (hvalid : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode I g s0 ⟨18342⟩ (head :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD fork midnightBytecode I g s0 ret (calldataWord I.calldata head.toNat :: R)
      mem aw rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_18342_fallthrough hstack
    (addressCheck_zero hcanon) rd
  have rd2 := midnightBlocks.midnight_block_18361 (by
    simp only [List.length_cons]; omega) hvalid rd1
  exact ⟨_, _, rd2⟩

theorem midnightCalldataAddress_bad {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw head ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 5 ≤ 1024)
    (hcanon : ¬ (calldataWord I.calldata head.toNat).toNat < EVM.addressModulus)
    (rd : RD fork midnightBytecode I g s0 ⟨18342⟩ (head :: ret :: R) mem aw rdata σ k C) :
    RDrev fork midnightBytecode g s0 := by
  have rd1 := midnightBlocks.midnight_block_18342_taken hstack
    (addressCheck_nonzero hcanon) (by jump_dest) rd
  exact midnightBlocks.midnight_block_6350 (by
    simp only [midnightBlocks.midnight_block_18342_taken_stack, List.length_cons]; omega) rd1

end Benchmarks.Midnight
