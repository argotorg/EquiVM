import Benchmarks.Midnight.CalldataAddress
import Benchmarks.Midnight.MemoryFunding

variable {fork : Ethereum.Fork}

/-! The shared calldata-address check preserves memory funding and accumulated gas. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem midnightCalldataAddress_funded {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw head ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 5 ≤ 1024)
    (hcanon : (calldataWord I.calldata head.toNat).toNat < EVM.addressModulus)
    (hvalid : (D_J midnightBytecode 0).contains ret = true)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨18342⟩ (head :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ MemoryFunding credit mem aw C' ∧
      RD fork midnightBytecode I g s0 ret (calldataWord I.calldata head.toNat :: R)
        mem aw rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_18342_fallthrough hstack
    (addressCheck_zero hcanon) rd
  have rd2 := midnightBlocks.midnight_block_18361
    (by simp only [List.length_cons]; omega) hvalid rd1
  exact ⟨_, _, by omega, ha.mono (by omega), rd2⟩

end Benchmarks.Midnight
