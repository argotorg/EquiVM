import Benchmarks.Midnight.RuntimeBlocks_075
import Benchmarks.Midnight.AddressDecode

/-! The shared checked address load from a calldata word. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- GENERALIZES the checked calldata-address routine to arbitrary pointers and continuations.
theorem midnightCalldataAddressDirectRead {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr ret : UInt256} {address : AccountAddress}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 5 ≤ 1024)
    (hread : calldataWord I.calldata ptr.toNat = UInt256.ofNat address.val)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨19691⟩ (ptr :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD midnightBytecode I g s0 ret
      (UInt256.ofNat address.val :: R) mem aw rdata σ k' C' := by
  have hr : uInt256OfByteArray (I.calldata.readBytes ptr.toNat 32) =
      UInt256.ofNat address.val := hread
  have rd1 := midnightBlocks.midnight_block_19691_fallthrough
    (by simp only [List.length_cons]; omega)
    (by rw [hr, addressMask_computed, solcAddrMask_clean (addressWord_canonical address),
      u256_sub_self]; rfl) rd
  have rd2 := midnightBlocks.midnight_block_19709 (by omega) hret rd1
  exact ⟨k + 13 + 2, C + 44 + 11, by omega, by
    simpa only [midnightBlocks.midnight_block_19709_stack,
      midnightBlocks.midnight_block_19691_fallthrough_stack, hr] using rd2⟩

end Benchmarks.Midnight
