import Benchmarks.Midnight.MarketHeapAccess
import Benchmarks.Midnight.RuntimeBlocks_074

/-! The bounds-checked index routine for arrays of pointers in memory. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem arrayIndexWord {index : UInt256} (hi : index.toNat < 2^64) (ptr : UInt256) :
    UInt256.shiftLeft index (UInt256.ofNat 5) + ptr + UInt256.ofNat 32 =
      (ptr + UInt256.ofNat 32) + UInt256.ofNat (32 * index.toNat) := by
  have hn := ushl5_ofNat_toNat index.toNat (by omega)
  rw [u256_ofNat_toNat] at hn
  change (UInt256.shiftLeft index (UInt256.ofNat 5)).toNat = 32 * index.toNat at hn
  have he : UInt256.shiftLeft index (UInt256.ofNat 5) = UInt256.ofNat (32 * index.toNat) := by
    apply u256_inj
    rw [hn, UInt256.toNat_ofNat_of_lt (by change 32 * _ < 2^256; omega)]
  rw [he, u256_add_comm (UInt256.ofNat _), wordAddNat_add, wordAddNat_add]
  rw [Nat.add_comm (32 * index.toNat) 32]

set_option maxRecDepth 2000000 in
theorem midnightMemoryArrayIndex {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr index ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 5 ≤ 1024)
    (hi : index.toNat < 2^64) (hlt : index.toNat < (memLoad ptr mem).toNat)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨19460⟩ (ptr :: index :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD midnightBytecode I g s0 ret
      (((ptr + UInt256.ofNat 32) + UInt256.ofNat (32 * index.toNat)) :: R)
      mem aw' rdata σ k' C' := by
  have hc : UInt256.lt index (memLoad ptr mem) = ⟨1⟩ := ult_one hlt
  have rd1 := midnightBlocks.midnight_block_19460_fallthrough (by
    simp only [List.length_cons]; omega) (by rw [hc]; rfl) rd
  have rd2 := midnightBlocks.midnight_block_19470 hstack hret rd1
  simp only [midnightBlocks.midnight_block_19470_stack, arrayIndexWord hi] at rd2
  exact ⟨_, _, _, rd2⟩

end Benchmarks.Midnight
