import Benchmarks.Midnight.MemoryArrayIndex
import Benchmarks.Midnight.CalldataArrayWords
import Benchmarks.Midnight.AddressDecode

/-! Checked indexing and canonical-address reads for calldata arrays. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def calldataIndex (ptr index : UInt256) : UInt256 :=
  UInt256.shiftLeft index (UInt256.ofNat 5) + ptr

theorem calldataIndex_toNat {ptr index : UInt256} (hi : index.toNat < 2 ^ 64)
    (hb : ptr.toNat + 32 * index.toNat < UInt256.size) :
    (calldataIndex ptr index).toNat = ptr.toNat + 32 * index.toNat := by
  have hn := ushl5_ofNat_toNat index.toNat (by omega)
  rw [u256_ofNat_toNat] at hn
  change (UInt256.shiftLeft index (UInt256.ofNat 5)).toNat = 32 * index.toNat at hn
  have he : UInt256.shiftLeft index (UInt256.ofNat 5) = UInt256.ofNat (32 * index.toNat) := by
    apply u256_inj
    rw [hn, UInt256.toNat_ofNat_of_lt (by omega)]
  unfold calldataIndex
  rw [he, u256_add_comm, uadd_word_ofNat_toNat _ _ hb]

theorem calldataArrayWords_index (bytes : ByteArray) {ptr index : UInt256} {count : Nat}
    (hi : index.toNat < count) (hb : count < 2 ^ 64)
    (hspan : ptr.toNat + 32 * count < UInt256.size) :
    (calldataArrayWords bytes count ptr.toNat)[index.toNat]'(by
      rw [calldataArrayWords_length]; exact hi) =
      calldataWord bytes (calldataIndex ptr index).toNat := by
  have hget := calldataArrayWords_get bytes count ptr.toNat
    ⟨index.toNat, by rw [calldataArrayWords_length]; exact hi⟩
  rw [calldataIndex_toNat (by omega) (by omega)]
  exact hget

theorem calldataArrayWords_index_canonical {bytes : ByteArray} {ptr index : UInt256} {count : Nat}
    (hi : index.toNat < count) (hb : count < 2 ^ 64)
    (hspan : ptr.toNat + 32 * count < UInt256.size)
    (hc : CanonicalAddressWords (calldataArrayWords bytes count ptr.toNat)) :
    (calldataWord bytes (calldataIndex ptr index).toNat).toNat < EVM.addressModulus := by
  rw [← calldataArrayWords_index bytes hi hb hspan]
  exact hc _ (List.getElem_mem _)

theorem midnightCalldataIndex {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr count index ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 5 ≤ 1024) (hi : index.toNat < count.toNat)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨19675⟩ (ptr :: count :: index :: ret :: R)
      mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD midnightBytecode I g s0 ret
      (calldataIndex ptr index :: R) mem aw rdata σ k' C' := by
  have hc : UInt256.isZero (UInt256.lt index count) = ⟨0⟩ := by
    rw [ult_one hi]
    rfl
  have rd1 := midnightBlocks.midnight_block_19675_fallthrough
    (by simp only [List.length_cons]; omega) hc rd
  simp only [midnightBlocks.midnight_block_19675_fallthrough_stack] at rd1
  have rd2 := midnightBlocks.midnight_block_19685 (by omega) hret rd1
  exact ⟨_, _, by omega, rd2⟩

theorem midnightCalldataAddressRead {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw head ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 5 ≤ 1024)
    (hc : (calldataWord I.calldata head.toNat).toNat < EVM.addressModulus)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨5543⟩ (head :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD midnightBytecode I g s0 ret
      (calldataWord I.calldata head.toNat :: R) mem aw rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_5543 (by simp only [List.length_cons]; omega)
    (by jump_dest) rd
  have rd2 := midnightBlocks.midnight_block_19691_fallthrough
    (by simp only [List.length_cons]; omega) (addressCheck_zero hc) rd1
  have rd3 := midnightBlocks.midnight_block_19709 (by omega) hret rd2
  exact ⟨_, _, by omega, rd3⟩

end Benchmarks.Midnight
