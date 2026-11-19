import Benchmarks.Midnight.CollateralData
import Benchmarks.Midnight.MemoryWords
import Benchmarks.Midnight.AddressDecode

/-! Copying one decoded collateral record into the market's ABI return buffer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def collateralEncodeRaw (mem : ByteArray) (ptr output : UInt256) : ByteArray :=
  let mask := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)
  let m1 := writeWord mem output.toNat (UInt256.land (memLoad ptr mem) mask)
  let m2 := writeWord m1 (output + UInt256.ofNat 32).toNat (memLoad (ptr + UInt256.ofNat 32) m1)
  let m3 := writeWord m2 (output + UInt256.ofNat 64).toNat (memLoad (ptr + UInt256.ofNat 64) m2)
  writeWord m3 (output + UInt256.ofNat 96).toNat (UInt256.land (memLoad (ptr + UInt256.ofNat 96) m3) mask)

theorem collateralEncodeBlock_shape (mem : ByteArray) (writePtr output : UInt256) :
    midnightBlocks.midnight_block_19324_memory (mem := mem) (x2 := writePtr) (x5 := output) =
      collateralEncodeRaw mem (memLoad writePtr mem) output := rfl

theorem collateralEncodeRaw_eq {mem : ByteArray} {ptr output : UInt256} (c : CollateralData)
    (hm : MemoryWords mem ptr.toNat c.words)
    (hbelow : ptr.toNat + 128 ≤ output.toNat) (hout : output.toNat + 128 < UInt256.size) :
    collateralEncodeRaw mem ptr output = writeWordArray mem output.toNat c.words := by
  have add (off : Nat) (ho : off ≤ 96) : (output + UInt256.ofNat off).toNat = output.toNat + off :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have hlen : c.words.length = 4 := rfl
  have ht : (UInt256.ofNat c.token.val).toNat < EVM.addressModulus := addressWord_val_canonical c.token
  have ho : (UInt256.ofNat c.oracle.val).toNat < EVM.addressModulus := addressWord_val_canonical c.oracle
  have h0 : memLoad ptr mem = UInt256.ofNat c.token.val := hm.load_word ⟨0, by simp [CollateralData.words]⟩ (by simp)
  let m1 := writeWord mem output.toNat (UInt256.ofNat c.token.val)
  have hm1 : MemoryWords m1 ptr.toNat c.words := hm.writeWord _ (Or.inl hbelow)
  have h32 : memLoad (ptr + UInt256.ofNat 32) m1 = c.lltv := hm1.load_offset ⟨1, by simp [CollateralData.words]⟩ rfl
  let m2 := writeWord m1 (output + UInt256.ofNat 32).toNat c.lltv
  have hm2 : MemoryWords m2 ptr.toNat c.words := hm1.writeWord _ (Or.inl (by rw [add 32 (by decide)]; omega))
  have h64 : memLoad (ptr + UInt256.ofNat 64) m2 = c.liquidationCursor := hm2.load_offset ⟨2, by simp [CollateralData.words]⟩ rfl
  let m3 := writeWord m2 (output + UInt256.ofNat 64).toNat c.liquidationCursor
  have hm3 : MemoryWords m3 ptr.toNat c.words := hm2.writeWord _ (Or.inl (by rw [add 64 (by decide)]; omega))
  have h96 : memLoad (ptr + UInt256.ofNat 96) m3 = UInt256.ofNat c.oracle.val := hm3.load_offset ⟨3, by simp [CollateralData.words]⟩ rfl
  unfold collateralEncodeRaw
  dsimp only
  rw [addressMask_computed, h0, solcAddrMask_clean ht]
  change writeWord (writeWord (writeWord m1 (output + UInt256.ofNat 32).toNat
    (memLoad (ptr + UInt256.ofNat 32) m1)) (output + UInt256.ofNat 64).toNat
    (memLoad (ptr + UInt256.ofNat 64) (writeWord m1 (output + UInt256.ofNat 32).toNat
      (memLoad (ptr + UInt256.ofNat 32) m1)))) (output + UInt256.ofNat 96).toNat _ = _
  rw [h32]
  change writeWord (writeWord m2 (output + UInt256.ofNat 64).toNat
    (memLoad (ptr + UInt256.ofNat 64) m2)) (output + UInt256.ofNat 96).toNat
    (UInt256.land (memLoad (ptr + UInt256.ofNat 96) (writeWord m2 (output + UInt256.ofNat 64).toNat
      (memLoad (ptr + UInt256.ofNat 64) m2))) solcAddrMask) = _
  rw [h64]
  change writeWord m3 (output + UInt256.ofNat 96).toNat
    (UInt256.land (memLoad (ptr + UInt256.ofNat 96) m3) solcAddrMask) = _
  rw [h96, solcAddrMask_clean ho]
  simp only [m3, m2, m1, add 32 (by decide), add 64 (by decide), add 96 (by decide),
    CollateralData.words, writeWordArray, Nat.add_assoc, Nat.reduceAdd]

theorem midnightCollateralEncodeStep {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr writePtr output index count market outputBase : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (c : CollateralData)
    (hstack : R.length + 15 ≤ 1024)
    (hptr : memLoad writePtr mem = ptr) (hm : MemoryWords mem ptr.toNat c.words)
    (hbelow : ptr.toNat + 128 ≤ output.toNat) (hout : output.toNat + 128 < UInt256.size)
    (rd : RD midnightBytecode I g s0 ⟨19324⟩
      (index :: count :: writePtr :: market :: outputBase :: output :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD midnightBytecode I g s0 ⟨19261⟩
      ((index + UInt256.ofNat 1) :: count :: (writePtr + UInt256.ofNat 32) :: market :: outputBase ::
        (output + UInt256.ofNat 128) :: R)
      (writeWordArray mem output.toNat c.words) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_19324 hstack (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_19324_stack, collateralEncodeBlock_shape, hptr,
    collateralEncodeRaw_eq c hm hbelow hout] at rd1
  exact ⟨_, _, _, rd1⟩

end Benchmarks.Midnight
