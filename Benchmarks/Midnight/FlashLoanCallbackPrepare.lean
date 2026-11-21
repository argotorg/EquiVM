import Benchmarks.Midnight.FlashLoanTransferRuntime
import Benchmarks.Midnight.CalldataBytesEncoder
import Benchmarks.Midnight.CalldataArrayCopyMemory

/-! Building the three dynamic arguments of the flash-loan callback. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def flashLoanCallbackSize (tn an dl : Nat) : Nat :=
  196 + 32 * tn + 32 * an + returnDataAllocation dl

def flashLoanCallbackMemory (mem bytes : ByteArray) (sender : AccountAddress)
    (root tp tn ap an dp dl : Nat) : ByteArray :=
  let m0 := writeWord mem root (UInt256.ofNat (3522322627 * 2^224))
  let m1 := writeWord m0 (root + 4) (UInt256.ofNat sender.val)
  let m2 := writeWord m1 (root + 36) (UInt256.ofNat 128)
  let m3 := calldataArrayEncodeMemory m2 (root + 132) bytes tp tn
  let m4 := writeWord m3 (root + 68) (UInt256.ofNat (160 + 32 * tn))
  let m5 := calldataArrayCopyMemory m4 (root + 164 + 32 * tn) bytes ap an
  let m6 := writeWord m5 (root + 100) (UInt256.ofNat (192 + 32 * tn + 32 * an))
  calldataBytesEncodeMemory m6 bytes (root + 196 + 32 * tn + 32 * an) dp dl

theorem midnightFlashLoanCallbackPrepare {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw root tn tp callback an ap dl dp : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 32 ≤ 1024)
    (htn : tn.toNat < 2^64) (han : an.toNat < 2^64) (hdl : dl.toNat < 2^64)
    (htp : tp.toNat + 32 * tn.toNat < UInt256.size)
    (hc : CanonicalAddressWords (calldataArrayWords I.calldata tn.toNat tp.toNat))
    (hroot : root.toNat < 2^128) (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨16266⟩
      (flashLoanOutLoopStack tn tn tp callback an ap dl dp ++ R) mem aw rdata σ k C) :
    ∃ gasArg aw' k' C', C ≤ C' ∧
      MemoryFunding (credit + 4)
        (flashLoanCallbackMemory mem I.calldata I.source root.toNat tp.toNat tn.toNat
          ap.toNat an.toNat dp.toNat dl.toNat) aw' C' ∧
      RD midnightBytecode I g s0 ⟨16367⟩
        ([gasArg, callback, ⟨0⟩, root,
          UInt256.ofNat (flashLoanCallbackSize tn.toNat an.toNat dl.toNat), root, ⟨32⟩,
          root, ap, callback, an, tp, tn] ++ R)
        (flashLoanCallbackMemory mem I.calldata I.source root.toNat tp.toNat tn.toNat
          ap.toNat an.toNat dp.toNat dl.toNat) aw' rdata σ k' C' := by
  have ho (n : Nat) (hn : n ≤ flashLoanCallbackSize tn.toNat an.toNat dl.toNat + 32) :
      (root + UInt256.ofNat n).toNat = root.toNat + n :=
    uadd_word_ofNat_toNat _ _ (by
      unfold flashLoanCallbackSize returnDataAllocation at hn
      change _ < 2^256
      omega)
  have rd1 := midnightBlocks.midnight_block_16266
    (by change R.length + 1 + 1 + 1 + 1 + 1 + 18 ≤ 1024; omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_16266_stack,
    midnightBlocks.midnight_block_16266_memory, hfree] at rd1
  have ha1 := memoryFundingAt (credit := credit + 4) rd1 (by memory_fund ha)
  rcases midnightCalldataAddressEncoderFunded
      (R := [an, ⟨16345⟩, dl, dp, ⟨16363⟩, root, ⟨0⟩, root, callback, root,
        ⟨32⟩, root, ap, callback, an, tp, tn] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      htp (by rw [ho 132 (by unfold flashLoanCallbackSize; omega)]; change _ < 2^256; omega)
      (by jump_dest) ha1 rd1 with ⟨hn, _⟩ | ⟨_, aw2, k2, C2, hC2, ha2, rd2⟩
  · exact False.elim (hn hc)
  have he1 : 132 + (32 + 32 * tn.toNat) = 164 + 32 * tn.toNat := by omega
  simp only [wordAddNat_add, he1, List.cons_append, List.nil_append] at rd2
  have rd3 := midnightBlocks.midnight_block_16326
    (by change R.length + 1 + 1 + 1 + 1 + 17 ≤ 1024; omega) (by jump_dest) rd2
  simp only [midnightBlocks.midnight_block_16326_stack,
    midnightBlocks.midnight_block_16326_memory, word_add_sub_left] at rd3
  have hd1 : UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat (164 + 32 * tn.toNat) =
      UInt256.ofNat (160 + 32 * tn.toNat) := by
    have hh : UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat 164 = UInt256.ofNat 160 :=
      by decide +kernel
    rw [← wordAddNat_add, hh]
    apply u256_inj
    simp only [uadd_toNat, ofNat_toNat_mod, Nat.add_mod_mod, Nat.mod_add_mod]
  rw [hd1] at rd3
  have ha3 := memoryFundingAt (credit := credit + 4) rd3 (by memory_fund ha2)
  obtain ⟨aw4, k4, C4, hC4, ha4, rd4⟩ := midnightCalldataWordArrayEncoderFunded
    (by simp only [List.length_cons]; omega) han
    (by rw [ho (164 + 32 * tn.toNat) (by unfold flashLoanCallbackSize; omega)]
        change _ < 2^256; omega) (by jump_dest) ha3 rd3
  have he2 : 164 + 32 * tn.toNat + (32 + 32 * an.toNat) =
      196 + 32 * tn.toNat + 32 * an.toNat := by omega
  simp only [wordAddNat_add, he2] at rd4
  have rd5 := midnightBlocks.midnight_block_16345
    (by simp only [List.length_cons]; omega) (by jump_dest) rd4
  simp only [midnightBlocks.midnight_block_16345_stack,
    midnightBlocks.midnight_block_16345_memory, word_add_sub_left] at rd5
  have hd2 : UInt256.lnot (UInt256.ofNat 3) +
      UInt256.ofNat (196 + 32 * tn.toNat + 32 * an.toNat) =
      UInt256.ofNat (192 + 32 * tn.toNat + 32 * an.toNat) := by
    have hh : UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat 196 = UInt256.ofNat 192 :=
      by decide +kernel
    rw [← wordAddNat_add, ← wordAddNat_add, hh, wordAddNat_add]
    apply u256_inj
    simp only [uadd_toNat, ofNat_toNat_mod, Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_assoc]
  rw [hd2] at rd5
  have ha5 := memoryFundingAt (credit := credit + 4) rd5 (by memory_fund ha4)
  obtain ⟨aw6, k6, C6, hC6, ha6, rd6⟩ := midnightCalldataBytesEncoderFunded
    (by simp only [List.length_cons]; omega) hdl
    (by rw [ho (196 + 32 * tn.toNat + 32 * an.toNat)
          (by unfold flashLoanCallbackSize; omega)]; change _ < 2^256; omega)
    (by jump_dest) ha5 rd5
  simp only [wordAddNat_add] at rd6
  have rd7 := midnightBlocks.midnight_block_16363
    (by simp only [List.length_cons]; omega) rd6
  simp only [midnightBlocks.midnight_block_16363_stack, word_add_sub_left] at rd7
  have ha7 := memoryFundingAt (credit := credit + 4) rd7 (by memory_fund ha6)
  have hf := And.intro ha7 rd7
  have hsel : UInt256.shiftLeft (UInt256.ofNat 3522322627) (UInt256.ofNat 224) =
      UInt256.ofNat (3522322627 * 2^224) := by decide +kernel
  simp only [hsel, ho 4 (by unfold flashLoanCallbackSize; omega),
    ho 36 (by unfold flashLoanCallbackSize; omega), ho 68 (by unfold flashLoanCallbackSize; omega),
    ho 100 (by unfold flashLoanCallbackSize; omega), ho 132 (by unfold flashLoanCallbackSize; omega),
    ho (164 + 32 * tn.toNat) (by unfold flashLoanCallbackSize; omega),
    ho (196 + 32 * tn.toNat + 32 * an.toNat) (by unfold flashLoanCallbackSize; omega)] at hf
  refine ⟨_, _, _, _, ?_, by
    simpa only [flashLoanCallbackMemory, flashLoanCallbackSize, Reasoning.Theory.writeWord,
      Nat.add_assoc, List.cons_append, List.nil_append] using hf⟩
  omega

end Benchmarks.Midnight
