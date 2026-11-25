import Benchmarks.Midnight.FlashLoanEventMemory
import Benchmarks.Midnight.RuntimeBlocks_060

variable {fork : Ethereum.Fork}

/-! Preparing the flash-loan event, with validation of every token address. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def flashLoanEventTopic : UInt256 :=
  UInt256.ofNat 26271614660902846776008755970087401779150335120009310310910965370553039763516

def flashLoanAfterEventStack (tn tp callback an ap dl dp : UInt256) : List UInt256 :=
  [dl, dp, tn, tp, callback, an, ap, callback, an, tp, tn]

theorem midnightFlashLoanEventEncode {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root tn tp callback an ap dl dp : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 32 ≤ 1024)
    (htn : tn.toNat < 2^64) (han : an.toNat < 2^64)
    (htp : tp.toNat + 32 * tn.toNat < UInt256.size)
    (hcallback : callback.toNat < EVM.addressModulus)
    (hroot : root.toNat < 2^128) (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (ha : MemoryAccounting mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨16162⟩
      (dp :: dl :: ap :: callback :: an :: tp :: tn :: R) mem aw rdata σ k C) :
    (¬ CanonicalAddressWords (calldataArrayWords I.calldata tn.toNat tp.toNat) ∧
      RDrev fork midnightBytecode g s0) ∨
    (CanonicalAddressWords (calldataArrayWords I.calldata tn.toNat tp.toNat) ∧
      ∃ aw' k' C', C ≤ C' ∧
      MemoryAccounting
        (flashLoanEventMemory mem I.calldata root.toNat tp.toNat tn.toNat ap.toNat an.toNat)
        aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨16253⟩
        ([root + UInt256.ofNat (128 + 32 * tn.toNat + 32 * an.toNat), root, root,
          flashLoanEventTopic, UInt256.ofNat I.source.val, callback] ++
          flashLoanAfterEventStack tn tp callback an ap dl dp ++ R)
        (flashLoanEventMemory mem I.calldata root.toNat tp.toNat tn.toNat ap.toNat an.toNat)
        aw' rdata σ k' C') := by
  have ho (n : Nat) (hn : n ≤ 128 + 32 * tn.toNat + 32 * an.toNat) :
      (root + UInt256.ofNat n).toNat = root.toNat + n :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have rd1 := midnightBlocks.midnight_block_16162 (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_16162_stack,
    midnightBlocks.midnight_block_16162_memory, hfree, addressMask_computed,
    solcAddrMask_clean hcallback] at rd1
  have ha1 := memoryAccountingAt rd1 (by memory_account ha)
  rcases midnightCalldataAddressEncoder
      (R := [⟨16253⟩, root, root, flashLoanEventTopic, ap, callback, dl, dp, tn, tp,
        callback, an, ap, callback, an, tp, tn] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      htp (by rw [ho 64 (by omega)]; change _ < 2^256; omega)
      (by jump_dest) ha1 rd1 with
    ⟨hn, hr⟩ | ⟨hc, aw2, k2, C2, hC2, ha2, rd2⟩
  · exact Or.inl ⟨hn, hr⟩
  have he : 64 + (32 + 32 * tn.toNat) = 96 + 32 * tn.toNat := by omega
  simp only [wordAddNat_add, he] at rd2
  have rd3 := midnightBlocks.midnight_block_16237
    (R := ap :: callback :: an :: tp :: tn :: R)
    (by simp only [List.length_cons]; omega)
    (by jump_dest) rd2
  simp only [midnightBlocks.midnight_block_16237_stack,
    midnightBlocks.midnight_block_16237_memory, word_add_sub_left] at rd3
  have ha3 := memoryAccountingAt rd3 (by memory_account ha2)
  obtain ⟨aw4, k4, C4, hC4, ha4, rd4⟩ := midnightCalldataWordArrayEncoder
    (R := [root, root, flashLoanEventTopic, UInt256.ofNat I.source.val, callback] ++
      flashLoanAfterEventStack tn tp callback an ap dl dp ++ R)
    (by simp only [flashLoanAfterEventStack, List.length_append, List.length_cons,
        List.length_nil]; omega)
    han (by rw [ho (96 + 32 * tn.toNat) (by omega)]; change _ < 2^256; omega)
    (by jump_dest) ha3 rd3
  have he' : 96 + 32 * tn.toNat + (32 + 32 * an.toNat) =
      128 + 32 * tn.toNat + 32 * an.toNat := by omega
  have hf := And.intro ha4 rd4
  simp only [wordAddNat_add, he', ho 64 (by omega), ho 32 (by omega),
    ho (96 + 32 * tn.toNat) (by omega)] at hf
  right
  refine ⟨hc, aw4, k4, C4, by omega, ?_⟩
  simpa only [flashLoanEventMemory, Nat.add_assoc] using hf

end Benchmarks.Midnight
