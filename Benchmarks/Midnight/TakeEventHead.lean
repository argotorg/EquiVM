import Benchmarks.Midnight.TakeEventArithmetic
import Benchmarks.Midnight.MemoryBytesEncodeMemory
import Benchmarks.Midnight.RuntimeBlocks_048

/-! The fixed prefix of the trade event's ABI buffer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takeEventHeadMemory (mem : ByteArray) (root caller hash buy group ratifier : UInt256) :
    ByteArray :=
  writeWordArray mem root.toNat [caller, hash, buy, group, ratifier, ⟨480⟩]

theorem takeEventHeadMemory_prefix (mem : ByteArray)
    (root caller hash buy group ratifier : UInt256) :
    MemoryPrefix mem (takeEventHeadMemory mem root caller hash buy group ratifier) root.toNat :=
  memoryPrefix_writeWordArray _ _ _ _ le_rfl

theorem takeEventHeadMemory_load (mem : ByteArray)
    (root caller hash buy group ratifier read : UInt256)
    (hin : read.toNat + 32 ≤ mem.size) (hlo : read.toNat + 32 ≤ root.toNat) :
    memLoad read (takeEventHeadMemory mem root caller hash buy group ratifier) =
      memLoad read mem := memLoad_writeWordArray_below _ _ _ _ hin hlo

set_option maxRecDepth 10000

theorem midnightTakeEventHead {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root group ratifier ptr buy difference maker hash : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 11 ≤ 1024)
    (hb : root.toNat + 192 < UInt256.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = root) (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨12921⟩
      ([group, ratifier, ptr, buy, difference, maker, hash] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C',
      MemoryFunding credit
        (takeEventHeadMemory mem root (UInt256.ofNat I.source.val) hash buy group ratifier) aw' C' ∧
      RD midnightBytecode I g s0 ⟨20095⟩
        ([ptr, root + UInt256.ofNat 480, ⟨12970⟩, difference, maker, root] ++ R)
        (takeEventHeadMemory mem root (UInt256.ofNat I.source.val) hash buy group ratifier)
        aw' rdata σ k' C' := by
  simp only [List.cons_append, List.nil_append] at rd
  have rd1 := midnightBlocks.midnight_block_12921 hstack (by jump_dest) rd
  have ha1 := memoryFundingAt (credit := credit) rd1 (by
    unfold midnightBlocks.midnight_block_12921_memory
    memory_fund ha)
  have hmem : midnightBlocks.midnight_block_12921_memory (ee := I) (mem := mem)
      (x0 := group) (x1 := ratifier) (x3 := buy) (x6 := hash) =
      takeEventHeadMemory mem root (UInt256.ofNat I.source.val) hash buy group ratifier := by
    simp only [midnightBlocks.midnight_block_12921_memory, hfree, takeEventHeadMemory,
      writeWordArray, Reasoning.Theory.writeWord,
      uadd_word_ofNat_toNat root 32 (by omega), uadd_word_ofNat_toNat root 64 (by omega),
      uadd_word_ofNat_toNat root 96 (by omega), uadd_word_ofNat_toNat root 128 (by omega),
      uadd_word_ofNat_toNat root 160 (by omega), Nat.add_assoc]
    rfl
  rw [hmem] at rd1 ha1
  simp only [midnightBlocks.midnight_block_12921_stack, hfree] at rd1 ha1
  exact ⟨_, _, _, ha1, rd1⟩

end Benchmarks.Midnight
