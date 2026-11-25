import Benchmarks.Midnight.LiquidatorGateABI
import Benchmarks.Midnight.SafeTransferMemory
import Benchmarks.Midnight.ByteCopyMemory

/-! The gate's fixed call and return buffers preserve the decoded market and reserved words. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def liquidatorGateCallMemory (mem : ByteArray) (root : UInt256) (caller : AccountAddress) :
    ByteArray := staticWordCallMem liquidatorGateSelectorWord [UInt256.ofNat caller.val]
      mem root.toNat

def liquidatorGateReplyMemory (mem : ByteArray) (root : UInt256) (caller : AccountAddress)
    (out : ByteArray) : ByteArray :=
  out.write 0 (liquidatorGateCallMemory mem root caller) root.toNat 32

def liquidatorGateResultMemory (mem : ByteArray) (root : UInt256) (caller : AccountAddress)
    (out : ByteArray) : ByteArray :=
  writeWord (liquidatorGateReplyMemory mem root caller out) 64 (root + UInt256.ofNat 32)

theorem liquidatorGateCallMemory_size (mem : ByteArray) (root : UInt256)
    (caller : AccountAddress) :
    (liquidatorGateCallMemory mem root caller).size = max mem.size (root.toNat + 36) := by
  rw [liquidatorGateCallMemory, staticWordCallMem_size _ _ _ _ (by simp)]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.add_assoc]

theorem liquidatorGateCallMemory_read (mem : ByteArray) (root : UInt256)
    (caller : AccountAddress) :
    (liquidatorGateCallMemory mem root caller).readWithPadding root.toNat 36 =
      liquidatorGateCalldata caller := by
  have h := staticWordCallMem_read liquidatorGateSelectorWord [UInt256.ofNat caller.val]
    mem root.toNat (by simp)
  simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul,
    liquidatorGateSelectorWord_bytes, wordArrayBytes, ByteArray.append_empty] using h

theorem liquidatorGateCallMemory_prefix (mem : ByteArray) (root : UInt256)
    (caller : AccountAddress) :
    MemoryPrefix mem (liquidatorGateCallMemory mem root caller) root.toNat :=
  staticWordCallMem_prefix _ _ _ _ _ le_rfl

theorem liquidatorGateReplyMemory_size (mem : ByteArray) (root : UInt256)
    (caller : AccountAddress) {out : ByteArray} (h32 : 32 ≤ out.size) :
    (liquidatorGateReplyMemory mem root caller out).size =
      max mem.size (root.toNat + 36) := by
  rw [liquidatorGateReplyMemory, copySparse_size _ _ _ _ _ (by decide) h32,
    liquidatorGateCallMemory_size]
  omega

theorem liquidatorGateReplyMemory_prefix (mem : ByteArray) (root : UInt256)
    (caller : AccountAddress) {out : ByteArray} (h32 : 32 ≤ out.size) :
    MemoryPrefix mem (liquidatorGateReplyMemory mem root caller out) root.toNat := by
  refine (liquidatorGateCallMemory_prefix mem root caller).trans ⟨?_, ?_⟩
  · rw [liquidatorGateReplyMemory_size _ _ _ h32, liquidatorGateCallMemory_size]
  · intro off _ hlim hin
    exact copySparse_read_before out _ 0 root.toNat 32 off 32 (by decide) h32
      (by decide) hin hlim

theorem liquidatorGateResultMemory_properties (mem : ByteArray) (root : UInt256)
    (caller : AccountAddress) {out : ByteArray} (h32 : 32 ≤ out.size)
    (hroot : 96 ≤ root.toNat) :
    (liquidatorGateResultMemory mem root caller out).size = max mem.size (root.toNat + 36) ∧
      memLoad (UInt256.ofNat 64) (liquidatorGateResultMemory mem root caller out) =
        root + UInt256.ofNat 32 ∧
      memLoad root (liquidatorGateResultMemory mem root caller out) = calldataWord out 0 ∧
      MemoryPrefix mem (liquidatorGateResultMemory mem root caller out) root.toNat := by
  have hs := liquidatorGateReplyMemory_size mem root caller h32
  refine ⟨?_, memLoad_writeWord _ (UInt256.ofNat 64) _, ?_,
    (liquidatorGateReplyMemory_prefix mem root caller h32).trans
      (memoryPrefix_writeWord _ 64 root.toNat _ (Or.inr (by decide)))⟩
  · rw [liquidatorGateResultMemory, writeWord_sparse_size, hs]
    omega
  · rw [liquidatorGateResultMemory, memLoad_writeWord_preserved _ _ _ _
      (by rw [hs]; omega) (Or.inr hroot)]
    apply mloadWordValue_of_readWithPadding (by rw [hs]; omega)
    have hr := copySparse_read out (liquidatorGateCallMemory mem root caller)
      0 root.toNat 32 0 32 h32 (by decide) (by decide)
    rw [calldataWord_bytes h32]
    simpa only [Nat.add_zero, Nat.zero_add,
      readWithPadding_eq_extract_unbounded out 0 32 (by decide) h32] using hr

end Benchmarks.Midnight
