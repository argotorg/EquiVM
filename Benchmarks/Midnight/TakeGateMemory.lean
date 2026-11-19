import Benchmarks.Midnight.TakeGateABI
import Benchmarks.Midnight.SafeTransferMemory
import Benchmarks.Midnight.ByteCopyMemory

/-! Fixed buffers for the entry-gate calls and their Boolean replies. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takeGateCallMemory (kind : TakeGateKind) (mem : ByteArray) (root : UInt256)
    (user : AccountAddress) : ByteArray :=
  staticWordCallMem kind.selectorWord [UInt256.ofNat user.val] mem root.toNat

def takeGateReplyMemory (kind : TakeGateKind) (mem : ByteArray) (root : UInt256)
    (user : AccountAddress) (out : ByteArray) : ByteArray :=
  out.write 0 (takeGateCallMemory kind mem root user) root.toNat 32

def takeGateResultMemory (kind : TakeGateKind) (mem : ByteArray) (root : UInt256)
    (user : AccountAddress) (out : ByteArray) : ByteArray :=
  writeWord (takeGateReplyMemory kind mem root user out) 64 (root + UInt256.ofNat 32)

theorem takeGateCallMemory_size (kind : TakeGateKind) (mem : ByteArray) (root : UInt256)
    (user : AccountAddress) :
    (takeGateCallMemory kind mem root user).size = max mem.size (root.toNat + 36) := by
  rw [takeGateCallMemory, staticWordCallMem_size _ _ _ _ (by simp)]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.add_assoc]

theorem takeGateCallMemory_read (kind : TakeGateKind) (mem : ByteArray) (root : UInt256)
    (user : AccountAddress) :
    (takeGateCallMemory kind mem root user).readWithPadding root.toNat 36 =
      takeGateCalldata kind user := by
  have h := staticWordCallMem_read kind.selectorWord [UInt256.ofNat user.val] mem root.toNat
    (by simp)
  simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul,
    TakeGateKind.selectorWord_bytes, wordArrayBytes, ByteArray.append_empty] using h

theorem takeGateCallMemory_prefix (kind : TakeGateKind) (mem : ByteArray) (root : UInt256)
    (user : AccountAddress) : MemoryPrefix mem (takeGateCallMemory kind mem root user) root.toNat :=
  staticWordCallMem_prefix _ _ _ _ _ le_rfl

theorem takeGateReplyMemory_size (kind : TakeGateKind) (mem : ByteArray) (root : UInt256)
    (user : AccountAddress) {out : ByteArray} (h32 : 32 ≤ out.size) :
    (takeGateReplyMemory kind mem root user out).size = max mem.size (root.toNat + 36) := by
  rw [takeGateReplyMemory, copySparse_size _ _ _ _ _ (by decide) h32, takeGateCallMemory_size]
  omega

theorem takeGateReplyMemory_prefix (kind : TakeGateKind) (mem : ByteArray) (root : UInt256)
    (user : AccountAddress) {out : ByteArray} (h32 : 32 ≤ out.size) :
    MemoryPrefix mem (takeGateReplyMemory kind mem root user out) root.toNat := by
  refine (takeGateCallMemory_prefix kind mem root user).trans ⟨?_, ?_⟩
  · rw [takeGateReplyMemory_size _ _ _ _ h32, takeGateCallMemory_size]
  · intro off _ hlim hin
    exact copySparse_read_before out _ 0 root.toNat 32 off 32 (by decide) h32 (by decide) hin hlim

theorem takeGateResultMemory_properties (kind : TakeGateKind) (mem : ByteArray) (root : UInt256)
    (user : AccountAddress) {out : ByteArray} (h32 : 32 ≤ out.size) (hroot : 96 ≤ root.toNat) :
    (takeGateResultMemory kind mem root user out).size = max mem.size (root.toNat + 36) ∧
      memLoad (UInt256.ofNat 64) (takeGateResultMemory kind mem root user out) =
        root + UInt256.ofNat 32 ∧
      memLoad root (takeGateResultMemory kind mem root user out) = calldataWord out 0 ∧
      MemoryPrefix mem (takeGateResultMemory kind mem root user out) root.toNat := by
  have hs := takeGateReplyMemory_size kind mem root user h32
  refine ⟨?_, memLoad_writeWord _ (UInt256.ofNat 64) _, ?_,
    (takeGateReplyMemory_prefix kind mem root user h32).trans
      (memoryPrefix_writeWord _ 64 root.toNat _ (Or.inr (by decide)))⟩
  · rw [takeGateResultMemory, writeWord_sparse_size, hs]
    omega
  · rw [takeGateResultMemory, memLoad_writeWord_preserved _ _ _ _
      (by rw [hs]; omega) (Or.inr hroot)]
    apply mloadWordValue_of_readWithPadding (by rw [hs]; omega)
    have hr := copySparse_read out (takeGateCallMemory kind mem root user)
      0 root.toNat 32 0 32 h32 (by decide) (by decide)
    rw [calldataWord_bytes h32]
    simpa only [Nat.add_zero, Nat.zero_add,
      readWithPadding_eq_extract_unbounded out 0 32 (by decide) h32] using hr

end Benchmarks.Midnight
