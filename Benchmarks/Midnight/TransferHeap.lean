import Benchmarks.Midnight.SafeTransferFunding

/-! The memory invariant preserved by repeated safe-transfer calls. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def transferHeapCredit (ptr : UInt256) : Nat :=
  4 * ((ptr.toNat + 160 + 31) / 32) - 999921

theorem transferHeapCredit_small {ptr : UInt256} (h : ptr.toNat ≤ 3200000) :
    transferHeapCredit ptr = 0 := by
  unfold transferHeapCredit
  omega

structure TransferHeap (mem : ByteArray) (aw ptr : UInt256) (spent : Nat) : Prop where
  size : 128 ≤ mem.size
  lower : 128 ≤ ptr.toNat
  free : memLoad (UInt256.ofNat 64) mem = ptr
  zero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩
  covered : ptr.toNat ≤ 32 * aw.toNat
  aligned : ptr.toNat % 32 = 0
  funding : MemoryFunding (transferHeapCredit ptr) mem aw spent

theorem TransferHeap.mono {mem aw ptr spent spent'}
    (h : TransferHeap mem aw ptr spent) (hle : spent ≤ spent') :
    TransferHeap mem aw ptr spent' :=
  { h with funding := h.funding.mono hle }

theorem transferHeapCredit_grows {ptr ptr' : UInt256} {work : Nat}
    (h : ptr.toNat ≤ ptr'.toNat) (ha : ptr.toNat % 32 = 0) (ha' : ptr'.toNat % 32 = 0)
    (hw : 4 * ((ptr'.toNat - ptr.toNat) / 32) ≤ work) :
    transferHeapCredit ptr' ≤ transferHeapCredit ptr + work := by
  unfold transferHeapCredit
  omega

theorem safeTransferHeap (isFrom : Bool) (imms : Store)
    {I : ExecutionEnv} {g : UInt256} {s0 evm : State} {mem rdata : ByteArray}
    {aw ptr ret : UInt256} {σ : AccountMap} {k C : Nat}
    {token sender recipient : AccountAddress} {value : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024) (hh : TransferHeap mem aw ptr C)
    (hgas : midnightGasBound g) (hfork : I.fork ≥ .osaka)
    (hs : SourceState s0 I σ evm)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 (safeTransferEntryPC isFrom)
      (safeTransferEntryStack isFrom token sender recipient value (ret :: R))
      mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecFuncBody config (safeTransferFrame isFrom imms token sender recipient value) evm
      (safeTransferFunctionFor isFrom).body .reverted ∧
      RDrev midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ (evm' : State) (σ' : AccountMap) (out mem' : ByteArray) (ptr' aw' : UInt256) (k' C' : Nat),
      ExecFuncBody config (safeTransferFrame isFrom imms token sender recipient value) evm
        (safeTransferFunctionFor isFrom).body
        (.returned (safeTransferCallFrame isFrom imms token sender recipient value true out) evm'
          none) ∧
      SourceState s0 I σ' evm' ∧ MemoryPrefix mem mem' ptr.toNat ∧
      ptr.toNat ≤ ptr'.toNat ∧ TransferHeap mem' aw' ptr' C' ∧
      RD midnightBytecode I (Sat256.ofUInt256 g) s0 ret R mem' aw' out σ' k' C' := by
  have hcredit : 4 * ((ptr.toNat + safeTransferCallAllocation isFrom + 31) / 32) ≤
      transferHeapCredit ptr + 999921 := by
    have ha : safeTransferCallAllocation isFrom ≤ 160 := by cases isFrom <;> decide
    unfold transferHeapCredit
    omega
  rcases safeTransferFundedPreserving isFrom imms hstack hh.size hh.lower hh.free hh.zero
      hh.funding hh.covered hh.aligned hcredit hgas hfork hs hret rd with
    hoog | hrev | hsuccess
  · exact Or.inl hoog
  · exact Or.inr (Or.inl hrev)
  · obtain ⟨evm', σ', out, mem', ptr', aw', k', C', hb, hs', hp, hf, hz, hl, _, ha,
        hcover, halign, hwork, rd'⟩ := hsuccess
    refine Or.inr (Or.inr ⟨evm', σ', out, mem', ptr', aw', k', C', hb, hs', hp, hl, ?_, rd'⟩)
    exact ⟨hh.size.trans hp.size, hh.lower.trans hl, hf, hz, hcover, halign,
      ha.weaken (transferHeapCredit_grows hl hh.aligned halign hwork)⟩

end Benchmarks.Midnight
