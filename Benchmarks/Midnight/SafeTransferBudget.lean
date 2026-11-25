import Benchmarks.Midnight.SafeTransfer
import Benchmarks.Midnight.SafeTransferFunding
import Benchmarks.Midnight.TransferBudget

variable {fork : Ethereum.Fork}

/-! A common transfer interface for small heaps and heaps funded by market encoding. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem safeTransferBudgeted (isFrom : Bool) (imms : Store) {credit : Nat}
    {I : ExecutionEnv} {g : UInt256} {s0 evm : State} {mem rdata : ByteArray}
    {aw ptr ret : UInt256} {σ : AccountMap} {k C : Nat}
    {token sender recipient : AccountAddress} {value : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024) (hm : 128 ≤ mem.size) (hl : 128 ≤ ptr.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hbudget : TransferBudget ptr credit mem aw C) (hused : ptr.toNat ≤ mem.size)
    (hcredit : 4 * ((ptr.toNat + safeTransferCallAllocation isFrom + 31) / 32) ≤
      credit + 999921)
    (hgas : midnightGasBound g) (hfork : fork ≥ .osaka)
    (hs : SourceState s0 I σ evm)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 (safeTransferEntryPC isFrom)
      (safeTransferEntryStack isFrom token sender recipient value (ret :: R))
      mem aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecFuncBody fork config (safeTransferFrame isFrom imms token sender recipient value) evm
      (safeTransferFunctionFor isFrom).body .reverted ∧
      RDrev fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ (evm' : State) (σ' : AccountMap) (out mem' : ByteArray) (ptr' aw' : UInt256) (k' C' : Nat),
      ExecFuncBody fork config (safeTransferFrame isFrom imms token sender recipient value) evm
        (safeTransferFunctionFor isFrom).body
        (.returned (safeTransferCallFrame isFrom imms token sender recipient value true out) evm'
          none) ∧
      SourceState s0 I σ' evm' ∧ MemoryPrefix mem mem' ptr.toNat ∧
      memLoad (UInt256.ofNat 64) mem' = ptr' ∧ memLoad (UInt256.ofNat 96) mem' = ⟨0⟩ ∧
      ptr.toNat ≤ ptr'.toNat ∧ ptr'.toNat < 2 ^ 64 ∧
      RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 ret R mem' aw' out σ' k' C' := by

  rcases hbudget with hsmall | ⟨halign, hfund⟩
  · apply safeTransferSmallHeap isFrom imms hstack hm hl hfree hzero _ hgas hfork hs hret rd
    have ha : safeTransferCallAllocation isFrom ≤ 160 := by cases isFrom <;> decide
    omega
  · exact safeTransferFunded isFrom imms hstack hm hl hfree hzero hfund
      (hused.trans hfund.covered) halign hcredit hgas hfork hs hret rd

end Benchmarks.Midnight
