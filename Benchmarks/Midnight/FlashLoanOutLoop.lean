import Benchmarks.Midnight.FlashLoanOutStep
import Benchmarks.Midnight.FlashLoanTransferLoop

variable {fork : Ethereum.Fork}

/-! The outgoing flash-loan transfer loop, including any failing token call. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem midnightFlashLoanOutLoop (remaining : Nat) {I : ExecutionEnv} {g : UInt256}
    {s0 evm : State} {frame : Frame} {mem rdata : ByteArray}
    {aw ptr index tn tp an ap dl dp : UInt256} {callback : AccountAddress} {data : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 24 ≤ 1024) (hn : tn.toNat = index.toNat + remaining)
    (hlen : an.toNat = tn.toNat) (hcount : tn.toNat < 2 ^ 64)
    (htspan : tp.toNat + 32 * tn.toNat < UInt256.size)
    (haspan : ap.toNat + 32 * an.toNat < UInt256.size)
    (hc : CanonicalAddressWords (calldataArrayWords I.calldata tn.toNat tp.toNat))
    (hf : FlashLoanSourceFrame frame (calldataArrayWords I.calldata tn.toNat tp.toNat)
      (calldataArrayWords I.calldata an.toNat ap.toNat) callback data)
    (hi : frame.locals.get? "i" = some (.int (Int.ofNat index.toNat)))
    (hh : TransferHeap mem aw ptr C) (hgas : midnightGasBound g) (hfork : fork ≥ .osaka)
    (hs : SourceState s0 I σ evm)
    (rd : RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨16258⟩
      (flashLoanOutLoopStack index tn tp (UInt256.ofNat callback.val) an ap dl dp ++ R)
      mem aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecForLoop fork config frame evm flashLoanLoopCondition flashLoanLoopPost (flashLoanLoopBody false)
      .reverted ∧ RDrev fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ (frame' : Frame) (evm' : State) (σ' : AccountMap) (mem' rdata' : ByteArray)
      (aw' ptr' : UInt256) (k' C' : Nat),
      ExecForLoop fork config frame evm flashLoanLoopCondition flashLoanLoopPost (flashLoanLoopBody false)
        (.ok frame' evm') ∧
      SourceState s0 I σ' evm' ∧ TransferHeap mem' aw' ptr' C' ∧
      FlashLoanSourceFrame frame' (calldataArrayWords I.calldata tn.toNat tp.toNat)
        (calldataArrayWords I.calldata an.toNat ap.toNat) callback data ∧
      RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨16266⟩
        (flashLoanOutLoopStack tn tn tp (UInt256.ofNat callback.val) an ap dl dp ++ R)
        mem' aw' rdata' σ' k' C' := by
  exact midnightFlashLoanTransferLoop false remaining hstack hn hlen hcount htspan haspan
    hc hf hi hh hgas hfork hs rd

end Benchmarks.Midnight
