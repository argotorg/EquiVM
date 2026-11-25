import Benchmarks.Midnight.FlashLoanTransferRuntime
import Benchmarks.Midnight.TransferHeap

variable {fork : Ethereum.Fork}

/-! One token transfer preserves the flash-loan loop's heap and source state. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightFlashLoanTransferStep (isFrom : Bool) (imms : Store) {I : ExecutionEnv} {g : UInt256}
    {s0 evm : State} {mem rdata : ByteArray} {aw ptr index tn tp an ap dl dp : UInt256}
    {callback : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 24 ≤ 1024) (ht : index.toNat < tn.toNat) (ha : index.toNat < an.toNat)
    (hc : (calldataWord I.calldata (calldataIndex tp index).toNat).toNat < EVM.addressModulus)
    (hh : TransferHeap mem aw ptr C) (hgas : midnightGasBound g) (hfork : fork ≥ .osaka)
    (hs : SourceState s0 I σ evm)
    (rd : RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 (flashLoanTransferLoopPC isFrom)
      (flashLoanTransferLoopStack isFrom index tn tp (UInt256.ofNat callback.val) an ap dl dp ++ R)
      mem aw rdata σ k C) :
    let token := flashLoanTokenAt I.calldata tp index
    let value := flashLoanAssetAt I.calldata ap index
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecFuncBody fork config (safeTransferFrame isFrom imms token
        (if isFrom then callback else I.source) (if isFrom then I.codeOwner else callback) value) evm
      (safeTransferFunctionFor isFrom).body .reverted ∧
      RDrev fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ (evm' : State) (σ' : AccountMap) (out mem' : ByteArray) (ptr' aw' : UInt256) (k' C' : Nat),
      ExecFuncBody fork config (safeTransferFrame isFrom imms token
        (if isFrom then callback else I.source) (if isFrom then I.codeOwner else callback) value) evm
        (safeTransferFunctionFor isFrom).body
        (.returned (safeTransferCallFrame isFrom imms token
            (if isFrom then callback else I.source) (if isFrom then I.codeOwner else callback)
            value true out)
          evm' none) ∧
      SourceState s0 I σ' evm' ∧ MemoryPrefix mem mem' ptr.toNat ∧
      ptr.toNat ≤ ptr'.toNat ∧ TransferHeap mem' aw' ptr' C' ∧
      RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 (flashLoanTransferLoopPC isFrom)
        (flashLoanTransferLoopStack isFrom (index + ⟨1⟩) tn tp (UInt256.ofNat callback.val) an ap dl dp ++ R)
        mem' aw' out σ' k' C' := by
  obtain ⟨k1, C1, hC1, rd1⟩ := midnightFlashLoanTransferPrepare isFrom (by omega) ht ha hc rd
  rcases safeTransferHeap isFrom imms
      (R := flashLoanTransferTail isFrom index tn tp (UInt256.ofNat callback.val) an ap dl dp ++ R)
      (by
        cases isFrom <;>
          simp only [flashLoanTransferTail, flashLoanInTransferTail, flashLoanOutTransferTail,
            Bool.false_eq_true, if_false, if_true, List.length_append, List.length_cons,
            List.length_nil] <;> omega)
      (hh.mono hC1) hgas hfork hs
      (by cases isFrom <;> unfold flashLoanTransferReturnPC <;> jump_dest) rd1 with
    hoog | hrev | hsuccess
  · exact Or.inl hoog
  · exact Or.inr (Or.inl hrev)
  · obtain ⟨evm', σ', out, mem', ptr', aw', k2, C2, hb, hs', hp, hl, hh', rd2⟩ := hsuccess
    obtain ⟨k3, C3, hC3, rd3⟩ := midnightFlashLoanTransferReturn isFrom (by omega) rd2
    exact Or.inr (Or.inr ⟨evm', σ', out, mem', ptr', aw', k3, C3,
      hb, hs', hp, hl, hh'.mono hC3, rd3⟩)

end Benchmarks.Midnight
