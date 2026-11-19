import Benchmarks.Midnight.FlashLoanTransferStep

/-! One outgoing transfer preserves the flash-loan loop's heap and source state. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem midnightFlashLoanOutStep (imms : Store) {I : ExecutionEnv} {g : UInt256}
    {s0 evm : State} {mem rdata : ByteArray} {aw ptr index tn tp an ap dl dp : UInt256}
    {callback : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 24 ≤ 1024) (ht : index.toNat < tn.toNat) (ha : index.toNat < an.toNat)
    (hc : (calldataWord I.calldata (calldataIndex tp index).toNat).toNat < EVM.addressModulus)
    (hh : TransferHeap mem aw ptr C) (hgas : midnightGasBound g) (hfork : I.fork ≥ .osaka)
    (hs : SourceState s0 I σ evm)
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨16258⟩
      (flashLoanOutLoopStack index tn tp (UInt256.ofNat callback.val) an ap dl dp ++ R)
      mem aw rdata σ k C) :
    let token := flashLoanTokenAt I.calldata tp index
    let value := flashLoanAssetAt I.calldata ap index
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecFuncBody config (safeTransferFrame false imms token I.source callback value) evm
      (safeTransferFunctionFor false).body .reverted ∧
      RDrev midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ (evm' : State) (σ' : AccountMap) (out mem' : ByteArray) (ptr' aw' : UInt256) (k' C' : Nat),
      ExecFuncBody config (safeTransferFrame false imms token I.source callback value) evm
        (safeTransferFunctionFor false).body
        (.returned (safeTransferCallFrame false imms token I.source callback value true out)
          evm' none) ∧
      SourceState s0 I σ' evm' ∧ MemoryPrefix mem mem' ptr.toNat ∧
      ptr.toNat ≤ ptr'.toNat ∧ TransferHeap mem' aw' ptr' C' ∧
      RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨16258⟩
        (flashLoanOutLoopStack (index + ⟨1⟩) tn tp (UInt256.ofNat callback.val) an ap dl dp ++ R)
        mem' aw' out σ' k' C' := by
  exact midnightFlashLoanTransferStep false imms hstack ht ha hc hh hgas hfork hs rd

end Benchmarks.Midnight
