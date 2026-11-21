import Benchmarks.Midnight.FlashLoanOutTransfer
import Benchmarks.Midnight.FlashLoanInTransfer
import Benchmarks.Midnight.SafeTransferPrepare

/-! The common runtime interface for outgoing transfers and incoming repayments. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def flashLoanTokenAt (bytes : ByteArray) (ptr index : UInt256) : AccountAddress :=
  AccountAddress.ofUInt256 (calldataWord bytes (calldataIndex ptr index).toNat)

def flashLoanAssetAt (bytes : ByteArray) (ptr index : UInt256) : UInt256 :=
  calldataWord bytes (calldataIndex ptr index).toNat

def flashLoanTransferLoopPC (isFrom : Bool) : UInt256 :=
  if isFrom then ⟨16403⟩ else ⟨16258⟩

def flashLoanTransferReturnPC (isFrom : Bool) : UInt256 :=
  if isFrom then ⟨16453⟩ else ⟨16580⟩

def flashLoanTransferExitPC (isFrom : Bool) : UInt256 :=
  if isFrom then ⟨16411⟩ else ⟨16266⟩

def flashLoanTransferLoopStack (isFrom : Bool) (index tn tp callback an ap dl dp : UInt256) :
    List UInt256 :=
  if isFrom then flashLoanInLoopStack index tn tp callback an ap
  else flashLoanOutLoopStack index tn tp callback an ap dl dp

def flashLoanTransferTail (isFrom : Bool) (index tn tp callback an ap dl dp : UInt256) :
    List UInt256 :=
  if isFrom then flashLoanInTransferTail index tn tp callback an ap
  else flashLoanOutTransferTail index tn tp callback an ap dl dp

theorem midnightFlashLoanTransferPrepare (isFrom : Bool) {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw index tn tp an ap dl dp : UInt256}
    {callback : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 20 ≤ 1024) (ht : index.toNat < tn.toNat) (ha : index.toNat < an.toNat)
    (hc : (calldataWord I.calldata (calldataIndex tp index).toNat).toNat < EVM.addressModulus)
    (rd : RD midnightBytecode I g s0 (flashLoanTransferLoopPC isFrom)
      (flashLoanTransferLoopStack isFrom index tn tp (UInt256.ofNat callback.val) an ap dl dp ++ R)
      mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD midnightBytecode I g s0 (safeTransferEntryPC isFrom)
      (safeTransferEntryStack isFrom (flashLoanTokenAt I.calldata tp index)
        (if isFrom then callback else I.source) (if isFrom then I.codeOwner else callback)
        (flashLoanAssetAt I.calldata ap index)
        (flashLoanTransferReturnPC isFrom ::
          flashLoanTransferTail isFrom index tn tp (UInt256.ofNat callback.val) an ap dl dp ++ R))
      mem aw rdata σ k' C' := by
  have htoken : UInt256.ofNat (flashLoanTokenAt I.calldata tp index).val =
      calldataWord I.calldata (calldataIndex tp index).toNat :=
    word_of_addressOfUInt256_of_canonical _ hc
  cases isFrom with
  | false =>
    simpa only [safeTransferEntryPC, safeTransferEntryStack, safeTransferCallWords,
      flashLoanTransferReturnPC, flashLoanTransferTail, Bool.false_eq_true, if_false,
      htoken, flashLoanAssetAt, List.cons_append, List.nil_append] using
      midnightFlashLoanOutTransferPrepare hstack ht ha hc rd
  | true =>
    simpa only [safeTransferEntryPC, safeTransferEntryStack, safeTransferCallWords,
      flashLoanTransferReturnPC, flashLoanTransferTail, if_true,
      htoken, flashLoanAssetAt, List.cons_append, List.nil_append] using
      midnightFlashLoanInTransferPrepare (by omega) ht ha hc rd

theorem midnightFlashLoanTransferReturn (isFrom : Bool) {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw index tn tp callback an ap dl dp : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 13 ≤ 1024)
    (rd : RD midnightBytecode I g s0 (flashLoanTransferReturnPC isFrom)
      (flashLoanTransferTail isFrom index tn tp callback an ap dl dp ++ R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD midnightBytecode I g s0 (flashLoanTransferLoopPC isFrom)
      (flashLoanTransferLoopStack isFrom (index + ⟨1⟩) tn tp callback an ap dl dp ++ R)
      mem aw rdata σ k' C' := by
  cases isFrom with
  | false => exact midnightFlashLoanOutTransferReturn hstack rd
  | true => exact midnightFlashLoanInTransferReturn (by omega) rd

theorem midnightFlashLoanTransferExit (isFrom : Bool) {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw tn tp callback an ap dl dp : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 24 ≤ 1024)
    (rd : RD midnightBytecode I g s0 (flashLoanTransferLoopPC isFrom)
      (flashLoanTransferLoopStack isFrom tn tn tp callback an ap dl dp ++ R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD midnightBytecode I g s0 (flashLoanTransferExitPC isFrom)
      (flashLoanTransferLoopStack isFrom tn tn tp callback an ap dl dp ++ R) mem aw rdata σ k' C' := by
  cases isFrom with
  | false =>
    have rd1 := midnightBlocks.midnight_block_16258_fallthrough
      (by change R.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 6 ≤ 1024; omega)
      (ult_zero (by omega)) rd
    exact ⟨_, _, by omega, rd1⟩
  | true =>
    have rd1 := midnightBlocks.midnight_block_16403_fallthrough
      (by change R.length + 8 ≤ 1024; omega) (ult_zero (by omega)) rd
    exact ⟨_, _, by omega, rd1⟩

end Benchmarks.Midnight
