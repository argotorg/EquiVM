import Benchmarks.EAS.EAS.ResolveManyPaymentControl

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem resolveManyPayableEVM {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C i len : Nat}
    {array target values available last total value ptr : UInt256} {R : List UInt256}
    (v : EASImmutables) (rev : Bool) (hstack : R.length+20 ≤ 1024)
    (hs : SourceState s0 ee σ evm) (hheap : ptr.toNat ≤ 2^64-1) (hlo : 96 ≤ ptr.toNat)
    (hh : memLoad (UInt256.ofNat 64) mem = ptr)
    (rd : RD fork (deployedRuntime v) ee g s0 (payableEntryPC (resolveManyPayableSite rev))
      (⟨1⟩::resolveManyCheckedStack rev i array target values available last total value len R) mem aw rdata σ k C) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (success : Bool) (out : ByteArray),
      callViaEVM fork evm (AccountAddress.ofUInt256 target) 0 payablePayload (success,evm',out) false ∧
      SourceState s0 ee σ' evm' ∧ out.size < 2^138 ∧
      (if callBoolAccepted ptr.toNat success out then
        ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (payableCheckedPC (resolveManyPayableSite rev))
          (resolveManyCheckedStack rev i array target values available last total value len R)
          (payableOutputMemory mem ptr out) aw' out σ' k' C'
       else RDrev fork (deployedRuntime v) g s0) := by
  cases rev with
  | false =>
    exact payableCheckEVM (a := available) (b := value) (c := UInt256.ofNat len) (d := ⟨0⟩) (e := array)
      (R := values::last::total::UInt256.ofNat i::R) v .multiAttest
      (by simp only [List.length_cons]; omega) hs hheap hlo hh rd
  | true =>
    exact payableCheckEVM (a := value) (b := available) (c := UInt256.ofNat len) (d := array) (e := ⟨0⟩)
      (R := values::last::total::UInt256.ofNat i::R) v .multiRevoke
      (by simp only [List.length_cons]; omega) hs hheap hlo hh rd

end Benchmarks.EAS.EAS
