import Benchmarks.EAS.EAS.ResolveOneRun
import Benchmarks.EAS.EAS.HeapCall

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem resolveOneCallRun {locals imms : Store} {args : List Expr} {retVar : Ident}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {schemaPtr src dataPtr available value ptr ret : UInt256} {R : List UInt256}
    {record : Value} {a : AttestationRecord} {target : AccountAddress} {rev last : Bool} (v : EASImmutables)
    (he : evalExprs? config {contract := contract, locals := locals, immutables := imms} evm args =
      .ok [record,a.value,.int (Int.ofNat value.toNat),.bool rev,.int (Int.ofNat available.toNat),.bool last,.int (Int.ofNat ptr.toNat)])
    (hfield : lookupField? record "resolver" = some (.address target))
    (ht : UInt256.land (memLoad (schemaPtr+UInt256.ofNat 32) mem) solcAddrMask = UInt256.ofNat target.val)
    (hstack : R.length+26 ≤ 1024) (hperm : ee.perm = true) (hs : SourceState s0 ee σ evm)
    (hview : AttestationMemoryView mem src dataPtr a)
    (hsrc : src.toNat+320 ≤ ptr.toNat) (hdata : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ ptr.toNat)
    (hheap : ptr.toNat ≤ 2^64-1) (hh : memLoad (UInt256.ofNat 64) mem = ptr)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨15724⟩
      (schemaPtr::src::value::rev.toUInt256::available::last.toUInt256::ret::R) mem aw rdata σ k C) :
    HeapCallPost fork ((resolveOneUsedValue target value).toNat ≤ available.toNat) config (deployedRuntime v) ee g s0 {contract := contract, locals := locals, immutables := imms}
      evm "_resolveAttestation" args retVar (.int (Int.ofNat (resolveOneUsedValue target value).toNat))
      ret (resolveOneUsedValue target value::R) mem ptr.toNat := by
  exact (resolveOneRun (imms := imms) v hfield ht hstack hperm hs hview hsrc hdata hheap hh hret rd).call
    he resolveOne_lookup (resolveOne_bind record a value rev available last ptr.toNat)

end Benchmarks.EAS.EAS
