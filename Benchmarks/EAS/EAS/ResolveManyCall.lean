import Benchmarks.EAS.EAS.ResolveManyRun
import Benchmarks.EAS.EAS.HeapCall

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem resolveManyCallRun {locals imms : Store} {args : List Expr} {retVar : Ident}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {schema array values available ptr ret : UInt256} {R : List UInt256}
    {record : Value} {ats : List AttestationRecord} {words : List UInt256} {target : AccountAddress} {rev last : Bool}
    (v : EASImmutables)
    (he : evalExprs? config {contract := contract, locals := locals, immutables := imms} evm args =
      .ok [record,.array (ats.map AttestationRecord.value),.array (words.map fun w => .int (Int.ofNat w.toNat)),
        .bool rev,.int (Int.ofNat available.toNat),.bool last,.int (Int.ofNat ptr.toNat)])
    (hfield : lookupField? record "resolver" = some (.address target))
    (ht : UInt256.land (memLoad (schema+UInt256.ofNat 32) mem) solcAddrMask = UInt256.ofNat target.val)
    (hstack : R.length+36 ≤ 1024) (hperm : ee.perm = true ∨ ats = []) (hs : SourceState s0 ee σ evm)
    (harray : AttestationArrayMemoryView mem array ats ptr.toNat)
    (hvalues : WordArrayMemoryView mem values words ptr.toNat) (hlen : ats.length = words.length)
    (hheap : ptr.toNat ≤ 2^64-1) (hh : memLoad (UInt256.ofNat 64) mem = ptr)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolveManyEntryPC rev)
      (schema::array::values::available::last.toUInt256::ret::R) mem aw rdata σ k C) :
    HeapCallPostOrStatic fork ((resolveManyUsedValue target words).toNat ≤ available.toNat) config (deployedRuntime v) ee g s0 {contract := contract, locals := locals, immutables := imms}
      evm "_resolveAttestations" args retVar (.int (Int.ofNat (resolveManyUsedValue target words).toNat))
      ret (resolveManyUsedValue target words::R) mem ptr.toNat := by
  exact (resolveManyRun (imms := imms) v hfield ht hstack hperm hs harray hvalues hlen hheap hh hret rd).call
    he resolveMany_lookup (resolveMany_bind record ats words rev available last ptr.toNat)

end Benchmarks.EAS.EAS
