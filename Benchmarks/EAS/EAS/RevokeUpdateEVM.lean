import Benchmarks.EAS.EAS.RevokeValuesLog
import Benchmarks.EAS.EAS.RecordUID
import Benchmarks.EAS.EAS.RevocationRequestMemory

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def revokeUpdateMemory (mem : ByteArray) (site : RevokeSite) (src heap value word : UInt256) (i : Nat) : ByteArray :=
  revokeValuesLogMemory (Reasoning.Theory.writeWord mem (site.records.toNat+32+32*i) src) site heap value word i

theorem easRevokeUpdate {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C i : Nat}
    {src request heap : UInt256} {r : RevocationRequestRecord} {R : List UInt256}
    (v : EASImmutables) (site : RevokeSite) (hstack : R.length+30 ≤ 1024)
    (hperm : ee.perm = true) (hi : i < site.length)
    (hb : site.values.toNat+32+32*site.length < UInt256.size)
    (ha : site.records.toNat+32+32*site.length ≤ site.values.toNat)
    (hac : site.records.toNat+32+32*site.length ≤ mem.size)
    (hvc : site.values.toNat+32 ≤ mem.size) (halo : 96 ≤ site.records.toNat)
    (hal : memLoad site.records mem = UInt256.ofNat site.length)
    (hvl : memLoad site.values mem = UInt256.ofNat site.length)
    (hr : RevocationRequestMemoryView mem request r) (hre : request.toNat+64 ≤ site.records.toNat)
    (hh : memLoad (UInt256.ofNat 64) mem = heap)
    (rd : RD fork (deployedRuntime v) ee g s0 site.kind.copyReturnPC
      (src::revokeCopySaved site ee request (UInt256.ofNat i) r.uid R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 site.kind.loopPC
      (revokeLoopStack site ee (UInt256.ofNat (i+1)) R)
      (revokeUpdateMemory mem site src heap r.value r.uid i) aw' rdata σ k' C' := by
  obtain ⟨aw1,k1,C1,rd1⟩ := easRevokeArrayStore v site hstack hi (by omega) hac hal rd
  let m := Reasoning.Theory.writeWord mem (site.records.toNat+32+32*i) src
  have hp : MemoryPrefix mem m site.records.toNat := memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (by omega))
  have hr1 := hr.preserve hp hre (by omega)
  have hv1 : memLoad site.values m = UInt256.ofNat site.length :=
    (memLoad_write_above _ _ _ _ (by omega) hvc).trans hvl
  have hh1 : memLoad (UInt256.ofNat 64) m = heap :=
    (memLoad_write_below _ _ _ _ (by change 64+32 ≤ _; omega) (by change 64+32 ≤ _; omega)).trans hh
  exact easRevokeValuesLog v site (by omega) hperm hi hb (le_trans hvc hp.size) (by omega) hv1
    (by omega) hr1.uid hr1.value hh1 rd1

end Benchmarks.EAS.EAS
