import Benchmarks.EAS.EAS.RecordEventEVM

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def recordFirstMemory (mem : ByteArray) (site : UIDSite) (src t3 t4 : UInt256) (i : Nat) : ByteArray :=
  Reasoning.Theory.writeWord mem ((recordArrayPtr site t3 t4).toNat+32+32*i) src
def recordSecondMemory (mem : ByteArray) (site : UIDSite) (src t3 t4 value : UInt256) (i : Nat) : ByteArray :=
  Reasoning.Theory.writeWord (recordFirstMemory mem site src t3 t4 i)
    ((recordValuesPtr site t4).toNat+32+32*i) value
def recordTailMemory (mem : ByteArray) (site : UIDSite) (src t3 t4 value uidPtr word : UInt256) (i : Nat) : ByteArray :=
  recordEventMemory (recordSecondMemory mem site src t3 t4 value i)
    (UInt256.ofNat (uidPtr.toNat+32+32*i)) word

theorem easRecordTail {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C i len : Nat}
    {dummy word src value uidPtr t1 t3 t4 : UInt256} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+31 ≤ 1024) (hp : ee.perm = true)
    (hi : i < len) (hb : (recordArrayPtr site t3 t4).toNat+32+32*len < UInt256.size)
    (hin : (recordArrayPtr site t3 t4).toNat+32+32*len ≤ mem.size)
    (hl : memLoad (recordArrayPtr site t3 t4) mem = UInt256.ofNat len)
    (hvb : (recordValuesPtr site t4).toNat+32+32*len < UInt256.size)
    (hvl : memLoad (recordValuesPtr site t4) (recordFirstMemory mem site src t3 t4 i) = UInt256.ofNat len)
    (hvalue : memLoad (refUIDPtr site t3+UInt256.ofNat 160) (recordFirstMemory mem site src t3 t4 i) = value)
    (hptr : recordUIDsPtr site (recordSecondMemory mem site src t3 t4 value i) = uidPtr)
    (hul : memLoad uidPtr (recordSecondMemory mem site src t3 t4 value i) = UInt256.ofNat len)
    (rd : RD fork (deployedRuntime v) ee g s0 (refUIDReadyPC site)
      (refUIDReadyStack site dummy word src t1 (UInt256.ofNat i) t3 t4 R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (recordNextPC site)
      (recordNextStack site t1 (UInt256.ofNat (i+1)) t3 t4 R)
      (recordTailMemory mem site src t3 t4 value uidPtr word i) aw' rdata σ k' C' := by
  obtain ⟨aw1,k1,C1,hr1⟩ := easRecordArrayStore v site hstack hi hb hin hl rd
  obtain ⟨aw2,k2,C2,hr2⟩ := easRecordValuesStore v site (by omega) hi hvb hvl hvalue hptr hul hr1
  obtain ⟨aw3,k3,C3,hr3⟩ := easRecordEvent v site (by omega) hp hr2
  have hinc : UInt256.ofNat i+UInt256.ofNat 1 = UInt256.ofNat (i+1) := by
    rw [u256_add_comm]
    exact u256_one_add_ofNat i
  rw [hinc] at hr3
  exact ⟨aw3,k3,C3,hr3⟩

end Benchmarks.EAS.EAS
