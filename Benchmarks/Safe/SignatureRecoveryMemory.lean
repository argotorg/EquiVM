import Benchmarks.Safe.EcrecoverMemory
import Benchmarks.Safe.BytesMemoryPreserved

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

theorem ecrecoverOutputMemory_bytes {mem out bytes : ByteArray} {ptr src : Nat}
    {input : EcrecoverInput} (hm : BytesMemory mem src bytes) (hs : 96 ≤ src)
    (ha : src + 32 + bytes.size ≤ ptr) (hb : src < UInt256.size) :
    BytesMemory (ecrecoverOutputMemory mem ptr input out) src bytes := by
  apply hm.preserved hb (by rw [ecrecoverOutputMemory_size _ _ _ _ (by omega)]; omega)
  intro off count hlo hin
  exact ecrecoverOutputMemory_preserved _ _ _ _ _ _ (by have := hm.available; omega)
    (by omega) (by omega)

theorem ecrecoverOutputMemory_zeroSlot {mem out : ByteArray} {ptr : Nat} {input : EcrecoverInput}
    (hm : 128 ≤ mem.size) (hp : 128 ≤ ptr) (hz : memLoad ⟨96⟩ mem = ⟨0⟩) :
    memLoad ⟨96⟩ (ecrecoverOutputMemory mem ptr input out) = ⟨0⟩ := by
  rw [memLoadReadWord, show (⟨96⟩ : UInt256).toNat = 96 from rfl,
    ecrecoverOutputMemory_preserved _ _ _ _ _ _ hm (by decide) hp,
    ← show (⟨96⟩ : UInt256).toNat = 96 from rfl, ← memLoadReadWord, hz]

end Benchmarks.Safe
