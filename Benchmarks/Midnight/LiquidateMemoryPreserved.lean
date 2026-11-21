import Benchmarks.Midnight.LiquidateIterationMemory

/-! Memory words retained across the liquidation loop, excluding its changing bitmap. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

structure LiquidateMemoryPreserved (before after : ByteArray) (limit : Nat) : Prop where
  size : before.size ≤ after.size
  load : ∀ read : UInt256, 96 ≤ read.toNat → read.toNat + 32 ≤ limit →
    read.toNat + 32 ≤ before.size → (read.toNat + 32 ≤ 704 ∨ 736 ≤ read.toNat) →
    memLoad read after = memLoad read before

theorem LiquidateMemoryPreserved.refl (mem : ByteArray) (limit : Nat) :
    LiquidateMemoryPreserved mem mem limit := ⟨le_rfl, fun _ _ _ _ _ ↦ rfl⟩

theorem LiquidateMemoryPreserved.trans {before middle after : ByteArray} {limit : Nat}
    (h1 : LiquidateMemoryPreserved before middle limit)
    (h2 : LiquidateMemoryPreserved middle after limit) :
    LiquidateMemoryPreserved before after limit := by
  refine ⟨h1.size.trans h2.size, fun read hlo hlim hin hdisj ↦ ?_⟩
  rw [h2.load read hlo hlim (hin.trans h1.size) hdisj, h1.load read hlo hlim hin hdisj]

theorem LiquidateMemoryPreserved.mono {before after : ByteArray} {limit smaller : Nat}
    (h : LiquidateMemoryPreserved before after limit) (hle : smaller ≤ limit) :
    LiquidateMemoryPreserved before after smaller :=
  ⟨h.size, fun read hlo hlim hin hdisj ↦ h.load read hlo (hlim.trans hle) hin hdisj⟩

theorem MemoryPrefix.liquidateClear {before after : ByteArray} {limit : Nat}
    (hp : MemoryPrefix before after limit) (bitmap : UInt256) :
    LiquidateMemoryPreserved before (liquidateBitmapMemory after bitmap) limit := by
  refine ⟨hp.size.trans (by rw [liquidateBitmapMemory, writeWord_sparse_size]; omega),
    fun read hlo hlim hin hdisj ↦ ?_⟩
  rw [liquidateBitmapMemory_preserved _ _ (hin.trans hp.size) hdisj,
    hp.load read hlo hlim hin]

end Benchmarks.Midnight
