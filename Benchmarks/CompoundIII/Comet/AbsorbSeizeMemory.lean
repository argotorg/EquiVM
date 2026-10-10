import Benchmarks.CompoundIII.Comet.CollateralMappingMemory
import Benchmarks.CompoundIII.Comet.MappingPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def absorbSeizeMemory (mem : ByteArray) (account asset : AccountAddress) : ByteArray :=
  twoWordHashMem (EVM.word asset.val) ⟨2⟩ (userCollateralMemory mem account asset)

theorem userCollateralMemory_prefix (mem : ByteArray) (account asset : AccountAddress)
    (limit : Nat) : MemoryPrefix mem (userCollateralMemory mem account asset) limit :=
  (twoWordHashMem_prefix mem (EVM.word account.val) ⟨6⟩ limit).trans
    (twoWordHashMem_prefix _ (EVM.word asset.val) (solcMappingSlot ⟨6⟩ (EVM.word account.val)) limit)

theorem absorbSeizeMemory_prefix (mem : ByteArray) (account asset : AccountAddress)
    (limit : Nat) : MemoryPrefix mem (absorbSeizeMemory mem account asset) limit :=
  (userCollateralMemory_prefix mem account asset limit).trans
    (twoWordHashMem_prefix _ (EVM.word asset.val) ⟨2⟩ limit)

theorem AssetMemory.userCollateral {mem ptr free out} (hm : AssetMemory mem ptr free out)
    (account asset : AccountAddress) :
    AssetMemory (userCollateralMemory mem account asset) ptr free out :=
  (hm.scratch (EVM.word account.val) ⟨6⟩).scratch
    (EVM.word asset.val) (solcMappingSlot ⟨6⟩ (EVM.word account.val))

theorem AssetMemory.afterSeize {mem ptr free out} (hm : AssetMemory mem ptr free out)
    (account asset : AccountAddress) :
    AssetMemory (absorbSeizeMemory mem account asset) ptr free out :=
  (hm.userCollateral account asset).scratch (EVM.word asset.val) ⟨2⟩

theorem absorbSeizeMemory_size {mem : ByteArray} (account asset : AccountAddress)
    (hm : 64 ≤ mem.size) : (absorbSeizeMemory mem account asset).size = mem.size := by
  rw [absorbSeizeMemory, twoWordHashMem_size_of_ge_64 _ _
    (by rw [userCollateralMemory_size account asset hm]; exact hm),
    userCollateralMemory_size account asset hm]

end Benchmarks.CompoundIII.Comet
