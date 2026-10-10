import Benchmarks.CompoundIII.Comet.UserCollateralRead
import Benchmarks.CompoundIII.Comet.MappingScratch
import Benchmarks.CompoundIII.Comet.WordStructMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def userCollateralMemory (mem : ByteArray) (account asset : AccountAddress) : ByteArray :=
  twoWordHashMem (EVM.word asset.val) (solcMappingSlot ⟨6⟩ (EVM.word account.val))
    (twoWordHashMem (EVM.word account.val) ⟨6⟩ mem)

theorem WordStructMemory.userCollateral {mem ptr n words}
    (h : WordStructMemory mem ptr n words) (hlo : 96 ≤ ptr.toNat)
    (account asset : AccountAddress) :
    WordStructMemory (userCollateralMemory mem account asset) ptr n words :=
  (h.scratch hlo (EVM.word account.val) ⟨6⟩).scratch hlo
    (EVM.word asset.val) (solcMappingSlot ⟨6⟩ (EVM.word account.val))

theorem userCollateralMemory_size {mem : ByteArray} (account asset : AccountAddress)
    (hm : 64 ≤ mem.size) : (userCollateralMemory mem account asset).size = mem.size := by
  unfold userCollateralMemory
  rw [twoWordHashMem_size_of_ge_64 _ _
      (by rw [twoWordHashMem_size_of_ge_64 _ _ hm]; exact hm),
    twoWordHashMem_size_of_ge_64 _ _ hm]

theorem userCollateralMemory_free {mem : ByteArray} {free : UInt256}
    (account asset : AccountAddress) (hm : 96 ≤ mem.size) (hf : memLoad ⟨64⟩ mem = free) :
    memLoad ⟨64⟩ (userCollateralMemory mem account asset) = free := by
  have hsize := twoWordHashMem_size_of_ge_64 (mem := mem)
    (EVM.word account.val) ⟨6⟩ (by omega)
  rw [userCollateralMemory, twoWordHashMem_load_ge (ptr := ⟨64⟩) _ _ (by decide)
    (by rw [hsize]; exact hm), twoWordHashMem_load_ge (ptr := ⟨64⟩) _ _ (by decide) hm, hf]

end Benchmarks.CompoundIII.Comet
