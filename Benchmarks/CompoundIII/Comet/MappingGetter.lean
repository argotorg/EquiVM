import Benchmarks.CompoundIII.Comet.AddressGetter

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: normalize a getter's return after a pair of mapping-hash stores.
theorem mappingGetterReturnData (key slot value : UInt256) :
    (value.toByteArray.write 0 (twoWordHashMem key slot solcFreePtrMem)
      (memLoad ⟨64⟩ (twoWordHashMem key slot solcFreePtrMem)).toNat 32).readWithPadding
        (memLoad ⟨64⟩ (twoWordHashMem key slot solcFreePtrMem)).toNat 32 =
      value.toByteArray := by
  have hsize := twoWordHashMem_size_96 key slot solcFreePtrMem_size
  have hread := twoWordHashMem_read64 key slot solcFreePtrMem_size solcFreePtrMem_read64
  have hload : memLoad ⟨64⟩ (twoWordHashMem key slot solcFreePtrMem) = ⟨128⟩ :=
    mloadFreePtrValue (by rw [hsize]; decide) hread
  rw [hload]
  exact solcScratchReturnMem_read128 value hsize

theorem mappingGetterHash (key slot : UInt256) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem key slot solcFreePtrMem) = solcMappingSlot slot key := by
  exact twoWordHashMem_solcMappingSlot slot key solcFreePtrMem_size

end Benchmarks.CompoundIII.Comet
