import Benchmarks.CompoundIII.Comet.UserBasicWrite
import Benchmarks.CompoundIII.Comet.UserBasicPackedWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def storeUserBasicLow (evm : EVM.State) (addr : AccountAddress) (basic : UserBasicData) :
    EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (userBasicSlot addr)
    (userBasicLowWord
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot addr))
      (UInt256.signextend ⟨12⟩ basic.principal) basic.index basic.accrued)

theorem storeUserBasic_eq (evm : EVM.State) (addr : AccountAddress) (basic : UserBasicData) :
    storeUserBasic evm addr basic =
      storePackedWord
        (storePackedWord (storeUserBasicLow evm addr basic) (userBasicSlot addr) basic.assets 29 2)
        (userBasicSlot addr) basic.reserved 31 1 := by
  have hlow :
      storePackedWord
        (storePackedWord
          (storePackedWord evm (userBasicSlot addr) (UInt256.signextend ⟨12⟩ basic.principal) 0 13)
          (userBasicSlot addr) basic.index 13 8)
        (userBasicSlot addr) basic.accrued 21 8 = storeUserBasicLow evm addr basic := by
    change storePackedWord
      (storePackedWord
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (userBasicSlot addr)
          (packedWriteWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot addr))
            (UInt256.signextend ⟨12⟩ basic.principal) 0 13))
        (userBasicSlot addr) basic.index 13 8)
      (userBasicSlot addr) basic.accrued 21 8 = _
    rw [storePackedWord_after_modify evm _ _ _ _
      (fun old ↦ packedWriteWord old (UInt256.signextend ⟨12⟩ basic.principal) 0 13)]
    rw [storePackedWord_after_modify evm _ _ _ _
      (fun old ↦ packedWriteWord
        (packedWriteWord old (UInt256.signextend ⟨12⟩ basic.principal) 0 13) basic.index 13 8)]
    rw [userBasicLowWord_packed]
    rfl
  dsimp only [storeUserBasic]
  rw [hlow]

theorem sourceState_userBasicLow {s0 I σ evm} (hs : SourceState s0 I σ evm)
    (addr : AccountAddress) (basic : UserBasicData) :
    SourceState s0 I
      (sstoreAccountMap I.codeOwner σ (userBasicSlot addr)
        (userBasicLowWord (solcSlotWordAt (userBasicSlot addr) σ I)
          (UInt256.signextend ⟨12⟩ basic.principal) basic.index basic.accrued))
      (storeUserBasicLow evm addr basic) :=
  hs.readModifyWrite (userBasicSlot addr)
    (fun old ↦ userBasicLowWord old (UInt256.signextend ⟨12⟩ basic.principal)
      basic.index basic.accrued)

theorem sourceState_userBasicAssets {s0 I σ evm} (hs : SourceState s0 I σ evm)
    (slot assets : UInt256) :
    SourceState s0 I
      (sstoreAccountMap I.codeOwner σ slot (userBasicAssetsWord (solcSlotWordAt slot σ I) assets))
      (storePackedWord evm slot assets 29 2) := by
  have hw := hs.readModifyWrite slot (fun old ↦ packedWriteWord old assets 29 2)
  change SourceState _ _ _ (storePackedWord evm slot assets 29 2) at hw
  rw [userBasicAssetsWord_packed] at hw
  exact hw

theorem sourceState_userBasicReserved {s0 I σ evm} (hs : SourceState s0 I σ evm)
    (slot reserved : UInt256) :
    SourceState s0 I
      (sstoreAccountMap I.codeOwner σ slot
        (userBasicReservedWord (solcSlotWordAt slot σ I) reserved))
      (storePackedWord evm slot reserved 31 1) := by
  have hw := hs.readModifyWrite slot (fun old ↦ packedWriteWord old reserved 31 1)
  change SourceState _ _ _ (storePackedWord evm slot reserved 31 1) at hw
  rw [userBasicReservedWord_packed] at hw
  exact hw

end Benchmarks.CompoundIII.Comet
