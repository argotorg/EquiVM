import Benchmarks.CompoundIII.Comet.UpdateBaseEvm
import Benchmarks.CompoundIII.Comet.MappingScratch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem updateBaseMemory_preserveLater {mem : ByteArray} {ptr otherPtr : UInt256}
    (v : CometWithExtendedAssetListImmutables) (evm : EVM.State)
    (addr : AccountAddress) (basic otherBasic : UserBasicData) (principal : UInt256)
    (hm : UserBasicMemory mem ptr basic) (ho : UserBasicMemory mem otherPtr otherBasic)
    (hlo : 96 ≤ otherPtr.toNat) (hsep : ptr.toNat + 96 ≤ otherPtr.toNat) :
    UserBasicMemory (updateBaseMemory mem ptr v evm addr basic principal) otherPtr otherBasic := by
  have hb := hm.bound
  have h32 : (ptr + UInt256.ofNat 32).toNat = ptr.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have h64 : (ptr + UInt256.ofNat 64).toNat = ptr.toNat + 64 :=
    uadd_word_ofNat_toNat _ _ (by omega)
  unfold updateBaseMemory updateBaseFinishMemory accountIndexMemory accountAccruedMemory
  apply WordStructMemory.scratch _ hlo
  apply WordStructMemory.writeDisjoint _ _ _ (Or.inl (by omega))
  apply WordStructMemory.writeDisjoint _ _ _ (Or.inl (by omega))
  exact ho.writeDisjoint _ _ (Or.inl (by omega))

theorem updateBaseMemory_size {mem : ByteArray} {ptr : UInt256}
    (v : CometWithExtendedAssetListImmutables) (evm : EVM.State)
    (addr : AccountAddress) (basic : UserBasicData) (principal : UInt256)
    (hm : UserBasicMemory mem ptr basic) (hptr : 96 ≤ ptr.toNat) :
    (updateBaseMemory mem ptr v evm addr basic principal).size = mem.size := by
  have hb := hm.bound
  have hs := hm.size
  have h32 : (ptr + UInt256.ofNat 32).toNat = ptr.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have h64 : (ptr + UInt256.ofNat 64).toNat = ptr.toNat + 64 :=
    uadd_word_ofNat_toNat _ _ (by omega)
  unfold updateBaseMemory updateBaseFinishMemory accountIndexMemory accountAccruedMemory
  rw [twoWordHashMem_size_of_ge_64 _ _ (by simp only [writeWord_sparse_size]; omega)]
  simp only [writeWord_sparse_size, h32, h64]
  omega

theorem updateBaseMemory_free {mem : ByteArray} {ptr : UInt256}
    (v : CometWithExtendedAssetListImmutables) (evm : EVM.State)
    (addr : AccountAddress) (basic : UserBasicData) (principal : UInt256)
    (hm : UserBasicMemory mem ptr basic) (hptr : 96 ≤ ptr.toNat) :
    memLoad ⟨64⟩ (updateBaseMemory mem ptr v evm addr basic principal) =
      memLoad ⟨64⟩ mem := by
  have hb := hm.bound
  have hs := hm.size
  have h32 : (ptr + UInt256.ofNat 32).toNat = ptr.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have h64 : (ptr + UInt256.ofNat 64).toNat = ptr.toNat + 64 :=
    uadd_word_ofNat_toNat _ _ (by omega)
  unfold updateBaseMemory updateBaseFinishMemory accountIndexMemory accountAccruedMemory
  rw [twoWordHashMem_load_ge (ptr := ⟨64⟩) _ _ (by decide)
    (by simp only [writeWord_sparse_size]; change 64 + 32 ≤ _; omega)]
  unfold memLoad
  simp only [writeWord_sparse_size, h32, h64]
  rw [if_neg (by change ¬ _ ≤ 64; omega), if_neg (by change ¬ _ ≤ 64; omega)]
  simp only [show (⟨64⟩ : UInt256).toNat = 64 from rfl]
  rw [writeWord_sparse_read_preserved _ _ 64 _ (Or.inl ⟨by omega, by
      simp only [writeWord_sparse_size]; omega⟩),
    writeWord_sparse_read_preserved _ _ 64 _ (Or.inl ⟨by omega, by
      rw [writeWord_sparse_size]; omega⟩),
    writeWord_sparse_read_preserved _ _ 64 _ (Or.inl ⟨by omega, by omega⟩)]

end Benchmarks.CompoundIII.Comet
