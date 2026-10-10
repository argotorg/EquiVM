import Benchmarks.Morpho.MetaMorphoV1_1.MorphoSlotAllocation
import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsCall

/-! Connect the fixed supply-share allocations to the actual external call. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

theorem nextCursor_256 (ptr : UInt256) : nextCursor ptr ⟨256⟩ = ptr + ⟨256⟩ := by
  rfl

theorem positionSlotArrayMem_view (mem calldata : ByteArray) (ptr id user : UInt256)
    (hlo : 96 ≤ ptr.toNat) (hfit : ptr.toNat + 256 < 2 ^ 64) :
    (ptr + ⟨192⟩).toNat + 64 ≤ (positionSlotArrayMem mem calldata ptr id user).size ∧
      memLoad (ptr + ⟨192⟩) (positionSlotArrayMem mem calldata ptr id user) = ⟨1⟩ ∧
      memLoad ((ptr + ⟨192⟩) + ⟨32⟩) (positionSlotArrayMem mem calldata ptr id user) =
        positionSupplySharesSlot id (AccountAddress.ofNat user.toNat) ∧
      memLoad ⟨64⟩ (positionSlotArrayMem mem calldata ptr id user) = ptr + ⟨256⟩ := by
  have h192 : (ptr + ⟨192⟩).toNat = ptr.toNat + 192 :=
    uadd_word_ofNat_toNat ptr 192 (lt_trans (by omega : ptr.toNat + 192 < 2 ^ 64) (by decide))
  have hsmall : (ptr + ⟨192⟩).toNat + 32 < UInt256.size := by
    rw [h192]
    exact lt_trans (by omega : ptr.toNat + 192 + 32 < 2 ^ 64) (by decide)
  have hsize : (ptr + ⟨192⟩).toNat + 64 ≤
      (positionSlotArrayMem mem calldata ptr id user).size := by
    rw [positionSlotArrayMem, morphoArrayMem_size _ _ _ _ hsmall]
    omega
  refine ⟨hsize, ?_, ?_, ?_⟩
  · exact loadedWord_of_read (by omega) (morphoArrayMem_length _ _ _ _ hsmall)
  · apply loadedWord_of_read
    · rw [show ((ptr + ⟨192⟩) + ⟨32⟩).toNat = (ptr + ⟨192⟩).toNat + 32 from
        uadd_word_ofNat_toNat _ _ hsmall]
      omega
    · exact morphoArrayMem_value _ _ _ _
  · have hread := morphoArrayMem_free (positionSlotHashMem mem ptr id user) calldata
      (ptr + ⟨192⟩) (positionSupplySharesSlot id (AccountAddress.ofNat user.toNat))
      (by rw [h192]; omega) hsmall
    rw [u256_add_assoc] at hread
    exact loadedWord_of_read (by change 64 + 32 ≤ _; rw [h192] at hsize; omega) hread

theorem supplySharesReachStaticcall {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr morpho id user : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 14 ≤ 1024)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hfit : allocationFits ptr ⟨256⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨14078⟩ (morpho :: id :: user :: R)
      mem aw rdata σ k C) :
    ∃ callGas aw' k' C', RD (deployedRuntime v) I g s0 ⟨14210⟩
      (callGas :: UInt256.land solcAddrMask morpho :: nextCursor ptr ⟨256⟩ :: ⟨100⟩ ::
        nextCursor ptr ⟨256⟩ :: ⟨0⟩ :: nextCursor ptr ⟨256⟩ :: R)
      (extSloadsCallMem (positionSlotArrayMem mem I.calldata ptr id user)
        (nextCursor ptr ⟨256⟩).toNat
        (positionSupplySharesSlot id (AccountAddress.ofNat user.toNat)))
      aw' rdata σ k' C' := by
  have hb : ptr.toNat + 256 < 2 ^ 64 :=
    (allocationFits_aligned ptr ⟨256⟩ (by decide +kernel)).mp hfit
  have h192 : (ptr + ⟨192⟩).toNat = ptr.toNat + 192 :=
    uadd_word_ofNat_toNat ptr 192 (lt_trans (by omega : ptr.toNat + 192 < 2 ^ 64) (by decide))
  have h256 : (ptr + ⟨256⟩).toNat = ptr.toNat + 256 :=
    uadd_word_ofNat_toNat ptr 256 (lt_trans hb (by decide))
  obtain ⟨aw1, k1, C1, h1⟩ := supplySharesReachEncoding v (by omega) hcalldata hfree hlo hb rd
  obtain ⟨hin, hlen, hslot, hcursor⟩ := positionSlotArrayMem_view mem I.calldata ptr id user hlo hb
  exact extSloadsReachStaticcall v hstack hin
    (by rw [h192, nextCursor_256, h256])
    (by rw [nextCursor_256, h256]; change _ < 2 ^ 256; omega)
    hcursor hlen hslot h1

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
