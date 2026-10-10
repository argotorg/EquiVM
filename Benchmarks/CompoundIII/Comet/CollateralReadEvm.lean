import Benchmarks.CompoundIII.Comet.CollateralValueModel
import Benchmarks.CompoundIII.Comet.MappingScratch
import Benchmarks.CompoundIII.Comet.CollateralMathEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def collateralPricePc (borrow : Bool) : UInt256 := if borrow then ⟨10531⟩ else ⟨11010⟩

def collateralReadMemory (mem : ByteArray) (account : AccountAddress)
    (out : ByteArray) : ByteArray :=
  twoWordHashMem (calldataWord out 32) (solcMappingSlot ⟨6⟩ (EVM.word account.val))
    (twoWordHashMem (EVM.word account.val) ⟨6⟩ mem)

theorem collateralReadMemory_size {mem out : ByteArray} (account : AccountAddress)
    (hm : 64 ≤ mem.size) : (collateralReadMemory mem account out).size = mem.size := by
  unfold collateralReadMemory
  rw [twoWordHashMem_size_of_ge_64 _ _
      (by rw [twoWordHashMem_size_of_ge_64 _ _ hm]; exact hm),
    twoWordHashMem_size_of_ge_64 _ _ hm]

theorem AssetMemory.afterCollateralRead {mem out : ByteArray} {ptr free : UInt256}
    (hm : AssetMemory mem ptr free out) (account : AccountAddress) :
    AssetMemory (collateralReadMemory mem account out) ptr free out :=
  (hm.scratch (EVM.word account.val) ⟨6⟩).scratch (calldataWord out 32)
    (solcMappingSlot ⟨6⟩ (EVM.word account.val))

theorem cometCollateralBalanceRead {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata out : ByteArray}
    {aw ptr free : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (borrow : Bool) (account : AccountAddress) (hstack : R.length + 16 ≤ 1024)
    (hm : AssetMemory mem ptr free out) (hc : AssetCanonical out)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨10490⟩
      (ptr :: ⟨10498⟩ :: ⟨10518⟩ :: collateralPricePc borrow :: ⟨10579⟩ ::
        UInt256.ofNat (collateralFactorOffset borrow) :: ⟨10587⟩ :: ⟨10592⟩ ::
        EVM.word account.val :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (collateralPricePc borrow)
      (collateralBalanceWord evm account out :: ⟨10579⟩ ::
        UInt256.ofNat (collateralFactorOffset borrow) :: ⟨10587⟩ :: ⟨10592⟩ :: ptr :: R)
      (collateralReadMemory mem account out) aw' rdata σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_10490 (immWords := wordsOf (immStore v))
    (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [cometWithExtendedAssetList_block_10490_stack,
    show UInt256.ofNat 6 = (⟨6⟩ : UInt256) from rfl] at r1
  obtain ⟨aw2, k2, C2, r2⟩ := cometMappingHash (v := v)
    (by change R.length + 7 + 6 ≤ 1024; omega) (word_val_addr_canonical account)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  have hm2 := hm.scratch (EVM.word account.val) ⟨6⟩
  have r3 := cometWithExtendedAssetList_block_10498 (immWords := wordsOf (immStore v))
    (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  dsimp only [cometWithExtendedAssetList_block_10498_stack] at r3
  have hasset : memLoad (ptr + UInt256.ofNat 32)
      (twoWordHashMem (EVM.word account.val) ⟨6⟩ mem) = calldataWord out 32 :=
    hm2.words 1 (by decide)
  have hmask : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) (calldataWord out 32) = calldataWord out 32 :=
    solcAddrMask_clean_left hc.2.1
  rw [hasset, hmask] at r3
  obtain ⟨aw4, k4, C4, r4⟩ := cometMappingHash (v := v)
    (by change R.length + 6 + 6 ≤ 1024; omega) hc.2.1
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
  obtain ⟨k5, C5, r5⟩ := cometWithExtendedAssetList_block_10518
    (immWords := wordsOf (immStore v)) (by change R.length + 5 + 5 ≤ 1024; omega)
    (by cases borrow <;>
      rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v] <;> jump_dest) r4
  dsimp only [cometWithExtendedAssetList_block_10518_stack] at r5
  have hslot : solcMappingSlot (solcMappingSlot ⟨6⟩ (EVM.word account.val))
      (calldataWord out 32) = userCollateralSlot account
        (AccountAddress.ofNat (calldataWord out 32).toNat) := by
    rw [userCollateralSlot, addressWord_eq_ofNat_address hc.2.1]
  have hword := hs.storageRead (userCollateralSlot account
    (AccountAddress.ofNat (calldataWord out 32).toNat))
  change RD _ _ _ _ _
    (UInt256.land _ (solcSlotWord σ ee
      (solcMappingSlot (solcMappingSlot ⟨6⟩ (EVM.word account.val)) (calldataWord out 32))) :: _)
    _ _ _ _ _ _ at r5
  rw [hslot, ← hword] at r5
  have hlo (word : UInt256) : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
        (UInt256.ofNat 1)) word = low128 word := u256_land_comm _ _
  rw [hlo] at r5
  exact ⟨_, _, _, r5⟩

theorem cometCollateralPriceStart {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata out : ByteArray}
    {aw ptr free amount : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (borrow : Bool) (hstack : R.length + 11 ≤ 1024)
    (hm : AssetMemory mem ptr free out) (hc : AssetCanonical out)
    (h : RD (deployedRuntime v) ee g s0 (collateralPricePc borrow)
      (amount :: ⟨10579⟩ :: UInt256.ofNat (collateralFactorOffset borrow) ::
        ⟨10587⟩ :: ⟨10592⟩ :: ptr :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨9375⟩
      (EVM.word (AccountAddress.ofNat (calldataWord out 64).toNat).val ::
        collateralMathPc borrow :: amount :: ⟨10579⟩ ::
        UInt256.ofNat (collateralFactorOffset borrow) :: ⟨10587⟩ :: ⟨10592⟩ :: ptr :: R)
      mem aw' rdata σ k' C' := by
  have hfeed : memLoad (ptr + UInt256.ofNat 64) mem = calldataWord out 64 :=
    hm.words 2 (by decide)
  have hmask : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) (calldataWord out 64) = calldataWord out 64 :=
    solcAddrMask_clean_left hc.2.2.1
  rw [addressWord_eq_ofNat_address hc.2.2.1]
  cases borrow with
  | false =>
      have r1 := cometWithExtendedAssetList_block_11010 (immWords := wordsOf (immStore v))
        hstack (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
      dsimp only [cometWithExtendedAssetList_block_11010_stack] at r1
      rw [hfeed, hmask] at r1
      exact ⟨_, _, _, r1⟩
  | true =>
      have r1 := cometWithExtendedAssetList_block_10531 (immWords := wordsOf (immStore v))
        hstack (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
      dsimp only [cometWithExtendedAssetList_block_10531_stack] at r1
      rw [hfeed, hmask] at r1
      exact ⟨_, _, _, r1⟩

end Benchmarks.CompoundIII.Comet
