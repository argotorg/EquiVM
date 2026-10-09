import Benchmarks.CompoundIII.Comet.WithdrawCollateralModel
import Benchmarks.CompoundIII.Comet.CollateralMappingMemory
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_075

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def withdrawCollateralTotalMemory (mem : ByteArray) (asset : AccountAddress) : ByteArray :=
  twoWordHashMem (EVM.word asset.val) ⟨2⟩ mem

def withdrawCollateralBalanceStack (src recipient asset : AccountAddress)
    (amount balance ret : UInt256) (R : List UInt256) : List UInt256 :=
  [balance, amount, ⟨16347⟩, balance, EVM.word src.val, ⟨2^128-1⟩,
    EVM.word recipient.val, solcAddrMask, EVM.word asset.val, EVM.word src.val,
    amount, ⟨0⟩, ret] ++ R

theorem cometWithdrawCollateralRead {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw amount ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (src recipient asset : AccountAddress) (hstack : R.length + 16 ≤ 1024)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨16281⟩
      (EVM.word src.val :: EVM.word recipient.val :: EVM.word asset.val :: amount :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨15305⟩
      (withdrawCollateralBalanceStack src recipient asset amount
        (withdrawCollateralBalance evm src asset) ret R)
      (userCollateralMemory mem src asset) aw' rdata σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_16281
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 13 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [cometWithExtendedAssetList_block_16281_stack,
    cometWithExtendedAssetList_block_16281_memory] at r1
  have hsrc : UInt256.land (EVM.word src.val)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = EVM.word src.val := addressWord_val_clean src
  rw [hsrc] at r1
  change RD _ _ _ _ ⟨2428⟩
    (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (EVM.word src.val) ⟨6⟩ mem) ::
      EVM.word asset.val :: ⟨16335⟩ :: ⟨2^128-1⟩ :: EVM.word src.val :: ⟨2^128-1⟩ ::
      EVM.word recipient.val :: solcAddrMask :: EVM.word asset.val :: EVM.word src.val ::
      amount :: ⟨0⟩ :: ret :: R) (twoWordHashMem (EVM.word src.val) ⟨6⟩ mem)
    _ _ _ _ _ at r1
  have hh : keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (EVM.word src.val) ⟨6⟩ mem) =
      solcMappingSlot ⟨6⟩ (EVM.word src.val) :=
    twoWordHashMem_solcMappingSlot_any ⟨6⟩ (EVM.word src.val) mem
  rw [hh] at r1
  obtain ⟨aw2, k2, C2, r2⟩ := cometMappingHash (v := v)
    (by change R.length + 10 + 6 ≤ 1024; omega) (word_val_addr_canonical asset)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  obtain ⟨k3, C3, r3⟩ := cometWithExtendedAssetList_block_16335
    (immWords := wordsOf (immStore v)) (by change R.length + 2 + 12 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  change RD _ _ _ _ _ (withdrawCollateralBalanceStack src recipient asset amount
    (low128 (solcSlotWord σ ee (userCollateralSlot src asset))) ret R) _ _ _ _ _ _ at r3
  rw [← hs.storageRead] at r3
  exact ⟨_, _, _, r3⟩

def withdrawCollateralSubStack (src recipient asset : AccountAddress)
    (amount balance next ret : UInt256) (R : List UInt256) : List UInt256 :=
  [next, balance, EVM.word src.val, ⟨2^128-1⟩, EVM.word recipient.val, solcAddrMask,
    EVM.word asset.val, EVM.word src.val, amount, ⟨0⟩, ret] ++ R

def withdrawCollateralTotalStack (src recipient asset : AccountAddress)
    (amount balance next total ret : UInt256) (R : List UInt256) : List UInt256 :=
  [total, amount, ⟨16380⟩, totalsCollateralSlot asset, ⟨0⟩, EVM.word asset.val,
    next, next, balance, EVM.word src.val, ⟨2^128-1⟩, EVM.word recipient.val,
    solcAddrMask, EVM.word asset.val, EVM.word src.val, amount, EVM.word asset.val, ret] ++ R

theorem cometWithdrawCollateralTotalRead {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw amount balance next ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (src recipient asset : AccountAddress) (hstack : R.length + 19 ≤ 1024)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨16347⟩
      (withdrawCollateralSubStack src recipient asset amount balance next ret R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨15305⟩
      (withdrawCollateralTotalStack src recipient asset amount balance next
        (withdrawCollateralTotal evm asset) ret R)
      (withdrawCollateralTotalMemory mem asset) aw' rdata σ k' C' := by
  obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_16347
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 18 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [cometWithExtendedAssetList_block_16347_stack,
    cometWithExtendedAssetList_block_16347_memory] at r1
  have hasset : UInt256.land (EVM.word asset.val) solcAddrMask = EVM.word asset.val :=
    addressWord_val_clean asset
  rw [hasset] at r1
  have hh : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      ((UInt256.ofNat 2).toByteArray.write 0
        ((EVM.word asset.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)
        (UInt256.ofNat 32).toNat 32) = totalsCollateralSlot asset :=
    twoWordHashMem_solcMappingSlot_any ⟨2⟩ (EVM.word asset.val) mem
  rw [hh] at r1
  change RD _ _ _ _ _
    (withdrawCollateralTotalStack src recipient asset amount balance next
      (low128 (solcSlotWord σ ee (totalsCollateralSlot asset))) ret R)
    (twoWordHashMem (EVM.word asset.val) ⟨2⟩ mem) _ _ _ _ _ at r1
  rw [← hs.storageRead] at r1
  exact ⟨_, _, _, r1⟩

end Benchmarks.CompoundIII.Comet
