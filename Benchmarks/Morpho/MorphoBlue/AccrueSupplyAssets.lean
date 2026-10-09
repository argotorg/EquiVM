import Benchmarks.Morpho.MorphoBlue.AccrueBorrowAssets

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def accrueSupplyAssetsAccounts (σ : AccountMap) (I : ExecutionEnv) (id interest : UInt256) : AccountMap :=
  storeMarketFieldAccounts σ I id ⟨0, by decide⟩ (marketFieldWord σ I id 0 + interest)

section Routines
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
  {id interest : UInt256} {R : List UInt256}

theorem morphoAccrueSupplyReachAdd (hstack : R.length + 19 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13650)
      ([interest, UInt256.lnot uint128Mask, UInt256.ofNat 0, UInt256.ofNat 64,
        uint128Mask, id, UInt256.ofNat 32, solcAddrMask, interest, UInt256.ofNat 3] ++ R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12664)
      ([marketFieldWord σ ee id 0, interest, UInt256.ofNat 13675, uint128Mask, UInt256.lnot uint128Mask,
        solcSlotWordAt (marketFieldSlot id 0) σ ee, marketFieldSlot id 0, UInt256.ofNat 0,
        UInt256.ofNat 64, uint128Mask, id, UInt256.ofNat 32, solcAddrMask, interest, UInt256.ofNat 3] ++ R)
      (twoWordHashMem id (UInt256.ofNat 3) mem) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_13650_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem id (UInt256.ofNat 3) mem) = marketFieldSlot id 0 := by
    have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem id (UInt256.ofNat 3) mem) = solcMappingSlot ⟨3⟩ id :=
      twoWordHashMem_solcMappingSlot_any _ _ _
    simpa only [marketFieldSlot, Nat.zero_div, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
      u256_add_zero] using hh
  change RD _ _ _ _ _
    ([UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem id (UInt256.ofNat 3) mem)) σ ee) uint128Mask,
      interest, UInt256.ofNat 13675, uint128Mask, UInt256.lnot uint128Mask,
      solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem id (UInt256.ofNat 3) mem)) σ ee,
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 3) mem),
      UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, id, UInt256.ofNat 32,
      solcAddrMask, interest, UInt256.ofNat 3] ++ R)
    (twoWordHashMem id (UInt256.ofNat 3) mem) _ _ _ _ _ at rd1
  rw [hh] at rd1
  exact ⟨aw1, k1, C1, rd1⟩

theorem morphoAccrueSupplyAddOk (hstack : R.length + 19 ≤ 1024)
    (hi : interest.toNat < 2 ^ 128)
    (hsum : (marketFieldWord σ ee id 0).toNat + interest.toNat < 2 ^ 128)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13650)
      ([interest, UInt256.lnot uint128Mask, UInt256.ofNat 0, UInt256.ofNat 64,
        uint128Mask, id, UInt256.ofNat 32, solcAddrMask, interest, UInt256.ofNat 3] ++ R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13675)
      ([marketFieldWord σ ee id 0 + interest, uint128Mask, UInt256.lnot uint128Mask,
        solcSlotWordAt (marketFieldSlot id 0) σ ee, marketFieldSlot id 0, UInt256.ofNat 0,
        UInt256.ofNat 64, uint128Mask, id, UInt256.ofNat 32, solcAddrMask, interest, UInt256.ofNat 3] ++ R)
      (twoWordHashMem id (UInt256.ofNat 3) mem) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoAccrueSupplyReachAdd (v := v) hstack h
  obtain ⟨k2, C2, rd2⟩ := morphoCheckedAdd128Ok (v := v)
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (halfWord_bound _ _) hi hsum rd1
  exact ⟨aw1, k2, C2, rd2⟩

theorem morphoAccrueSupplyAddReverts (hstack : R.length + 19 ≤ 1024)
    (hi : interest.toNat < 2 ^ 128)
    (hover : 2 ^ 128 ≤ (marketFieldWord σ ee id 0).toNat + interest.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13650)
      ([interest, UInt256.lnot uint128Mask, UInt256.ofNat 0, UInt256.ofNat 64,
        uint128Mask, id, UInt256.ofNat 32, solcAddrMask, interest, UInt256.ofNat 3] ++ R)
      mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoAccrueSupplyReachAdd (v := v) hstack h
  exact morphoCheckedAdd128Reverts (v := v) (by simp only [List.append, List.length_cons]; omega)
    (halfWord_bound _ _) hi hover rd1

theorem morphoAccrueSupplyStore {marker : UInt256} (hstack : R.length + 14 ≤ 1024)
    (hp : ee.perm = true) (hc : (marketFieldWord σ ee id 0 + interest).toNat < 2 ^ 128)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13675)
      ([marketFieldWord σ ee id 0 + interest, uint128Mask, UInt256.lnot uint128Mask,
        solcSlotWordAt (marketFieldSlot id 0) σ ee, marketFieldSlot id 0, UInt256.ofNat 0,
        UInt256.ofNat 64, uint128Mask, id, UInt256.ofNat 32, solcAddrMask, interest,
        UInt256.ofNat 3, marker] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0
      (if marketFieldWord (accrueSupplyAssetsAccounts σ ee id interest) ee id 5 = ⟨0⟩ then
        UInt256.ofNat 13706 else UInt256.ofNat 13738)
      ([marker, UInt256.ofNat 3, UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, id,
        UInt256.ofNat 32, solcAddrMask, interest, UInt256.ofNat 0,
        marketFieldWord (accrueSupplyAssetsAccounts σ ee id interest) ee id 5] ++ R)
      (twoWordHashMem id (UInt256.ofNat 3) mem) aw' rdata
      (accrueSupplyAssetsAccounts σ ee id interest) k' C' := by
  have hclean : UInt256.land (marketFieldWord σ ee id 0 + interest) uint128Mask =
      marketFieldWord σ ee id 0 + interest := halfWord_low_clean _ hc
  have hw : sstoreAccountMap ee.codeOwner σ (marketFieldSlot id 0)
      (UInt256.lor (UInt256.land (solcSlotWordAt (marketFieldSlot id 0) σ ee) (UInt256.lnot uint128Mask))
        (UInt256.land (marketFieldWord σ ee id 0 + interest) uint128Mask)) =
      accrueSupplyAssetsAccounts σ ee id interest := by rw [hclean]; rfl
  have hm : (UInt256.ofNat 3).toByteArray.write 0
      (id.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32 =
      twoWordHashMem id (UInt256.ofNat 3) mem := rfl
  have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem id (UInt256.ofNat 3) mem) = solcMappingSlot ⟨3⟩ id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  by_cases hf : marketFieldWord (accrueSupplyAssetsAccounts σ ee id interest) ee id 5 = ⟨0⟩
  · rw [if_pos hf]
    obtain ⟨aw1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_13675_fallthrough_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.append]; omega) hp
      (by rw [hw, hm, hh]; exact hf) h
    refine ⟨aw1, k1, C1, ?_⟩
    simpa only [morphoBlocks.morpho_block_13675_fallthrough_stack,
      morphoBlocks.morpho_block_13675_fallthrough_memory, hw, hm, hh] using rd1
  · rw [if_neg hf]
    obtain ⟨aw1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_13675_taken_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.append]; omega) hp
      (by rw [hw, hm, hh]; exact hf)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    refine ⟨aw1, k1, C1, ?_⟩
    simpa only [morphoBlocks.morpho_block_13675_taken_stack,
      morphoBlocks.morpho_block_13675_taken_memory, hw, hm, hh] using rd1

end Routines
end Benchmarks.Morpho.MorphoBlue
