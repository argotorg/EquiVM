import Benchmarks.Morpho.MorphoBlue.AccrueMathRoutines
import Benchmarks.Morpho.MorphoBlue.SharesDownRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def accrueFeeAmount (σ : AccountMap) (I : ExecutionEnv) (id interest : UInt256) : UInt256 :=
  wMulDownResult interest (marketFieldWord σ I id 5)

def accrueNetSupply (σ : AccountMap) (I : ExecutionEnv) (id interest : UInt256) : UInt256 :=
  UInt256.sub (marketFieldWord σ I id 0) (accrueFeeAmount σ I id interest)

def accrueFeeShares (σ : AccountMap) (I : ExecutionEnv) (id interest : UInt256) : UInt256 :=
  sharesDownWord (accrueFeeAmount σ I id interest) (accrueNetSupply σ I id interest)
    (marketFieldWord σ I id 1)

def AccrueFeeFits (σ : AccountMap) (I : ExecutionEnv) (id interest : UInt256) : Prop :=
  interest.toNat * (marketFieldWord σ I id 5).toNat < UInt256.size ∧
  (accrueFeeAmount σ I id interest).toNat ≤ (marketFieldWord σ I id 0).toNat ∧
  SharesDownFits (accrueFeeAmount σ I id interest) (accrueNetSupply σ I id interest)
    (marketFieldWord σ I id 1)

section Routines
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
  {id rate interest ret : UInt256} {R : List UInt256}

theorem morphoAccrueFeeReachMul (hstack : R.length + 40 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13738)
      ([wad, UInt256.ofNat 3, UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, id,
        UInt256.ofNat 32, solcAddrMask, interest, UInt256.ofNat 0, marketFieldWord σ ee id 5] ++
        accrueMathTail id rate ret R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14395)
      ([interest, marketFieldWord σ ee id 5, UInt256.ofNat 13759, wad, UInt256.ofNat 3,
        UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, id, UInt256.ofNat 13774,
        UInt256.ofNat 32, UInt256.ofNat 13793, interest, solcAddrMask] ++ accrueMathTail id rate ret R)
      mem aw rdata σ k' C' := by
  exact ⟨_, _, morphoBlocks.morpho_block_13738 (immWords := wordsOf (immStore v))
    (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h⟩

theorem morphoAccrueFeeReachSub (hstack : R.length + 40 ≤ 1024)
    (hfit : interest.toNat * (marketFieldWord σ ee id 5).toNat < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13738)
      ([wad, UInt256.ofNat 3, UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, id,
        UInt256.ofNat 32, solcAddrMask, interest, UInt256.ofNat 0, marketFieldWord σ ee id 5] ++
        accrueMathTail id rate ret R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12833)
      ([marketFieldWord σ ee id 0, accrueFeeAmount σ ee id interest, UInt256.ofNat 13774,
        accrueFeeAmount σ ee id interest, UInt256.ofNat 13793, interest, solcAddrMask] ++
        accrueMathTail id rate ret R)
      (twoWordHashMem id (UInt256.ofNat 3) mem) aw' rdata σ k' C' := by
  obtain ⟨k1, C1, rd1⟩ := morphoAccrueFeeReachMul (v := v) hstack h
  obtain ⟨k2, C2, rd2⟩ := morphoCheckedMulOk (v := v)
    (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hfit rd1
  obtain ⟨aw3, k3, C3, rd3⟩ := morphoBlocks.morpho_block_13759_packed
    (immWords := wordsOf (immStore v))
    (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  have hm : (UInt256.ofNat 3).toByteArray.write 0
      (id.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32 =
      twoWordHashMem id (UInt256.ofNat 3) mem := rfl
  have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem id (UInt256.ofNat 3) mem) = marketFieldSlot id 0 := by
    have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem id (UInt256.ofNat 3) mem) = solcMappingSlot ⟨3⟩ id :=
      twoWordHashMem_solcMappingSlot_any _ _ _
    simpa only [marketFieldSlot, Nat.zero_div, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
      u256_add_zero] using hh
  refine ⟨aw3, k3, C3, ?_⟩
  simpa only [morphoBlocks.morpho_block_13759_stack, morphoBlocks.morpho_block_13759_memory, hm, hh] using rd3

theorem morphoAccrueFeeReachShares (hstack : R.length + 40 ≤ 1024)
    (hfit : interest.toNat * (marketFieldWord σ ee id 5).toNat < UInt256.size)
    (hsub : (accrueFeeAmount σ ee id interest).toNat ≤ (marketFieldWord σ ee id 0).toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13738)
      ([wad, UInt256.ofNat 3, UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, id,
        UInt256.ofNat 32, solcAddrMask, interest, UInt256.ofNat 0, marketFieldWord σ ee id 5] ++
        accrueMathTail id rate ret R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15336)
      ([accrueFeeAmount σ ee id interest, accrueNetSupply σ ee id interest, marketFieldWord σ ee id 1,
        UInt256.ofNat 13793, interest, solcAddrMask] ++ accrueMathTail id rate ret R)
      (twoWordHashMem id (UInt256.ofNat 3) (twoWordHashMem id (UInt256.ofNat 3) mem)) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoAccrueFeeReachSub (v := v) hstack hfit h
  obtain ⟨k2, C2, rd2⟩ := morphoCheckedSubOk (v := v)
    (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hsub rd1
  obtain ⟨aw3, k3, C3, rd3⟩ := morphoBlocks.morpho_block_13774_packed
    (immWords := wordsOf (immStore v))
    (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  let hm := twoWordHashMem id (UInt256.ofNat 3) (twoWordHashMem id (UInt256.ofNat 3) mem)
  have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) hm = marketFieldSlot id 1 := by
    have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) hm = solcMappingSlot ⟨3⟩ id :=
      twoWordHashMem_solcMappingSlot_any _ _ _
    simpa only [marketFieldSlot, Nat.reduceDiv, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
      u256_add_zero] using hh
  change RD _ _ _ _ _
    ([accrueFeeAmount σ ee id interest, accrueNetSupply σ ee id interest,
      UInt256.shiftRight (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) hm) σ ee)
        (UInt256.ofNat 128), UInt256.ofNat 13793, interest, solcAddrMask] ++ accrueMathTail id rate ret R)
    hm _ _ _ _ _ at rd3
  rw [hh] at rd3
  exact ⟨aw3, k3, C3, rd3⟩

theorem morphoAccrueFeeMathOk (hstack : R.length + 40 ≤ 1024) (hfit : AccrueFeeFits σ ee id interest)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13738)
      ([wad, UInt256.ofNat 3, UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, id,
        UInt256.ofNat 32, solcAddrMask, interest, UInt256.ofNat 0, marketFieldWord σ ee id 5] ++
        accrueMathTail id rate ret R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13793)
      ([accrueFeeShares σ ee id interest, interest, solcAddrMask] ++ accrueMathTail id rate ret R)
      (twoWordHashMem id (UInt256.ofNat 3) (twoWordHashMem id (UInt256.ofNat 3) mem)) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoAccrueFeeReachShares (v := v) hstack hfit.1 hfit.2.1 h
  obtain ⟨k2, C2, rd2⟩ := morphoSharesDownOk (v := v)
    (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hfit.2.2 rd1
  exact ⟨aw1, k2, C2, rd2⟩

theorem morphoAccrueFeeMathReverts (hstack : R.length + 40 ≤ 1024) (hbad : ¬ AccrueFeeFits σ ee id interest)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13738)
      ([wad, UInt256.ofNat 3, UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, id,
        UInt256.ofNat 32, solcAddrMask, interest, UInt256.ofNat 0, marketFieldWord σ ee id 5] ++
        accrueMathTail id rate ret R) mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  by_cases hm : interest.toNat * (marketFieldWord σ ee id 5).toNat < UInt256.size
  · by_cases hs : (accrueFeeAmount σ ee id interest).toNat ≤ (marketFieldWord σ ee id 0).toNat
    · obtain ⟨aw1, k1, C1, rd1⟩ := morphoAccrueFeeReachShares (v := v) hstack hm hs h
      exact morphoSharesDownReverts (v := v)
        (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega)
        (fun hf => hbad ⟨hm, hs, hf⟩) rd1
    · obtain ⟨aw1, k1, C1, rd1⟩ := morphoAccrueFeeReachSub (v := v) hstack hm h
      exact morphoCheckedSubReverts (v := v)
        (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega)
        (Nat.lt_of_not_ge hs) rd1
  · obtain ⟨k1, C1, rd1⟩ := morphoAccrueFeeReachMul (v := v) hstack h
    exact morphoCheckedMulReverts (v := v)
      (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega)
      (Nat.le_of_not_gt hm) rd1

end Routines
end Benchmarks.Morpho.MorphoBlue
