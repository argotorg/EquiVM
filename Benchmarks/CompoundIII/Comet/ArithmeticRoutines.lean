import Benchmarks.CompoundIII.Comet.GetterCommon
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_039
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_040
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_041
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_042

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables
open cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: the solc division-based multiplication guard accepts every fitting product.
theorem checkedMulGuard_zero {x y : UInt256} (hfit : x.toNat * y.toNat < UInt256.size) :
    UInt256.land (UInt256.isZero (UInt256.isZero x))
      (UInt256.gt y (UInt256.div (UInt256.lnot ⟨0⟩) x)) = ⟨0⟩ := by
  by_cases hx : x = ⟨0⟩
  · rw [hx]
    change UInt256.land ⟨0⟩ _ = _
    exact u256_land_zero_left _
  · have hpos : 0 < x.toNat := by
      by_contra h
      exact hx (u256_inj (by change x.toNat = 0; omega))
    have hle : y.toNat ≤ (UInt256.div (UInt256.lnot ⟨0⟩) x).toNat := by
      rw [udiv_toNat, u256_lnot_zero_toNat]
      apply (Nat.le_div_iff_mul_le hpos).mpr
      rw [Nat.mul_comm]
      omega
    rw [ugt_zero hle, u256_land_zero_right]

theorem cometCheckedMul {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {x y ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hfit : x.toNat * y.toNat < UInt256.size)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨7799⟩ (x :: y :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret (UInt256.mul x y :: R)
      mem aw rdata σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_7799_fallthrough
    (immWords := wordsOf (immStore v)) (by simpa using hstack) (checkedMulGuard_zero hfit) h
  have r2 := cometWithExtendedAssetList_block_7815
    (immWords := wordsOf (immStore v)) (by omega) hvalid r1
  exact ⟨_, _, r2⟩

-- LIBRARY CANDIDATE: the complementary multiplication guard detects every overflowing product.
theorem checkedMulGuard_nonzero {x y : UInt256} (hover : UInt256.size ≤ x.toNat * y.toNat) :
    UInt256.land (UInt256.isZero (UInt256.isZero x))
      (UInt256.gt y (UInt256.div (UInt256.lnot ⟨0⟩) x)) ≠ ⟨0⟩ := by
  have hx : x ≠ ⟨0⟩ := by
    intro h
    rw [h] at hover
    change UInt256.size ≤ 0 * y.toNat at hover
    have : 0 < UInt256.size := by decide
    omega
  have hp : 0 < x.toNat := by
    by_contra h
    exact hx (u256_inj (by change x.toNat = 0; omega))
  have hlt : (UInt256.div (UInt256.lnot ⟨0⟩) x).toNat < y.toNat := by
    rw [udiv_toNat, u256_lnot_zero_toNat]
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    rw [Nat.mul_comm]
    have hsize : 0 < UInt256.size := by decide
    omega
  rw [ugt_one hlt, isZero_eq_zero_of_ne hx]
  decide

theorem cometCheckedMul_revert {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {x y : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hover : UInt256.size ≤ x.toNat * y.toNat)
    (h : RD (deployedRuntime v) ee g s0 ⟨7799⟩ (x :: y :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have r1 := cometWithExtendedAssetList_block_7799_taken
    (immWords := wordsOf (immStore v)) hstack (checkedMulGuard_nonzero hover)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have r2 := cometWithExtendedAssetList_block_7818
    (immWords := wordsOf (immStore v)) (by simpa using hstack)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  exact cometWithExtendedAssetList_block_7730
    (immWords := wordsOf (immStore v)) (by simpa using hstack) r2

-- LIBRARY CANDIDATE: the complemented-operand addition guard is equivalent to no overflow.
theorem checkedAddGuard_zero {x y : UInt256} (hfit : x.toNat + y.toNat < UInt256.size) :
    UInt256.gt x (UInt256.lnot y) = ⟨0⟩ := by
  apply ugt_zero
  rw [lnot_toNat_gen]
  change x.toNat ≤ UInt256.size - 1 - y.toNat
  omega

theorem checkedAddGuard_nonzero {x y : UInt256} (hover : UInt256.size ≤ x.toNat + y.toNat) :
    UInt256.gt x (UInt256.lnot y) ≠ ⟨0⟩ := by
  have hy := y.val.isLt
  have hg : UInt256.gt x (UInt256.lnot y) = ⟨1⟩ := by
    apply ugt_one
    rw [lnot_toNat_gen]
    change UInt256.size - 1 - y.toNat < x.toNat
    change y.toNat < UInt256.size at hy
    omega
  rw [hg]
  decide

theorem cometCheckedAdd {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {x y ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hfit : x.toNat + y.toNat < UInt256.size)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨8591⟩ (x :: y :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret ((x + y) :: R) mem aw rdata σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_8591_fallthrough
    (immWords := wordsOf (immStore v)) (by simpa using hstack) (checkedAddGuard_zero hfit) h
  have r2 := cometWithExtendedAssetList_block_8600
    (immWords := wordsOf (immStore v)) (by omega) hvalid r1
  exact ⟨_, _, r2⟩

theorem cometCheckedAdd_revert {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {x y : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024) (hover : UInt256.size ≤ x.toNat + y.toNat)
    (h : RD (deployedRuntime v) ee g s0 ⟨8591⟩ (x :: y :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have r1 := cometWithExtendedAssetList_block_8591_taken
    (immWords := wordsOf (immStore v)) hstack (checkedAddGuard_nonzero hover)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have r2 := cometWithExtendedAssetList_block_7859
    (immWords := wordsOf (immStore v)) (by simpa using hstack)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  exact cometWithExtendedAssetList_block_7730
    (immWords := wordsOf (immStore v)) (by simpa using hstack) r2

theorem cometSafe64 {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {x ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hfit : x.toNat < 2^64)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨8407⟩ (x :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret (x :: R) mem aw rdata σ k' C' := by
  have hmask : (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1)).toNat = 2^64 - 1 := by decide
  have hg := ugt_zero (a := x) (b := UInt256.sub
    (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))
    (by rw [hmask]; omega)
  have r1 := cometWithExtendedAssetList_block_8407_fallthrough
    (immWords := wordsOf (immStore v)) (by simpa using hstack) hg h
  have r2 := cometWithExtendedAssetList_block_8424
    (immWords := wordsOf (immStore v)) (by omega) hvalid r1
  simp only [cometWithExtendedAssetList_block_8424_stack] at r2
  rw [u256LandMaskCleanOfToNat x _ hmask hfit] at r2
  exact ⟨_, _, r2⟩

theorem cometSafe64_revert {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {x : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hfit : ¬ x.toNat < 2^64)
    (h : RD (deployedRuntime v) ee g s0 ⟨8407⟩ (x :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hmask : (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1)).toNat = 2^64 - 1 := by decide
  have hg : UInt256.gt x (UInt256.sub
      (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1)) ≠ ⟨0⟩ := by
    rw [ugt_one (by rw [hmask]; omega)]
    decide
  have r1 := cometWithExtendedAssetList_block_8407_taken
    (immWords := wordsOf (immStore v)) (by omega) hg
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  exact cometWithExtendedAssetList_block_8427
    (immWords := wordsOf (immStore v))
    (by simpa [cometWithExtendedAssetList_block_8407_taken_stack] using hstack) r1

end Benchmarks.CompoundIII.Comet
