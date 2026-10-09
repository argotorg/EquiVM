import Benchmarks.Morpho.MorphoBlue.AccrueMathRoutines
import Benchmarks.Morpho.MorphoBlue.Uint128Arithmetic
import Benchmarks.Morpho.MorphoBlue.MarketWrites

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- The compiler retains a redundant high-half mask after shifting the checked uint128.
theorem uint128_shift_high_mask (value : UInt256) (hc : value.toNat < 2 ^ 128) :
    UInt256.land (UInt256.shiftLeft value (UInt256.ofNat 128)) (UInt256.lnot uint128Mask) =
      UInt256.shiftLeft value (UInt256.ofNat 128) := by
  change UInt256.land _ (UInt256.ofNat (2 ^ 256 - 2 ^ 128)) = _
  apply u256_land_high_mask_eq_self _ (by decide)
  rw [shiftLeft128_toNat value hc]
  omega

section Routines
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
  {id rate interest shares ret : UInt256} {R : List UInt256}

theorem morphoStoreUint128High {slot value dest : UInt256}
    (hstack : R.length + 7 ≤ 1024) (hp : ee.perm = true)
    (hvalid : (D_J (deployedRuntime v) 0).contains dest = true) (hc : value.toNat < 2 ^ 128)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2278) (value :: slot :: dest :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 dest R mem aw rdata
      (sstoreAccountMap ee.codeOwner σ slot (setUint128HighWord (solcSlotWordAt slot σ ee) value)) k' C' := by
  obtain ⟨k1, C1, rd1⟩ := morphoBlocks.morpho_block_2278 (immWords := wordsOf (immStore v))
    hstack hp hvalid h
  have hm : UInt256.land (UInt256.shiftLeft value (UInt256.ofNat 128))
      (UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480) =
      UInt256.shiftLeft value (UInt256.ofNat 128) := uint128_shift_high_mask value hc
  rw [hm] at rd1
  exact ⟨k1, C1, rd1⟩

theorem morphoAccrueSharesReachAdd (hstack : R.length + 24 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13840)
      ([shares, UInt256.ofNat 13863, interest, shares] ++ accrueMathTail id rate ret R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12664)
      ([marketFieldWord σ ee id 1, shares, UInt256.ofNat 2278, marketFieldSlot id 1,
        UInt256.ofNat 13863, interest, shares] ++ accrueMathTail id rate ret R)
      (twoWordHashMem id (UInt256.ofNat 3) mem) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_13840_packed
    (immWords := wordsOf (immStore v))
    (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem id (UInt256.ofNat 3) mem) = marketFieldSlot id 1 := by
    have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem id (UInt256.ofNat 3) mem) = solcMappingSlot ⟨3⟩ id :=
      twoWordHashMem_solcMappingSlot_any _ _ _
    simpa only [marketFieldSlot, Nat.reduceDiv, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
      u256_add_zero] using hh
  change RD _ _ _ _ _
    ([UInt256.shiftRight (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem id (UInt256.ofNat 3) mem)) σ ee) (UInt256.ofNat 128), shares, UInt256.ofNat 2278,
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 3) mem),
      UInt256.ofNat 13863, interest, shares] ++ accrueMathTail id rate ret R)
    (twoWordHashMem id (UInt256.ofNat 3) mem) _ _ _ _ _ at rd1
  rw [hh] at rd1
  exact ⟨aw1, k1, C1, rd1⟩

theorem morphoAccrueSharesAddReverts (hstack : R.length + 24 ≤ 1024) (hc : shares.toNat < 2 ^ 128)
    (hover : 2 ^ 128 ≤ (marketFieldWord σ ee id 1).toNat + shares.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13840)
      ([shares, UInt256.ofNat 13863, interest, shares] ++ accrueMathTail id rate ret R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoAccrueSharesReachAdd (v := v) hstack h
  exact morphoCheckedAdd128Reverts (v := v)
    (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega)
    (halfWord_bound _ _) hc hover rd1

theorem morphoAccrueSharesStore (hstack : R.length + 24 ≤ 1024) (hp : ee.perm = true)
    (hc : shares.toNat < 2 ^ 128)
    (hfit : (marketFieldWord σ ee id 1).toNat + shares.toNat < 2 ^ 128)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13840)
      ([shares, UInt256.ofNat 13863, interest, shares] ++ accrueMathTail id rate ret R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13863)
      ([interest, shares] ++ accrueMathTail id rate ret R)
      (twoWordHashMem id (UInt256.ofNat 3) mem) aw' rdata
      (storeMarketFieldAccounts σ ee id ⟨1, by decide⟩ (marketFieldWord σ ee id 1 + shares)) k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoAccrueSharesReachAdd (v := v) hstack h
  obtain ⟨k2, C2, rd2⟩ := morphoCheckedAdd128Ok (v := v)
    (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (halfWord_bound _ _) hc hfit rd1
  obtain ⟨k3, C3, rd3⟩ := morphoStoreUint128High (v := v)
    (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega) hp
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by
      change (marketFieldWord σ ee id 1 + shares).toNat < 2 ^ 128
      rw [uadd_toNat, Nat.mod_eq_of_lt (show (marketFieldWord σ ee id 1).toNat + shares.toNat < UInt256.size by
        change _ < 2 ^ 256; omega)]
      exact hfit) rd2
  exact ⟨aw1, k3, C3, rd3⟩

end Routines
end Benchmarks.Morpho.MorphoBlue
