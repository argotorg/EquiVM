import Benchmarks.Morpho.MetaMorphoV1_1.MarketAssetsSource
import Benchmarks.Morpho.MetaMorphoV1_1.CastStoreMemory

/-! Both interest casts and checked asset additions, up to the final supply-asset store. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

def marketBorrowMemory (mem : ByteArray) (ptr src interest : UInt256) (market : ByteArray) :
    ByteArray :=
  castStoreMemory mem ptr (src + UInt256.ofNat 64) (calldataWord market 64 + interest)

def marketAssetsInterimMemory (mem : ByteArray) (ptr src interest : UInt256)
    (market : ByteArray) : ByteArray :=
  uint128CastMemory (marketBorrowMemory mem ptr src interest market) (nextCursor ptr ⟨64⟩)

set_option maxRecDepth 2000 in
theorem marketAssetsRoutine {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem market : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr src interest : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 20 ≤ 1024)
    (hlo : 96 ≤ src.toNat) (hsep : src.toNat + 192 ≤ ptr.toNat)
    (hmem : ptr.toNat ≤ mem.size)
    (hs : (calldataWord market 0).toNat < 2 ^ 128)
    (hb : (calldataWord market 64).toNat < 2 ^ 128)
    (hfree : memLoad ⟨64⟩ mem = ptr)
    (hls : memLoad src mem = calldataWord market 0)
    (hlb : memLoad (src + UInt256.ofNat 64) mem = calldataWord market 64)
    (rd : RD (deployedRuntime v) I g s0 ⟨19367⟩
      (interest :: ⟨17353⟩ :: ⟨17362⟩ :: uint128Mask :: (src + UInt256.ofNat 64) ::
        (src + UInt256.ofNat 160) :: uint128Mask :: interest ::
        (src + UInt256.ofNat 32) :: src :: R) mem aw rdata σ k C) :
    (¬ marketAssetsFits ptr interest market ∧ RDrev (deployedRuntime v) g s0) ∨
    (marketAssetsFits ptr interest market ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ⟨17387⟩
        ((calldataWord market 0 + interest) :: uint128Mask :: (src + UInt256.ofNat 160) ::
          uint128Mask :: interest :: (src + UInt256.ofNat 32) :: src :: R)
        (marketAssetsInterimMemory mem ptr src interest market) aw' rdata σ k' C') := by
  have hadd (n : Nat) (hn : n ≤ 192) : (src + UInt256.ofNat n).toNat = src.toNat + n :=
    uadd_word_ofNat_toNat src n (by have h : ptr.toNat < UInt256.size := ptr.val.isLt; omega)
  rcases castAddFieldRoutine v (by simp only [List.length_cons]; omega)
      (by rw [hadd 64 (by decide)]; omega) (by rw [hadd 64 (by decide)]; omega)
      (by rw [hadd 64 (by decide)]; omega) hb hfree hlb
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd with
    ⟨hbad, hrev⟩ | ⟨hborrow, aw1, k1, C1, h1⟩
  · exact .inl ⟨fun h ↦ hbad h.1, hrev⟩
  have hsumBorrow : (calldataWord market 64 + interest).toNat < 2 ^ 128 := by
    rw [uadd_toNat, Nat.mod_eq_of_lt (show
      (calldataWord market 64).toNat + interest.toNat < UInt256.size by
        have h := hborrow.2.2
        change _ < 2 ^ 256
        omega)]
    exact hborrow.2.2
  have hmaskBorrow := u256LandMaskCleanOfToNat
    (calldataWord market 64 + interest) uint128Mask (by decide +kernel) hsumBorrow
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_17362_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  simp only [metaMorphoV1_1_block_17362_memory, hmaskBorrow] at h2
  have hn : (nextCursor ptr ⟨64⟩).toNat = ptr.toNat + 64 := by
    have h := (allocationFits_aligned ptr ⟨64⟩ (by decide +kernel)).mp hborrow.1
    exact uadd_word_ofNat_toNat ptr 64 (by change _ < 2 ^ 256; omega)
  have hf : memLoad ⟨64⟩ (marketBorrowMemory mem ptr src interest market) =
      nextCursor ptr ⟨64⟩ :=
    castStoreMemory_free _ _ _ _ (by rw [hadd 64 (by decide)]; omega)
      (by rw [hadd 64 (by decide)]; omega)
  have hm : (marketBorrowMemory mem ptr src interest market).size =
      max mem.size (ptr.toNat + 64) :=
    castStoreMemory_size _ _ _ _ (by omega) (by rw [hadd 64 (by decide)]; omega)
  by_cases halloc : allocationFits (nextCursor ptr ⟨64⟩) ⟨64⟩
  · obtain ⟨aw3, k3, C3, h3⟩ := uint128CastReturn v
      (by simp only [List.length_cons]; omega) hf halloc hborrow.2.1
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h2
    have hread : memLoad src (marketAssetsInterimMemory mem ptr src interest market) =
        calldataWord market 0 := by
      have he := (uint128CastMemory_prefix
        (marketBorrowMemory mem ptr src interest market) (nextCursor ptr ⟨64⟩)).load_preserved
        hlo (by rw [hn]; omega) (by rw [hm]; omega) src.val.isLt
      rw [show memLoad src (marketAssetsInterimMemory mem ptr src interest market) =
          memLoad src (marketBorrowMemory mem ptr src interest market) by
            simpa only [u256_ofNat_toNat] using he]
      rw [marketBorrowMemory, castStoreMemory_preserves hlo (by omega) (by omega)
        (.inl (by rw [hadd 64 (by decide)]; omega)), hls]
    have hmaskSupply := u256LandMaskCleanOfToNat
      (calldataWord market 0) uint128Mask (by decide +kernel) hs
    dsimp only [marketAssetsInterimMemory] at hread
    have h4 := metaMorphoV1_1_block_17378 (immWords := wordsOf (immStore v))
      (by omega) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
    simp only [metaMorphoV1_1_block_17378_stack, hread, hmaskSupply] at h4
    by_cases hsum : (calldataWord market 0).toNat + interest.toNat < 2 ^ 128
    · obtain ⟨k5, C5, h5⟩ := uint128AddReturn v
        (by simp only [List.length_cons]; omega) hs hborrow.2.1 hsum
        (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h4
      exact .inr ⟨⟨hborrow, halloc, hborrow.2.1, hsum⟩, _, k5, C5, h5⟩
    · exact .inl ⟨fun h ↦ hsum h.2.2.2, uint128AddRevert v
        (by simp only [List.length_cons]; omega) hs hborrow.2.1 (Nat.le_of_not_lt hsum) h4⟩
  · exact .inl ⟨fun h ↦ halloc h.2.1, uint128CastRevert v
      (by simp only [List.length_cons]; omega) hf (.inl halloc) h2⟩

theorem marketAssetsSimulation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem market : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr src interest : UInt256} {R : List UInt256}
    {frame : Frame} {evm : State}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 20 ≤ 1024)
    (hlo : 96 ≤ src.toNat) (hsep : src.toNat + 192 ≤ ptr.toNat)
    (hmem : ptr.toNat ≤ mem.size)
    (hs : (calldataWord market 0).toNat < 2 ^ 128)
    (hb : (calldataWord market 64).toNat < 2 ^ 128)
    (hfree : memLoad ⟨64⟩ mem = ptr)
    (hls : memLoad src mem = calldataWord market 0)
    (hlb : memLoad (src + UInt256.ofNat 64) mem = calldataWord market 64)
    (hcontract : frame.contract = contract)
    (hm : frame.locals.get? "market" = some (marketValue market))
    (hp : frame.locals.get? cursorName = some (uint256Value ptr))
    (hi : frame.locals.get? "interest" = some (uint256Value interest))
    (rd : RD (deployedRuntime v) I g s0 ⟨19367⟩
      (interest :: ⟨17353⟩ :: ⟨17362⟩ :: uint128Mask :: (src + UInt256.ofNat 64) ::
        (src + UInt256.ofNat 160) :: uint128Mask :: interest ::
        (src + UInt256.ofNat 32) :: src :: R) mem aw rdata σ k C) :
    (ExecBlock config frame evm (marketAccrualBody.drop 4) .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    (marketAssetsFits ptr interest market ∧
      ABlock config evm frame (marketAccrualBody.drop 4)
        (marketAssetsFrame frame market ptr interest) (marketAccrualBody.drop 12) ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨17387⟩
        ((calldataWord market 0 + interest) :: uint128Mask :: (src + UInt256.ofNat 160) ::
          uint128Mask :: interest :: (src + UInt256.ofNat 32) :: src :: R)
        (marketAssetsInterimMemory mem ptr src interest market) aw' rdata σ k' C') := by
  rcases marketAssetsRoutine v hstack hlo hsep hmem hs hb hfree hls hlb rd with
    ⟨hbad, hrev⟩ | ⟨hfit, hdone⟩
  · exact .inl ⟨marketAssetsSourceReverts hcontract hm hp hi hbad, hrev⟩
  · exact .inr ⟨hfit, marketAssetsSourcePrefix hcontract hm hp hi hfit, hdone⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
