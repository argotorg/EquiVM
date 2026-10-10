import Benchmarks.Morpho.MetaMorphoV1_1.MarketAssetsMemory
import Benchmarks.Morpho.MetaMorphoV1_1.MarketBalanceFinal
import Benchmarks.Morpho.MetaMorphoV1_1.MarketFeeRoutines

/-! Composition of interest casts, balance updates, optional fees, and the four-word return. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

structure BalanceSnapshot (market before : ByteArray) (limit : Nat) where
  memory : ByteArray
  frame : Frame
  supplyAssets : UInt256
  supplyShares : UInt256
  borrowAssets : UInt256
  cursor : UInt256
  marketLocal : frame.locals.get? "market" =
    some (marketUpdatedValue market supplyAssets supplyShares borrowAssets)
  cursorLocal : frame.locals.get? cursorName = some (uint256Value cursor)
  free : memLoad ⟨64⟩ memory = cursor
  lower : 96 ≤ cursor.toNat
  upper : cursor.toNat < 2 ^ 64
  size : cursor.toNat ≤ memory.size
  preserves : MemoryPrefix before memory limit

def BalanceSnapshot.rebase {market before middle : ByteArray} {limit sourceLimit : Nat}
    (result : BalanceSnapshot market middle sourceLimit)
    (hprefix : MemoryPrefix before middle limit) (hle : limit ≤ sourceLimit) :
    BalanceSnapshot market before limit :=
  { memory := result.memory, frame := result.frame, supplyAssets := result.supplyAssets,
    supplyShares := result.supplyShares, borrowAssets := result.borrowAssets
    cursor := result.cursor
    marketLocal := result.marketLocal, cursorLocal := result.cursorLocal, free := result.free
    lower := result.lower, upper := result.upper, size := result.size
    preserves := hprefix.trans (result.preserves.mono hle) }

theorem narrowSumBound {a b : UInt256} (h : a.toNat + b.toNat < 2 ^ 128) :
    (a + b).toNat < 2 ^ 128 := by
  rw [uadd_toNat]
  exact lt_of_le_of_lt (Nat.mod_le _ _) h

set_option maxRecDepth 2000 in
theorem accruedBalanceSimulation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem market : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr src interest ret : UInt256} {R : List UInt256}
    {frame : Frame} {evm : State}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 21 ≤ 1024)
    (hc : MarketChecks market) (hlo : 96 ≤ src.toNat)
    (hsep : src.toNat + 192 ≤ ptr.toNat) (hmem : ptr.toNat ≤ mem.size)
    (hfree : memLoad ⟨64⟩ mem = ptr)
    (hread : ∀ off, off + 32 ≤ 192 →
      memLoad (src + UInt256.ofNat off) mem = calldataWord market off)
    (hcontract : frame.contract = contract)
    (hm : frame.locals.get? "market" = some (marketValue market))
    (hp : frame.locals.get? cursorName = some (uint256Value ptr))
    (hi : frame.locals.get? "interest" = some (uint256Value interest))
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨19367⟩
      (interest :: ⟨17353⟩ :: ⟨17362⟩ :: uint128Mask :: (src + UInt256.ofNat 64) ::
        (src + UInt256.ofNat 160) :: uint128Mask :: interest ::
        (src + UInt256.ofNat 32) :: src :: ret :: R) mem aw rdata σ k C) :
    (ExecBlock config frame evm (marketAccrualBody.drop 4) .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    (∃ result : BalanceSnapshot market mem src.toNat,
      ExecBlock config frame evm (marketAccrualBody.drop 4) (.ok result.frame evm) ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret
        (calldataWord market 96 :: result.borrowAssets :: result.supplyShares ::
          result.supplyAssets :: R) result.memory aw' rdata σ k' C') := by
  have hzero : memLoad src mem = calldataWord market 0 := by
    simpa only [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero] using
      hread 0 (by decide)
  have hadd (n : Nat) (hn : n ≤ 192) : (src + UInt256.ofNat n).toNat = src.toNat + n :=
    uadd_word_ofNat_toNat src n (by have h : ptr.toNat < UInt256.size := ptr.val.isLt; omega)
  rcases marketAssetsSimulation v (by simp only [List.length_cons]; omega) hlo hsep hmem
      hc.2.1 hc.2.2.2.1 hfree hzero (hread 64 (by decide)) hcontract hm hp hi rd with
    ⟨hbad, hrev⟩ | ⟨hfit, hsource, aw1, k1, C1, h1⟩
  · exact .inl ⟨hbad, hrev⟩
  let sa := calldataWord market 0 + interest
  let ba := calldataWord market 64 + interest
  let ptr2 := nextCursor (nextCursor ptr ⟨64⟩) ⟨64⟩
  let memA := marketAssetsMemory mem ptr src interest market
  let frameA := marketAssetsFrame frame market ptr interest
  have hsa : sa.toNat < 2 ^ 128 := narrowSumBound hfit.2.2.2
  have hba : ba.toNat < 2 ^ 128 := narrowSumBound hfit.1.2.2
  have hn1 := nextCursor64_toNat hfit.1.1
  have hn2 : ptr2.toNat = ptr.toNat + 128 := by
    dsimp only [ptr2]
    rw [nextCursor64_toNat hfit.2.1, hn1]
  have hptr2hi : ptr2.toNat < 2 ^ 64 := by
    have h := (allocationFits_aligned (nextCursor ptr ⟨64⟩) ⟨64⟩
      (by decide +kernel)).mp hfit.2.1
    rw [hn1] at h
    rw [hn2]
    change ptr.toNat + 64 + 64 < 2 ^ 64 at h
    omega
  have hmsize : memA.size = max mem.size (ptr.toNat + 128) :=
    marketAssetsMemory_size hlo hsep hfit.1.1
  have hmfree : memLoad ⟨64⟩ memA = ptr2 := marketAssetsMemory_free hlo hsep hfit.1.1
  have hprefix : MemoryPrefix mem memA src.toNat := marketAssetsMemory_prefix hsep hfit.1.1
  have hpres (off : Nat) (hmin : 32 ≤ off) (hmax : off + 32 ≤ 192)
      (hdis : off + 32 ≤ 64 ∨ 96 ≤ off) :
      memLoad (src + UInt256.ofNat off) memA = calldataWord market off := by
    rw [marketAssetsMemory_preserves hfit.1.1
      (by rw [hadd off (by omega)]; omega) (by rw [hadd off (by omega)]; omega)
      (by rw [hadd off (by omega)]; omega)
      (by rw [hadd off (by omega), hadd 64 (by decide)]; omega)
      (.inr (by rw [hadd off (by omega)]; omega))]
    exact hread off hmax
  have hshares := hpres 32 (by decide) (by decide) (.inl (by decide))
  have hborrowShares := hpres 96 (by decide) (by decide) (.inr (by decide))
  have hfee := hpres 160 (by decide) (by decide) (.inr (by decide))
  have hmarketA : frameA.locals.get? "market" =
      some (marketUpdatedValue market sa (calldataWord market 32) ba) := store_get_self _ _ _
  have hcursorA : frameA.locals.get? cursorName = some (uint256Value ptr2) := by
    rw [show frameA = marketAssetsFrame frame market ptr interest from rfl,
      marketAssetsFrame, marketUpdateFrame, store_get_ne _ _ (by decide)]
    exact cursorCastFrame_cursor _ _ _ _
  have hinterA : frameA.locals.get? "interest" = some (uint256Value interest) := by
    rw [show frameA = marketAssetsFrame frame market ptr interest from rfl,
      marketAssetsFrame, marketUpdateFrame, store_get_ne _ _ (by decide),
      cursorCastFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide)]
    exact marketBorrowFrame_interest market ptr interest hi
  obtain ⟨aw2, k2, C2, h2⟩ := marketFeeBranchRoutine v
    (by simp only [List.length_cons]; omega) hsa hc.2.2.2.2.2.2 hfee h1
  by_cases hz : calldataWord market 160 = ⟨0⟩
  · rw [if_pos hz] at h2
    obtain ⟨aw3, k3, C3, h3⟩ := marketBalanceWordsReturn v (by omega)
      hsa hc.2.2.1 hba hc.2.2.2.2.1 marketAssetsMemory_supply hshares
      (marketAssetsMemory_borrow hlo hsep hfit.1.1) hborrowShares hret h2
    let result : BalanceSnapshot market mem src.toNat :=
      { memory := memA, frame := frameA, supplyAssets := sa,
        supplyShares := calldataWord market 32, borrowAssets := ba, cursor := ptr2
        marketLocal := hmarketA, cursorLocal := hcursorA, free := hmfree
        lower := by rw [hn2]; omega
        upper := hptr2hi
        size := by rw [hn2, hmsize]; omega
        preserves := hprefix }
    exact .inr ⟨result, hsource.run (marketFeeSkipSource hmarketA hz), aw3, k3, C3, h3⟩
  · rw [if_neg hz] at h2
    rcases marketFeeSimulation (mem := memA) (market := market) (frame := frameA)
        (ptr := ptr2) (interest := interest) (sa := sa) (ss := calldataWord market 32) (ba := ba)
        (assetsPtr := src) (sharesPtr := src + UInt256.ofNat 32) (R := ret :: R)
        v (by simp only [List.length_cons]; omega)
        hfit.1.2.1 hc.2.2.2.2.2.2 hsa hc.2.2.1
        (by rw [hadd 32 (by decide)]; omega)
        (by rw [hadd 32 (by decide), hn2]; omega)
        (by rw [hadd 32 (by decide), hmsize]; omega) hmfree
        marketAssetsMemory_supply hshares
        (by dsimp only [frameA, marketAssetsFrame, marketBorrowFrame, marketUpdateFrame,
              cursorCastFrame]
            exact hcontract) hmarketA hinterA hcursorA h2 with
      ⟨hbad, hrev⟩ | ⟨hfeeFit, hfeeSource, aw3, k3, C3, h3⟩
    · refine .inl ⟨hsource.run ?_, hrev⟩
      rw [marketFeeStatements]
      exact ExecBlock.consRevert (ExecStmt.iteTrue
        (by rw [marketFeeConditionSource hmarketA]; simp only [ne_eq, hz, not_false_eq_true,
          decide_true]) hbad)
    let fs := marketFeeShares interest (calldataWord market 160) sa (calldataWord market 32)
    let ss := calldataWord market 32 + fs
    let memF := castStoreMemory memA ptr2 (src + UInt256.ofNat 32) ss
    let ptr3 := nextCursor ptr2 ⟨64⟩
    have hss : ss.toNat < 2 ^ 128 := narrowSumBound hfeeFit.2.2.2.2
    have hptr3 : ptr3.toNat = ptr2.toNat + 64 := nextCursor64_toNat hfeeFit.2.2.1
    have hptr3hi : ptr3.toNat < 2 ^ 64 := by
      rw [hptr3]
      exact (allocationFits_aligned ptr2 ⟨64⟩ (by decide +kernel)).mp hfeeFit.2.2.1
    have hkeep (off : Nat) (hmax : off + 32 ≤ 192)
        (hdis : off + 32 ≤ 32 ∨ 64 ≤ off) :
        memLoad (src + UInt256.ofNat off) memF = memLoad (src + UInt256.ofNat off) memA :=
      castStoreMemory_preserves (by rw [hadd off (by omega)]; omega)
        (by rw [hadd off (by omega), hn2]; omega)
        (by rw [hadd off (by omega), hmsize]; omega)
        (by rw [hadd off (by omega), hadd 32 (by decide)]; omega)
    have hkeepA : memLoad src memF = sa := by
      have h := hkeep 0 (by decide) (.inl (by decide))
      have h0 : memLoad src memF = memLoad src memA := by
        simpa only [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero] using h
      exact h0.trans marketAssetsMemory_supply
    have hkeepB : memLoad (src + UInt256.ofNat 64) memF = ba :=
      (hkeep 64 (by decide) (.inr (by decide))).trans
        (marketAssetsMemory_borrow hlo hsep hfit.1.1)
    have hkeepBS : memLoad (src + UInt256.ofNat 96) memF = calldataWord market 96 :=
      (hkeep 96 (by decide) (.inr (by decide))).trans hborrowShares
    obtain ⟨aw4, k4, C4, h4⟩ := marketBalanceWordsReturn v (by omega) hsa hss hba
      hc.2.2.2.2.1 hkeepA (castStoreMemory_field _ _ _ _) hkeepB hkeepBS hret h3
    let frameF := marketFeeResultFrame frameA market ptr2 interest sa (calldataWord market 32) ba
    have hcursorF : frameF.locals.get? cursorName = some (uint256Value ptr3) := by
      rw [show frameF = marketFeeResultFrame frameA market ptr2 interest
          sa (calldataWord market 32) ba from rfl,
        marketFeeResultFrame, marketUpdateFrame, store_get_ne _ _ (by decide)]
      exact cursorCastFrame_cursor _ _ _ _
    let result : BalanceSnapshot market mem src.toNat :=
      { memory := memF, frame := frameF, supplyAssets := sa, supplyShares := ss,
        borrowAssets := ba, cursor := ptr3
        marketLocal := store_get_self _ _ _
        cursorLocal := hcursorF
        free := castStoreMemory_free _ _ _ _ (by rw [hadd 32 (by decide)]; omega)
          (by rw [hadd 32 (by decide), hn2]; omega)
        lower := by rw [hptr3, hn2]; omega
        upper := hptr3hi
        size := by rw [hptr3, show memF.size = max memA.size (ptr2.toNat + 64) from
            castStoreMemory_size _ _ _ _ (by rw [hn2]; omega)
              (by rw [hadd 32 (by decide), hn2]; omega)]; omega
        preserves := hprefix.trans ((castStoreMemory_prefix _ _ _ _
          (by rw [hadd 32 (by decide), hn2]; omega)).mono (by rw [hadd 32 (by decide)]; omega)) }
    refine .inr ⟨result, hsource.run ?_, aw4, k4, C4, h4⟩
    rw [marketFeeStatements]
    exact ExecBlock.consNormal (ExecStmt.iteTrue
      (by rw [marketFeeConditionSource hmarketA]; simp only [ne_eq, hz, not_false_eq_true,
        decide_true]) hfeeSource)
      ExecBlock.nil

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
