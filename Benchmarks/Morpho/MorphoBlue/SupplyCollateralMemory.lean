import Benchmarks.Morpho.MorphoBlue.ZeroAddressMessage
import Benchmarks.Morpho.MorphoBlue.ZeroAssetsMessage
import Benchmarks.Morpho.MorphoBlue.AccruePublicRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem createMarketDecodedMem_zero96 (p : MarketParamsWords) :
    memLoad (UInt256.ofNat 96) (createMarketDecodedMem p) = UInt256.ofNat 0 := by
  let base := marketParamsAllocatedMem solcFreePtrMem
  have hs : base.size = 96 := by native_decide
  have hg : 128 - base.size < USize.size := by rw [hs]; exact lt_usize _ (by decide)
  have hm : (writeWord base 128 p.loanToken).size = 160 := by
    rw [writeWord_size _ _ _ hg, hs]; rfl
  apply mloadWordValue_of_readWithPadding (by rw [(createMarketDecodedHeap p).size]; decide)
  rw [createMarketDecodedMem, marketParamsMem_asWordWrites p _ _ (by decide)]
  change (writeCascade (writeWord base 128 p.loanToken)
    (returnWordWrites 160 [p.collateralToken, p.oracle, p.irm, p.lltv])).readWithPadding 96 32 = _
  rw [writeCascade_read_preserved _ _ _ (returnWordWrites_preserveBelow _ _ _ _ _
    (by rw [hm]; exact USize.size_pos) (by rw [hm]; decide) (by decide))]
  have hgap := writeWord_read_gap32 base p.loanToken
  rw [hs] at hgap
  exact hgap

def supplyCollateralAssetsMem (p : MarketParamsWords) : ByteArray := morphoZeroAssetsMem (accruePublicMem p)
def supplyCollateralGuardMem (p : MarketParamsWords) : ByteArray := morphoZeroAddressMem (supplyCollateralAssetsMem p)
def supplyCollateralCastMem (p : MarketParamsWords) : ByteArray := uint128ErrorMem (supplyCollateralGuardMem p)

theorem supplyCollateralAssetsHeap (p : MarketParamsWords) :
    CreateMarketHeap p 416 (supplyCollateralAssetsMem p) ∧
      morphoErrorLength (supplyCollateralAssetsMem p) (UInt256.ofNat 352) = UInt256.ofNat 11 :=
  (accruePublicMemory p).1.message (by decide) (by decide) _ _

theorem supplyCollateralGuardHeap (p : MarketParamsWords) :
    CreateMarketHeap p 480 (supplyCollateralGuardMem p) ∧
      morphoErrorLength (supplyCollateralGuardMem p) (UInt256.ofNat 416) = UInt256.ofNat 12 :=
  (supplyCollateralAssetsHeap p).1.message (by decide) (by decide) _ _

theorem supplyCollateralCastHeap (p : MarketParamsWords) :
    CreateMarketHeap p 544 (supplyCollateralCastMem p) ∧
      morphoErrorLength (supplyCollateralCastMem p) (UInt256.ofNat 480) = UInt256.ofNat 20 :=
  (supplyCollateralGuardHeap p).1.message (by decide) (by decide) _ _

-- A word already in the allocated prefix is preserved by the compiler's error strings.
theorem CreateMarketHeap.messageLoad {p : MarketParamsWords} {free : Nat} {mem : ByteArray}
    (hm : CreateMarketHeap p free mem) (hlo : 288 ≤ free) (hhi : free + 32 < UInt256.size)
    (length payload off : UInt256) (hoff : 96 ≤ off.toNat) (hin : off.toNat + 32 ≤ free) :
    memLoad off (morphoErrorMem length payload mem) = memLoad off mem := by
  have hg : (UInt256.ofNat free).toNat - mem.size < USize.size := by
    rw [UInt256.toNat_ofNat_of_lt (by omega), hm.size, Nat.sub_self]; exact USize.size_pos
  have hb : (UInt256.ofNat free).toNat + 32 < UInt256.size := by
    rw [UInt256.toNat_ofNat_of_lt (by omega)]; exact hhi
  exact memoryPrefix_memLoad (morphoErrorMem_prefix length payload (by rw [hm.size]; omega)
    hm.freePtr hg hb) off hoff
    (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; exact hin) (by rw [hm.size]; exact hin)

theorem supplyCollateralCastMem_zero96 (p : MarketParamsWords) :
    memLoad (UInt256.ofNat 96) (supplyCollateralCastMem p) = UInt256.ofNat 0 := by
  rw [supplyCollateralCastMem, uint128ErrorMem,
    (supplyCollateralGuardHeap p).1.messageLoad (by decide) (by decide) _ _ _ (by decide) (by decide)]
  rw [supplyCollateralGuardMem, morphoZeroAddressMem,
    (supplyCollateralAssetsHeap p).1.messageLoad (by decide) (by decide) _ _ _ (by decide) (by decide)]
  rw [supplyCollateralAssetsMem, morphoZeroAssetsMem,
    (accruePublicMemory p).1.messageLoad (by decide) (by decide) _ _ _ (by decide) (by decide)]
  rw [accruePublicMem, marketCreatedErrorMem,
    ((createMarketDecodedHeap p).hash (by decide) p.id (UInt256.ofNat 3)).messageLoad
      (by decide) (by decide) _ _ _ (by decide) (by decide)]
  rw [twoWordHashMem_memLoad_above64 _ _ _ (by decide) (by rw [(createMarketDecodedHeap p).size]; decide)]
  exact createMarketDecodedMem_zero96 p

end Benchmarks.Morpho.MorphoBlue
