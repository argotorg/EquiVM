import Benchmarks.Morpho.MorphoBlue.AccruePublicRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def setFeeTopic : UInt256 := UInt256.ofNat
  8872107603176126585573561987199299102136895706495482743817460101907661305691

def setFeeOwnerMem (p : MarketParamsWords) : ByteArray := morphoNotOwnerMem (createMarketDecodedMem p)
def setFeeCreatedMem (p : MarketParamsWords) : ByteArray :=
  marketCreatedErrorMem (twoWordHashMem p.id (UInt256.ofNat 3) (setFeeOwnerMem p))
def setFeeChangedMem (p : MarketParamsWords) : ByteArray :=
  morphoAlreadySetMem (twoWordHashMem p.id (UInt256.ofNat 3) (setFeeCreatedMem p))
def setFeeLimitMem (p : MarketParamsWords) : ByteArray :=
  morphoErrorMem (UInt256.ofNat 16)
    (UInt256.ofNat 49474313743923013073499841803577862786990104228205336467551667145325330563072)
    (setFeeChangedMem p)

theorem setFeeOwnerHeap (p : MarketParamsWords) :
    CreateMarketHeap p 352 (setFeeOwnerMem p) ∧
      morphoErrorLength (setFeeOwnerMem p) (UInt256.ofNat 288) = UInt256.ofNat 9 :=
  (createMarketDecodedHeap p).message (by decide) (by decide) _ _

theorem setFeeCreatedHeap (p : MarketParamsWords) :
    CreateMarketHeap p 416 (setFeeCreatedMem p) ∧
      morphoErrorLength (setFeeCreatedMem p) (UInt256.ofNat 352) = UInt256.ofNat 18 :=
  ((setFeeOwnerHeap p).1.hash (by decide) p.id (UInt256.ofNat 3)).message (by decide) (by decide) _ _

theorem setFeeChangedHeap (p : MarketParamsWords) :
    CreateMarketHeap p 480 (setFeeChangedMem p) ∧
      morphoErrorLength (setFeeChangedMem p) (UInt256.ofNat 416) = UInt256.ofNat 11 :=
  ((setFeeCreatedHeap p).1.hash (by decide) p.id (UInt256.ofNat 3)).message (by decide) (by decide) _ _

theorem setFeeLimitHeap (p : MarketParamsWords) :
    CreateMarketHeap p 544 (setFeeLimitMem p) ∧
      morphoErrorLength (setFeeLimitMem p) (UInt256.ofNat 480) = UInt256.ofNat 16 :=
  (setFeeChangedHeap p).1.message (by decide) (by decide) _ _

theorem setFeeOwnerMem_hash (p : MarketParamsWords) :
    keccakWord (UInt256.ofNat 128) (UInt256.ofNat 160) (setFeeOwnerMem p) = p.id := by
  have hm := createMarketDecodedHeap p
  have hr : (setFeeOwnerMem p).readWithPadding 128 160 = (createMarketDecodedMem p).readWithPadding 128 160 := by
    rw [setFeeOwnerMem, morphoNotOwnerMem, morphoErrorMem_asCascade _ _ _ _ hm.freePtr]
    apply writeCascade_read_preserved_len _ _ _ _ ?_ (by decide) (by decide)
    simp only [WindowDisjointFromWrites, hm.size]
    have hz : 32 < USize.size := lt_usize _ (by decide)
    simp only [show (UInt256.ofNat 288).toNat = 288 from rfl,
      show (UInt256.ofNat 288 + UInt256.ofNat 32).toNat = 320 from rfl]
    norm_num
  have hid := marketParamsMem_hash p (UInt256.ofNat 128) (marketParamsAllocatedMem solcFreePtrMem)
    (by decide) (by native_decide) (by native_decide)
  change keccakWord (UInt256.ofNat 128) (UInt256.ofNat 160) (createMarketDecodedMem p) = p.id at hid
  unfold keccakWord at hid ⊢
  simp only [show (UInt256.ofNat 128).toNat = 128 from rfl,
    show (UInt256.ofNat 160).toNat = 160 from rfl] at hid ⊢
  rw [hr]
  exact hid

def setFeeAccrueTail (id fee : UInt256) : List UInt256 :=
  [uint128Mask, UInt256.ofNat 9965, fee, UInt256.ofNat 32, setFeeTopic, id, UInt256.ofNat 0]
def setFeeAccrueStack (id fee : UInt256) : List UInt256 :=
  [UInt256.ofNat 128, id, UInt256.ofNat 9884] ++ setFeeAccrueTail id fee

end Benchmarks.Morpho.MorphoBlue
