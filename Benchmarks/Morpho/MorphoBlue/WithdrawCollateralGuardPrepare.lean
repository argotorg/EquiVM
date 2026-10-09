import Benchmarks.Morpho.MorphoBlue.SupplyCollateralMemory
import Benchmarks.Morpho.MorphoBlue.WithdrawAuthorization

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def withdrawCollateralGuardTail (id assets account receiver : UInt256)
    (R : List UInt256) : List UInt256 :=
  [account, UInt256.ofNat 5693, UInt256.ofNat 5701, id, UInt256.ofNat 0, receiver,
    UInt256.ofNat 128, UInt256.ofNat 32, solcAddrMask, receiver, assets,
    UInt256.ofNat 1211, UInt256.ofNat 0] ++ R

section Guards
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {aw assets account receiver : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat}
  {R : List UInt256}

theorem morphoWithdrawCollateralCreated (p : MarketParamsWords) (hstack : R.length + 24 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5498)
      ([UInt256.ofNat 128, account, solcAddrMask, receiver, assets, receiver, UInt256.ofNat 0] ++ R)
      (createMarketDecodedMem p) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      ([UInt256.isZero (UInt256.isZero (marketFieldWord σ ee p.id 4)), UInt256.ofNat 288, UInt256.ofNat 5562] ++
        withdrawCollateralGuardTail p.id assets account receiver R) (accruePublicMem p) aw' out σ k' C' := by
  have hid : keccakWord (UInt256.ofNat 128) (UInt256.ofNat 160) (createMarketDecodedMem p) = p.id :=
    marketParamsMem_hash p _ _ (by decide) (by native_decide) (by native_decide)
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_5498_packed
    (immWords := wordsOf (immStore v)) (by simp only [withdrawCollateralGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [morphoBlocks.morpho_block_5498_stack, morphoBlocks.morpho_block_5498_memory, hid] at rd1
  let mem := twoWordHashMem p.id (UInt256.ofNat 3) (createMarketDecodedMem p)
  have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem = solcMappingSlot ⟨3⟩ p.id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  change RD _ _ _ _ _
    ([UInt256.ofNat 585, UInt256.isZero (UInt256.isZero (UInt256.land
      (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem + UInt256.ofNat 2) σ ee)
      uint128Mask)), UInt256.ofNat 5562] ++ withdrawCollateralGuardTail p.id assets account receiver R)
    mem _ _ _ _ _ at rd1
  rw [hh] at rd1
  have hm := createMarketHeap_morpho ((createMarketDecodedHeap p).hash (by decide) p.id (UInt256.ofNat 3))
    (by decide) 64 (by decide) (lt_usize _ (by decide))
  obtain ⟨a2, k2, C2, rd2⟩ := morphoMarketCreatedMessage (v := v)
    (by simp only [withdrawCollateralGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega) hm (by decide)
    (by rw [morphoPatchedValidJumps v]; jump_dest) rd1
  have rd3 := morphoBlocks.morpho_block_585 (immWords := wordsOf (immStore v))
    (by simp only [withdrawCollateralGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  exact ⟨a2, _, _, rd3⟩

theorem morphoWithdrawCollateralAssets (p : MarketParamsWords) (hstack : R.length + 24 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5562)
      (withdrawCollateralGuardTail p.id assets account receiver R) (accruePublicMem p) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      ([UInt256.isZero (UInt256.isZero assets), UInt256.ofNat 352, UInt256.ofNat 5581] ++
        withdrawCollateralGuardTail p.id assets account receiver R) (supplyCollateralAssetsMem p) aw' out σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_5562 (immWords := wordsOf (immStore v))
    (by simp only [withdrawCollateralGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨a2, k2, C2, rd2⟩ := morphoZeroAssetsMessage (v := v)
    (by simp only [withdrawCollateralGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (accruePublicMemory p).1.freePtr (by decide) rd1
  have rd3 := morphoBlocks.morpho_block_5573 (immWords := wordsOf (immStore v))
    (by simp only [withdrawCollateralGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  exact ⟨a2, _, _, rd3⟩

theorem morphoWithdrawCollateralAddress (p : MarketParamsWords) (hstack : R.length + 24 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5581)
      (withdrawCollateralGuardTail p.id assets account receiver R) (supplyCollateralAssetsMem p) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      ([UInt256.isZero (UInt256.isZero receiver), UInt256.ofNat 416, UInt256.ofNat 5600] ++
        withdrawCollateralGuardTail p.id assets account receiver R) (supplyCollateralGuardMem p) aw' out σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_5581 (immWords := wordsOf (immStore v))
    (by simp only [withdrawCollateralGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨a2, k2, C2, rd2⟩ := morphoZeroAddressMessage (v := v)
    (by simp only [withdrawCollateralGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (supplyCollateralAssetsHeap p).1.freePtr (by decide) rd1
  have rd3 := morphoBlocks.morpho_block_5592 (immWords := wordsOf (immStore v))
    (by simp only [withdrawCollateralGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  exact ⟨a2, _, _, rd3⟩

end Guards

def withdrawCollateralGuardMem (p : MarketParamsWords) (ee : ExecutionEnv) (account : UInt256) : ByteArray :=
  morphoUnauthorizedMem (senderAuthorizedMem ee account (supplyCollateralGuardMem p))

theorem withdrawCollateralGuardHeap (p : MarketParamsWords) (ee : ExecutionEnv) (account : UInt256) :
    CreateMarketHeap p 544 (withdrawCollateralGuardMem p ee account) ∧
      morphoErrorLength (withdrawCollateralGuardMem p ee account) (UInt256.ofNat 480) = UInt256.ofNat 12 :=
  (senderAuthorizedMem_createHeap (supplyCollateralGuardHeap p).1 (by decide) ee account).message
    (by decide) (by decide) _ _

theorem withdrawCollateralGuardMem_zero96 (p : MarketParamsWords) (ee : ExecutionEnv) (account : UInt256) :
    memLoad (UInt256.ofNat 96) (withdrawCollateralGuardMem p ee account) = UInt256.ofNat 0 := by
  have hzero := supplyCollateralCastMem_zero96 p
  rw [supplyCollateralCastMem, uint128ErrorMem,
    (supplyCollateralGuardHeap p).1.messageLoad (by decide) (by decide) _ _ _ (by decide) (by decide)] at hzero
  have hm := senderAuthorizedMem_createHeap (supplyCollateralGuardHeap p).1 (by decide) ee account
  rw [withdrawCollateralGuardMem, morphoUnauthorizedMem, hm.messageLoad (by decide) (by decide) _ _ _ (by decide) (by decide)]
  have hp := (senderAuthorizedMem_heap
    (createMarketHeap_morpho (supplyCollateralGuardHeap p).1 (by decide) 0 (by decide) (lt_usize _ (by decide))) ee account).2
  rw [memoryPrefix_memLoad hp _ (by decide) (by decide) (by rw [(supplyCollateralGuardHeap p).1.size]; decide)]
  exact hzero

theorem morphoWithdrawCollateralAuthorization {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {aw assets account receiver : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (p : MarketParamsWords) (hstack : R.length + 32 ≤ 1024)
    (hc : account.toNat < EVM.addressModulus)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5600)
      (withdrawCollateralGuardTail p.id assets account receiver R) (supplyCollateralGuardMem p) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      ([senderAuthorizedWord σ ee account, UInt256.ofNat 480, UInt256.ofNat 5620] ++
        withdrawCollateralGuardTail p.id assets account receiver R)
      (withdrawCollateralGuardMem p ee account) aw' out σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_5600 (immWords := wordsOf (immStore v))
    (by simp only [withdrawCollateralGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨a2, k2, C2, rd2⟩ := morphoSenderAuthorized (v := v)
    (by simp only [withdrawCollateralGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hc rd1
  have rd3 := morphoBlocks.morpho_block_5612 (immWords := wordsOf (immStore v))
    (by simp only [withdrawCollateralGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  have hm := senderAuthorizedMem_createHeap (supplyCollateralGuardHeap p).1 (by decide) ee account
  obtain ⟨a4, k4, C4, rd4⟩ := morphoUnauthorizedMessage (v := v)
    (by simp only [withdrawCollateralGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hm.freePtr (by decide) rd3
  have rd5 := morphoBlocks.morpho_block_585 (immWords := wordsOf (immStore v))
    (by simp only [withdrawCollateralGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd4
  exact ⟨a4, _, _, rd5⟩


end Benchmarks.Morpho.MorphoBlue
