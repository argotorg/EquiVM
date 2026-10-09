import Benchmarks.Morpho.MorphoBlue.SupplyGuards

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def repayCreatedTail (id assets shares account srcOff len : UInt256) (R : List UInt256) : List UInt256 :=
  [assets, shares, UInt256.ofNat 3, id, shares, srcOff, len, UInt256.ofNat 0, UInt256.ofNat 128,
    UInt256.ofNat 32, uint128Mask, assets, account] ++ R

def repayInputTail (id assets shares account srcOff len : UInt256) (R : List UInt256) : List UInt256 :=
  [shares, shares, UInt256.ofNat 3, id, UInt256.isZero assets, srcOff, len, UInt256.ofNat 0,
    UInt256.ofNat 128, UInt256.ofNat 32, uint128Mask, assets, account] ++ R

def repayAccrueTail (id assets shares account srcOff len : UInt256) (R : List UInt256) : List UInt256 :=
  [UInt256.isZero assets, shares, shares, UInt256.ofNat 3, id, account, srcOff, len, UInt256.ofNat 0,
    UInt256.ofNat 128, UInt256.ofNat 32, uint128Mask, assets, solcAddrMask] ++ R

section Guards
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {aw assets shares account srcOff len : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat}
  {R : List UInt256}

theorem morphoRepayCreated (p : MarketParamsWords) (hstack : R.length + 32 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 10448)
      ([len, srcOff, account, shares, assets, UInt256.ofNat 128, UInt256.ofNat 0] ++ R)
      (createMarketDecodedMem p) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      ([UInt256.isZero (UInt256.isZero (marketFieldWord σ ee p.id 4)), UInt256.ofNat 288, UInt256.ofNat 10512] ++
        repayCreatedTail p.id assets shares account srcOff len R) (accruePublicMem p) aw' out σ k' C' := by
  have hid : keccakWord (UInt256.ofNat 128) (UInt256.ofNat 160) (createMarketDecodedMem p) = p.id :=
    marketParamsMem_hash p _ _ (by decide) (by native_decide) (by native_decide)
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_10448_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 18 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [morphoBlocks.morpho_block_10448_stack, morphoBlocks.morpho_block_10448_memory, hid] at rd1
  let mem := twoWordHashMem p.id (UInt256.ofNat 3) (createMarketDecodedMem p)
  have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem = solcMappingSlot ⟨3⟩ p.id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  change RD _ _ _ _ _
    ([UInt256.ofNat 585, UInt256.isZero (UInt256.isZero (UInt256.land
      (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem + UInt256.ofNat 2) σ ee)
      uint128Mask)), UInt256.ofNat 10512] ++ repayCreatedTail p.id assets shares account srcOff len R)
    mem _ _ _ _ _ at rd1
  rw [hh] at rd1
  have hm := createMarketHeap_morpho ((createMarketDecodedHeap p).hash (by decide) p.id (UInt256.ofNat 3))
    (by decide) 64 (by decide) (lt_usize _ (by decide))
  obtain ⟨a2, k2, C2, rd2⟩ := morphoMarketCreatedMessage (v := v)
    (by change R.length + 15 + 9 ≤ 1024; omega) hm (by decide)
    (by rw [morphoPatchedValidJumps v]; jump_dest) rd1
  have rd3 := morphoBlocks.morpho_block_585 (immWords := wordsOf (immStore v))
    (by change R.length + 14 + 3 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  exact ⟨a2, _, _, rd3⟩

theorem morphoRepayInput (p : MarketParamsWords) (hstack : R.length + 32 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 10512)
      (repayCreatedTail p.id assets shares account srcOff len R) (accruePublicMem p) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      ([UInt256.xor (UInt256.isZero assets) (UInt256.isZero shares), UInt256.ofNat 352, UInt256.ofNat 10525] ++
        repayInputTail p.id assets shares account srcOff len R) (supplyInputMem p) aw' out σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_10512 (immWords := wordsOf (immStore v))
    (by change R.length + 8 + 8 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨a2, k2, C2, rd2⟩ := morphoInconsistentInputMessage (v := v)
    (by change R.length + 14 + 8 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (accruePublicMemory p).1.freePtr (by decide) rd1
  have rd3 := morphoBlocks.morpho_block_7585 (immWords := wordsOf (immStore v))
    (by change R.length + 8 + 9 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  exact ⟨a2, _, _, rd3⟩

theorem morphoRepayAddress (p : MarketParamsWords) (hstack : R.length + 32 ≤ 1024)
    (hc : account.toNat < EVM.addressModulus)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 10525)
      (repayInputTail p.id assets shares account srcOff len R) (supplyInputMem p) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      ([UInt256.isZero (UInt256.isZero account), UInt256.ofNat 416, UInt256.ofNat 10561] ++
        repayAccrueTail p.id assets shares account srcOff len R) (supplyGuardMem p) aw' out σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_10525 (immWords := wordsOf (immStore v))
    (by change R.length + 17 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [morphoBlocks.morpho_block_10525_stack] at rd1
  rw [show UInt256.ofNat 1461501637330902918203684832716283019655932542975 = solcAddrMask from rfl,
    solcAddrMask_clean hc] at rd1
  obtain ⟨a2, k2, C2, rd2⟩ := morphoZeroAddressMessage (v := v)
    (by change R.length + 15 + 8 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (supplyInputHeap p).1.freePtr (by decide) rd1
  have rd3 := morphoBlocks.morpho_block_5592 (immWords := wordsOf (immStore v))
    (by change R.length + 8 + 10 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  exact ⟨a2, _, _, rd3⟩

end Guards
end Benchmarks.Morpho.MorphoBlue
