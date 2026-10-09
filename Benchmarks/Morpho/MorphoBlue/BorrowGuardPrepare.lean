import Benchmarks.Morpho.MorphoBlue.SupplyGuards

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def borrowCreatedTail (id assets shares account receiver : UInt256) (R : List UInt256) : List UInt256 :=
  [assets, uint128Mask, id, account, UInt256.ofNat 0, UInt256.ofNat 128, shares, receiver,
    UInt256.ofNat 32, UInt256.ofNat 3, assets, shares] ++ R

def borrowInputTail (id assets shares account receiver : UInt256) (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat 0, uint128Mask, id, account, UInt256.isZero assets, UInt256.ofNat 128, shares, receiver,
    UInt256.ofNat 32, UInt256.ofNat 3, assets, shares] ++ R

def borrowAccrueTail (id assets shares account receiver : UInt256) (R : List UInt256) : List UInt256 :=
  [UInt256.isZero assets, shares, UInt256.ofNat 0, uint128Mask, id, account, receiver, UInt256.ofNat 128,
    solcAddrMask, receiver, UInt256.ofNat 32, UInt256.ofNat 3, assets, shares] ++ R

section Guards
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {aw assets shares account receiver : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat}
  {R : List UInt256}

theorem morphoBorrowCreated (p : MarketParamsWords) (hstack : R.length + 32 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 8336)
      ([receiver, account, shares, assets, UInt256.ofNat 128, UInt256.ofNat 0] ++ R)
      (createMarketDecodedMem p) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      ([UInt256.isZero (UInt256.isZero (marketFieldWord σ ee p.id 4)), UInt256.ofNat 288, UInt256.ofNat 8402] ++
        borrowCreatedTail p.id assets shares account receiver R) (accruePublicMem p) aw' out σ k' C' := by
  have hid : keccakWord (UInt256.ofNat 128) (UInt256.ofNat 160) (createMarketDecodedMem p) = p.id :=
    marketParamsMem_hash p _ _ (by decide) (by native_decide) (by native_decide)
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_8336_packed
    (immWords := wordsOf (immStore v)) (by simp only [borrowCreatedTail, borrowInputTail, borrowAccrueTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [morphoBlocks.morpho_block_8336_stack, morphoBlocks.morpho_block_8336_memory, hid] at rd1
  let mem := twoWordHashMem p.id (UInt256.ofNat 3) (createMarketDecodedMem p)
  have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem = solcMappingSlot ⟨3⟩ p.id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  change RD _ _ _ _ _
    ([UInt256.ofNat 585, UInt256.isZero (UInt256.isZero (UInt256.land
      (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem + UInt256.ofNat 2) σ ee)
      uint128Mask)), UInt256.ofNat 8402] ++ borrowCreatedTail p.id assets shares account receiver R)
    mem _ _ _ _ _ at rd1
  rw [hh] at rd1
  have hm := createMarketHeap_morpho ((createMarketDecodedHeap p).hash (by decide) p.id (UInt256.ofNat 3))
    (by decide) 64 (by decide) (lt_usize _ (by decide))
  obtain ⟨a2, k2, C2, rd2⟩ := morphoMarketCreatedMessage (v := v)
    (by simp only [borrowCreatedTail, borrowInputTail, borrowAccrueTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega) hm (by decide)
    (by rw [morphoPatchedValidJumps v]; jump_dest) rd1
  have rd3 := morphoBlocks.morpho_block_585 (immWords := wordsOf (immStore v))
    (by simp only [borrowCreatedTail, borrowInputTail, borrowAccrueTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  exact ⟨a2, _, _, rd3⟩

theorem morphoBorrowInput (p : MarketParamsWords) (hstack : R.length + 32 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 8402)
      (borrowCreatedTail p.id assets shares account receiver R) (accruePublicMem p) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      ([UInt256.xor (UInt256.isZero assets) (UInt256.isZero shares), UInt256.ofNat 352, UInt256.ofNat 8424] ++
        borrowInputTail p.id assets shares account receiver R) (supplyInputMem p) aw' out σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_8402 (immWords := wordsOf (immStore v))
    (by simp only [borrowCreatedTail, borrowInputTail, borrowAccrueTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨a2, k2, C2, rd2⟩ := morphoInconsistentInputMessage (v := v)
    (by simp only [borrowCreatedTail, borrowInputTail, borrowAccrueTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (accruePublicMemory p).1.freePtr (by decide) rd1
  have rd3 := morphoBlocks.morpho_block_8415 (immWords := wordsOf (immStore v))
    (by simp only [borrowCreatedTail, borrowInputTail, borrowAccrueTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  exact ⟨a2, _, _, rd3⟩

theorem morphoBorrowAddress (p : MarketParamsWords) (hstack : R.length + 32 ≤ 1024)
    (hc : receiver.toNat < EVM.addressModulus)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 8424)
      (borrowInputTail p.id assets shares account receiver R) (supplyInputMem p) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      ([UInt256.isZero (UInt256.isZero receiver), UInt256.ofNat 416, UInt256.ofNat 8469] ++
        borrowAccrueTail p.id assets shares account receiver R) (supplyGuardMem p) aw' out σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_8424 (immWords := wordsOf (immStore v))
    (by simp only [borrowCreatedTail, borrowInputTail, borrowAccrueTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [morphoBlocks.morpho_block_8424_stack] at rd1
  rw [show UInt256.ofNat 1461501637330902918203684832716283019655932542975 = solcAddrMask from rfl,
    solcAddrMask_clean hc] at rd1
  obtain ⟨a2, k2, C2, rd2⟩ := morphoZeroAddressMessage (v := v)
    (by simp only [borrowCreatedTail, borrowInputTail, borrowAccrueTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (supplyInputHeap p).1.freePtr (by decide) rd1
  have rd3 := morphoBlocks.morpho_block_8461 (immWords := wordsOf (immStore v))
    (by simp only [borrowCreatedTail, borrowInputTail, borrowAccrueTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  exact ⟨a2, _, _, rd3⟩

end Guards
end Benchmarks.Morpho.MorphoBlue
