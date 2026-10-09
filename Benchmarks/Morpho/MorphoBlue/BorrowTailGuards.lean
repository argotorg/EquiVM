import Benchmarks.Morpho.MorphoBlue.BorrowHealthRefine
import Benchmarks.Morpho.MorphoBlue.HealthMessage
import Benchmarks.Morpho.MorphoBlue.MarketLiquidity

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def borrowEventTail (id assets shares account receiver : UInt256) (R : List UInt256) : List UInt256 :=
  [id, account, receiver, UInt256.ofNat 128, solcAddrMask, assets, receiver, UInt256.ofNat 32,
    shares, assets] ++ R

theorem morphoBorrowHealthCheck {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (z : Bool) (hstack : R.length + 24 ≤ 1024) (hm : MorphoHeap mem ptr 0) (hfit : ptr.toNat + 64 < 2 ^ 64)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 8794)
      ((if z then UInt256.ofNat 1 else UInt256.ofNat 0) :: R) mem aw out σ k C) :
    if z then
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 8811) R
        (morphoHealthMem mem) aw' out σ k' C' ∧ MorphoHeap (morphoHealthMem mem) (ptr + UInt256.ofNat 64) 0 ∧
        HeapAdvance mem ptr (morphoHealthMem mem) (ptr + UInt256.ofNat 64) 64
    else RDrev (deployedRuntime v) g s0 := by
  have rd0 := morphoBlocks.morpho_block_8794 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨a1, k1, C1, rd1⟩ := morphoHealthMessage (v := v)
    (by change R.length + 1 + 8 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hm.free hfit rd0
  have rd2 := morphoBlocks.morpho_block_8802 (immWords := wordsOf (immStore v))
    (by change R.length + 4 ≤ 1024; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  have hh := morphoErrorMem_properties_general (UInt256.ofNat 23)
    (UInt256.ofNat 47687999144296217495830161024900827403930695608853198639623507940336098869248)
    ptr mem hm.lower hm.free hm.size (by have hg := hm.gap; omega) (by change _ < 2 ^ 256; omega)
  cases z
  · exact morphoRequireFalseShort (v := v) (by omega) rfl
      (by rw [morphoHealthMem, hh.2.2]; decide) (by rw [morphoHealthMem, hh.2.2]; decide) rd2
  · obtain ⟨k3, C3, rd3⟩ := morphoRequireTrue (v := v) (by omega)
      (by rw [morphoPatchedValidJumps v]; jump_dest) (by decide) rd2
    refine ⟨a1, k3, C3, rd3, hm.errorMessage _ _ hfit, ?_⟩
    exact ⟨morphoErrorMem_prefix _ _ hm.size hm.free (by have hg := hm.gap; omega)
      (by change _ < 2 ^ 256; omega), uadd_word_ofNat_toNat ptr 64 (by change _ < 2 ^ 256; omega)⟩

theorem morphoBorrowLiquidity {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr id assets shares account receiver : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 36 ≤ 1024)
    (hm : MorphoHeap mem ptr 0) (hfit : ptr.toNat + 64 < 2 ^ 64)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 8811)
      (borrowHealthTail id assets shares account receiver R) mem aw out σ k C) :
    ((marketFieldWord σ ee id 0).toNat < (marketFieldWord σ ee id 2).toNat ∧ RDrev (deployedRuntime v) g s0) ∨
    ((marketFieldWord σ ee id 2).toNat ≤ (marketFieldWord σ ee id 0).toNat ∧ ∃ aw' k' C',
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 8850) (borrowEventTail id assets shares account receiver R)
        (morphoLiquidityMem (twoWordHashMem id (UInt256.ofNat 3) mem)) aw' out σ k' C' ∧
      MorphoHeap (morphoLiquidityMem (twoWordHashMem id (UInt256.ofNat 3) mem)) (ptr + UInt256.ofNat 64) 0 ∧
      HeapAdvance mem ptr (morphoLiquidityMem (twoWordHashMem id (UInt256.ofNat 3) mem)) (ptr + UInt256.ofNat 64) 64) := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_8811_packed (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 13 ≤ 1024; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  have hh := marketSupplySlot_hash id mem
  have hh2 := marketBorrowSlot_hash id mem
  change RD _ _ _ _ _
    ([UInt256.ofNat 8841, UInt256.isZero (UInt256.lt
      (UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 3) mem)) σ ee) uint128Mask)
      (UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 3) mem) + UInt256.ofNat 1) σ ee) uint128Mask))] ++
      borrowEventTail id assets shares account receiver R) (twoWordHashMem id (UInt256.ofNat 3) mem) _ _ _ _ _ at rd1
  rw [hh2, hh] at rd1
  change RD _ _ _ _ _
    ([UInt256.ofNat 8841, UInt256.isZero (UInt256.lt (marketFieldWord σ ee id 0) (marketFieldWord σ ee id 2))] ++
      borrowEventTail id assets shares account receiver R) (twoWordHashMem id (UInt256.ofNat 3) mem) _ _ _ _ _ at rd1
  have hm1 := hm.hash id (UInt256.ofNat 3)
  obtain ⟨a2, k2, C2, rd2⟩ := morphoLiquidityMessage (v := v)
    (by change R.length + 11 + 8 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hm1.free hfit rd1
  have rd3 := morphoBlocks.morpho_block_8841 (immWords := wordsOf (immStore v))
    (by change R.length + 10 + 4 ≤ 1024; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  have hp := morphoErrorMem_properties_general (UInt256.ofNat 22)
    (UInt256.ofNat 47687999144296217495830161024901027589677182894640623885992664163599792472064)
    ptr _ hm1.lower hm1.free hm1.size (by have hg := hm1.gap; omega) (by change _ < 2 ^ 256; omega)
  by_cases hf : (marketFieldWord σ ee id 2).toNat ≤ (marketFieldWord σ ee id 0).toNat
  · obtain ⟨k4, C4, rd4⟩ := morphoRequireTrue (v := v) (by change R.length + 10 + 4 ≤ 1024; omega)
      (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [ult_zero hf]; decide) rd3
    refine .inr ⟨hf, a2, k4, C4, rd4, hm1.errorMessage _ _ hfit, ?_⟩
    exact ⟨(twoWordHashMem_prefix id (UInt256.ofNat 3) mem ptr.toNat).trans
      (morphoErrorMem_prefix _ _ hm1.size hm1.free (by have hg := hm1.gap; omega) (by change _ < 2 ^ 256; omega)),
      uadd_word_ofNat_toNat ptr 64 (by change _ < 2 ^ 256; omega)⟩
  · have hf' := Nat.lt_of_not_ge hf
    exact .inl ⟨hf', morphoRequireFalseShort (v := v) (by change R.length + 10 + 11 ≤ 1024; omega)
      (by rw [ult_one hf']; decide) (by rw [morphoLiquidityMem, hp.2.2]; decide)
      (by rw [morphoLiquidityMem, hp.2.2]; decide) rd3⟩

end Benchmarks.Morpho.MorphoBlue
