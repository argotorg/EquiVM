import Benchmarks.Morpho.MorphoBlue.LiquidateBadMathRefine
import Benchmarks.Morpho.MorphoBlue.SupplyMathReach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def liquidateBadLowField (borrow : Bool) : Fin 6 := if borrow then ⟨2, by decide⟩ else ⟨0, by decide⟩
def liquidateBadLowEntry (borrow : Bool) : UInt256 := if borrow then UInt256.ofNat 3014 else UInt256.ofNat 3077
def liquidateBadLowStore (borrow : Bool) : UInt256 := if borrow then UInt256.ofNat 3062 else UInt256.ofNat 3122

def liquidateBadLowStoreTail (borrow : Bool) (σ : AccountMap) (ee : ExecutionEnv)
    (id assets seized shares badAssets badShares srcOff len : UInt256) (R : List UInt256) : List UInt256 :=
  [uint128Mask, UInt256.lnot uint128Mask, solcSlotWordAt (marketFieldSlot id (liquidateBadLowField borrow)) σ ee,
    marketFieldSlot id (liquidateBadLowField borrow)] ++
    liquidateBadTail id assets seized shares badAssets badShares srcOff len R

def liquidateBadNextCastStack (borrow : Bool) (id assets seized shares badAssets badShares srcOff len : UInt256)
    (R : List UInt256) : List UInt256 :=
  (if borrow then [badAssets, UInt256.ofNat 3077] else [badShares, UInt256.ofNat 3140, UInt256.ofNat 3169]) ++
    liquidateBadTail id assets seized shares badAssets badShares srcOff len R

section Reach
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem out : ByteArray} {aw id assets seized shares badAssets badShares srcOff len value : UInt256} {σ : AccountMap}
  {k C : Nat} {R : List UInt256}

theorem liquidateBadBorrowStack (σ : AccountMap) (ee : ExecutionEnv) (mem : ByteArray)
    (id assets seized shares badAssets badShares srcOff len : UInt256) (R : List UInt256) :
    morphoBlocks.morpho_block_3014_stack (ee := ee) (mem := mem) (σ := σ)
      (x0 := badAssets) (x1 := UInt256.lnot uint128Mask) (x2 := badAssets) (x3 := badShares)
      (x4 := shares) (x5 := id) (x6 := srcOff) (x7 := len) (x8 := UInt256.ofNat 0)
      (R := [assets, seized, UInt256.ofNat 128] ++ R) =
      [marketFieldWord σ ee id 2, badAssets, UInt256.ofNat 3062] ++
        liquidateBadLowStoreTail true σ ee id assets seized shares badAssets badShares srcOff len R := by
  have hh := marketBorrowSlot_hash id mem
  dsimp only [twoWordHashMem, wordAt32Mem, wordAt0Mem] at hh
  dsimp only [morphoBlocks.morpho_block_3014_stack]
  simp only [show (UInt256.ofNat 0).toNat = 0 from rfl, show (UInt256.ofNat 32).toNat = 32 from rfl]
  rw [hh]
  rfl

theorem liquidateBadSupplyStack (σ : AccountMap) (ee : ExecutionEnv) (mem : ByteArray)
    (id assets seized shares badAssets badShares srcOff len : UInt256) (R : List UInt256) :
    morphoBlocks.morpho_block_3077_stack (ee := ee) (mem := mem) (σ := σ)
      (x0 := badAssets) (x1 := UInt256.lnot uint128Mask) (x2 := badAssets) (x3 := badShares)
      (x4 := shares) (x5 := id) (x6 := srcOff) (x7 := len) (x8 := UInt256.ofNat 0)
      (R := [assets, seized, UInt256.ofNat 128] ++ R) =
      [marketFieldWord σ ee id 0, badAssets, UInt256.ofNat 3122] ++
        liquidateBadLowStoreTail false σ ee id assets seized shares badAssets badShares srcOff len R := by
  have hh := marketSupplySlot_hash id mem
  dsimp only [twoWordHashMem, wordAt32Mem, wordAt0Mem] at hh
  dsimp only [morphoBlocks.morpho_block_3077_stack]
  simp only [show (UInt256.ofNat 0).toNat = 0 from rfl, show (UInt256.ofNat 32).toNat = 32 from rfl]
  rw [hh]
  rfl

theorem morphoLiquidateBadLowReachSupply (hstack : R.length + 40 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (liquidateBadLowEntry false)
      (badAssets :: liquidateBadTail id assets seized shares badAssets badShares srcOff len R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12846)
      ([marketFieldWord σ ee id (liquidateBadLowField false), badAssets, liquidateBadLowStore false] ++
        liquidateBadLowStoreTail false σ ee id assets seized shares badAssets badShares srcOff len R)
      (twoWordHashMem id (UInt256.ofNat 3) mem) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_3077_packed (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 16 ≤ 1024; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  rw [liquidateBadSupplyStack] at rd1
  exact ⟨a1, k1, C1, rd1⟩

theorem morphoLiquidateBadLowReachBorrow (hstack : R.length + 40 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (liquidateBadLowEntry true)
      (badAssets :: liquidateBadTail id assets seized shares badAssets badShares srcOff len R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12846)
      ([marketFieldWord σ ee id (liquidateBadLowField true), badAssets, liquidateBadLowStore true] ++
        liquidateBadLowStoreTail true σ ee id assets seized shares badAssets badShares srcOff len R)
      (twoWordHashMem id (UInt256.ofNat 3) mem) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_3014_packed (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 16 ≤ 1024; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  rw [liquidateBadBorrowStack] at rd1
  exact ⟨a1, k1, C1, rd1⟩

theorem morphoLiquidateBadLowReachSub (borrow : Bool) (hstack : R.length + 40 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (liquidateBadLowEntry borrow)
      (badAssets :: liquidateBadTail id assets seized shares badAssets badShares srcOff len R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12846)
      ([marketFieldWord σ ee id (liquidateBadLowField borrow), badAssets, liquidateBadLowStore borrow] ++
        liquidateBadLowStoreTail borrow σ ee id assets seized shares badAssets badShares srcOff len R)
      (twoWordHashMem id (UInt256.ofNat 3) mem) aw' out σ k' C' := by
  cases borrow
  · exact morphoLiquidateBadLowReachSupply hstack h
  · exact morphoLiquidateBadLowReachBorrow hstack h

theorem morphoLiquidateBadLowStore (borrow : Bool) (hstack : R.length + 40 ≤ 1024) (hperm : ee.perm = true)
    (hc : value.toNat < 2 ^ 128)
    (h : RD (deployedRuntime v) ee g s0 (liquidateBadLowStore borrow)
      (value :: liquidateBadLowStoreTail borrow σ ee id assets seized shares badAssets badShares srcOff len R)
      mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15480)
      (liquidateBadNextCastStack borrow id assets seized shares badAssets badShares srcOff len R)
      mem aw' out (storeMarketFieldAccounts σ ee id (liquidateBadLowField borrow) value) k' C' := by
  have hc' : UInt256.land value uint128Mask = value := halfWord_low_clean value hc
  cases borrow
  · obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_3122_packed (immWords := wordsOf (immStore v))
      (by change R.length + 8 + 8 ≤ 1024; omega) hperm (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    change RD _ _ _ _ _ _ _ _ _
      (sstoreAccountMap ee.codeOwner σ (marketFieldSlot id 0)
        (UInt256.lor (UInt256.land (solcSlotWordAt (marketFieldSlot id 0) σ ee) (UInt256.lnot uint128Mask))
          (UInt256.land value uint128Mask))) _ _ at rd1
    rw [hc'] at rd1
    exact ⟨a1, k1, C1, rd1⟩
  · obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_3062_packed (immWords := wordsOf (immStore v))
      (by change R.length + 9 + 7 ≤ 1024; omega) hperm (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    change RD _ _ _ _ _ _ _ _ _
      (sstoreAccountMap ee.codeOwner σ (marketFieldSlot id 2)
        (UInt256.lor (UInt256.land (solcSlotWordAt (marketFieldSlot id 2) σ ee) (UInt256.lnot uint128Mask))
          (UInt256.land value uint128Mask))) _ _ at rd1
    rw [hc'] at rd1
    exact ⟨a1, k1, C1, rd1⟩

end Reach
end Benchmarks.Morpho.MorphoBlue
