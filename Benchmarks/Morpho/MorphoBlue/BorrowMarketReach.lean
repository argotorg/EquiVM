import Benchmarks.Morpho.MorphoBlue.BorrowPositionRefine
import Benchmarks.Morpho.MorphoBlue.AccrueSourceMath

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def borrowSharesStoreTail (id assets shares account receiver : UInt256) (R : List UInt256) : List UInt256 :=
  [marketFieldSlot id 2, UInt256.lnot uint128Mask, account, UInt256.ofNat 3, UInt256.ofNat 0, uint128Mask,
    id, account, receiver, UInt256.ofNat 128, solcAddrMask, assets, receiver, UInt256.ofNat 32,
    shares, assets] ++ R

def borrowHealthTail (id assets shares account receiver : UInt256) (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat 3, UInt256.ofNat 0, uint128Mask, id, account, receiver, UInt256.ofNat 128, solcAddrMask,
    assets, receiver, UInt256.ofNat 32, shares, assets] ++ R

def borrowStoreTail (σ : AccountMap) (ee : ExecutionEnv) (id assets shares account receiver : UInt256)
    (R : List UInt256) : List UInt256 :=
  [uint128Mask, UInt256.lnot uint128Mask, solcSlotWordAt (marketFieldSlot id 2) σ ee,
    marketFieldSlot id 2, account] ++ borrowHealthTail id assets shares account receiver R

section Reach
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem out : ByteArray} {aw id assets shares account receiver value : UInt256} {σ : AccountMap}
  {k C : Nat} {R : List UInt256}

theorem morphoBorrowMarketSharesReachAdd (hstack : R.length + 36 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 8645)
      (shares :: borrowMarketTail id assets shares account receiver R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12664)
      ([marketFieldWord σ ee id 3, shares, UInt256.ofNat 8673] ++ borrowSharesStoreTail id assets shares account receiver R)
      (twoWordHashMem id (UInt256.ofNat 3) mem) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_8645_packed (immWords := wordsOf (immStore v))
    (by change R.length + 9 + 11 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  have hh : UInt256.ofNat 1 + keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem id (UInt256.ofNat 3) mem) = marketFieldSlot id 2 := by
    rw [u256_add_comm]
    exact marketBorrowSlot_hash id mem
  dsimp only [morphoBlocks.morpho_block_8645_stack, morphoBlocks.morpho_block_8645_memory] at rd1
  dsimp only [twoWordHashMem, wordAt32Mem, wordAt0Mem] at hh
  simp only [show (UInt256.ofNat 0).toNat = 0 from rfl, show (UInt256.ofNat 32).toNat = 32 from rfl] at rd1
  rw [hh] at rd1
  exact ⟨a1, k1, C1, rd1⟩

theorem morphoBorrowMarketSharesStore (hstack : R.length + 36 ≤ 1024) (hperm : ee.perm = true)
    (hc : value.toNat < 2 ^ 128)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 8673)
      (value :: borrowSharesStoreTail id assets shares account receiver R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15480)
      ([assets, UInt256.ofNat 8747] ++ borrowMarketTail id assets shares account receiver R)
      mem aw' out (storeMarketFieldAccounts σ ee id ⟨3, by decide⟩ value) k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_8673_packed (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 18 ≤ 1024; omega) hperm
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  change RD _ _ _ _ _ _ _ _ _
    (sstoreAccountMap ee.codeOwner σ (marketFieldSlot id 2)
      (UInt256.lor (UInt256.land (UInt256.lnot uint128Mask) (UInt256.shiftLeft value (UInt256.ofNat 128)))
        (UInt256.land uint128Mask (solcSlotWordAt (marketFieldSlot id 2) σ ee)))) _ _ at rd1
  rw [u256_land_comm (UInt256.lnot uint128Mask), uint128_shift_high_mask value hc,
    u256_land_comm uint128Mask, u256_lor_comm] at rd1
  exact ⟨a1, k1, C1, rd1⟩

theorem morphoBorrowMarketAssetsReachAdd (hstack : R.length + 36 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 8747)
      (assets :: borrowMarketTail id assets shares account receiver R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12664)
      ([marketFieldWord σ ee id 2, assets, UInt256.ofNat 8777] ++ borrowStoreTail σ ee id assets shares account receiver R)
      (twoWordHashMem id (UInt256.ofNat 3) mem) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_8747_packed (immWords := wordsOf (immStore v))
    (by change R.length + 9 + 13 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  have hh : UInt256.ofNat 1 + keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem id (UInt256.ofNat 3) mem) = marketFieldSlot id 2 := by
    rw [u256_add_comm]
    exact marketBorrowSlot_hash id mem
  dsimp only [morphoBlocks.morpho_block_8747_stack, morphoBlocks.morpho_block_8747_memory] at rd1
  dsimp only [twoWordHashMem, wordAt32Mem, wordAt0Mem] at hh
  simp only [show (UInt256.ofNat 0).toNat = 0 from rfl, show (UInt256.ofNat 32).toNat = 32 from rfl] at rd1
  rw [hh] at rd1
  exact ⟨a1, k1, C1, rd1⟩

theorem morphoBorrowStoreHealth (hstack : R.length + 36 ≤ 1024) (hperm : ee.perm = true)
    (hc : value.toNat < 2 ^ 128)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 8777)
      (value :: borrowStoreTail σ ee id assets shares account receiver R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13948)
      ([UInt256.ofNat 128, id, account, UInt256.ofNat 8794] ++ borrowHealthTail id assets shares account receiver R)
      mem aw' out (storeMarketFieldAccounts σ ee id ⟨2, by decide⟩ value) k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_8777_packed (immWords := wordsOf (immStore v))
    (by change R.length + 6 + 13 ≤ 1024; omega) hperm
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  change RD _ _ _ _ _ _ _ _ _
    (sstoreAccountMap ee.codeOwner σ (marketFieldSlot id 2)
      (UInt256.lor (UInt256.land (solcSlotWordAt (marketFieldSlot id 2) σ ee) (UInt256.lnot uint128Mask))
        (UInt256.land value uint128Mask))) _ _ at rd1
  have hclean : UInt256.land value uint128Mask = value := halfWord_low_clean value hc
  rw [hclean] at rd1
  exact ⟨a1, k1, C1, rd1⟩

end Reach
end Benchmarks.Morpho.MorphoBlue
