import Benchmarks.UniswapV3.Pool.PositionUpdateModel
import Benchmarks.UniswapV3.Pool.PositionSnapshotMemory
import Benchmarks.UniswapV3.Pool.SignedWordZero

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

theorem positionUpdateLiquidityBefore_bounds (a : PositionUpdateArgs) (evm : EVM.State) :
    0 ≤ positionUpdateLiquidityBefore a evm ∧ positionUpdateLiquidityBefore a evm < 2 ^ 128 := by
  constructor
  · exact Int.ofNat_nonneg _
  · change ((positionUpdateLiquidityWord a evm).toNat : Int) < 2 ^ 128
    exact_mod_cast positionUpdateLiquidityWord_lt a evm

theorem positionUpdateLiquidityBefore_word (a : PositionUpdateArgs) (evm : EVM.State) :
    EVM.wordOfInt (positionUpdateLiquidityBefore a evm) = positionUpdateLiquidityWord a evm :=
  wordOfInt_ofNat_toNat _

theorem positionUpdateLiquidityNext_bounds (a : PositionUpdateArgs) (evm : EVM.State) :
    0 ≤ positionUpdateLiquidityNext a evm ∧ positionUpdateLiquidityNext a evm < 2 ^ 128 := by
  unfold positionUpdateLiquidityNext
  split_ifs
  · exact positionUpdateLiquidityBefore_bounds a evm
  · exact liquidityDeltaResult_bounds _ _

theorem positionUpdateLiquidityNext_toNat (a : PositionUpdateArgs) (evm : EVM.State) :
    (EVM.wordOfInt (positionUpdateLiquidityNext a evm)).toNat =
      (positionUpdateLiquidityNext a evm).toNat := by
  have hb := positionUpdateLiquidityNext_bounds a evm
  rw [wordOfInt_mod, Int.emod_eq_of_lt hb.1 (by omega)]

theorem positionUpdateLiquidityNext_word_lt (a : PositionUpdateArgs) (evm : EVM.State) :
    (EVM.wordOfInt (positionUpdateLiquidityNext a evm)).toNat < 2 ^ 128 := by
  rw [positionUpdateLiquidityNext_toNat]
  have hb := positionUpdateLiquidityNext_bounds a evm
  omega

theorem positionUpdateDelta_word (a : PositionUpdateArgs)
    (hlo : -(2 ^ 127 : Int) ≤ a.delta) (hhi : a.delta < 2 ^ 127) :
    UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt a.delta) = EVM.wordOfInt a.delta := by
  rw [signextend_wordOfInt ⟨128, by decide⟩ _ _ (by decide) (by decide),
    normalizeSint_eq_self ⟨128, by decide⟩ _ hlo hhi]

theorem positionSnapshotLoadLiquidity {mem : ByteArray} {p : UInt256}
    (a : PositionUpdateArgs) (evm : EVM.State)
    (hm : WordArrayMemory mem p (positionSnapshotWords a.key evm.accountMap evm.executionEnv))
    (hb : p.toNat + 160 < UInt256.size) :
    memLoad p mem = positionUpdateLiquidityWord a evm := by
  have h := WordArrayMemory.load hm 0 (by change 0 < 5; decide) hb
  simpa only [positionSnapshotWords, List.getElem_cons_zero, Nat.mul_zero,
    show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero] using h

theorem positionSnapshotLoadLast {mem : ByteArray} {p : UInt256}
    (a : PositionUpdateArgs) (evm : EVM.State) (second : Bool)
    (hm : WordArrayMemory mem p (positionSnapshotWords a.key evm.accountMap evm.executionEnv))
    (hb : p.toNat + 160 < UInt256.size) :
    memLoad (p + UInt256.ofNat (if second then 64 else 32)) mem =
      positionFieldWord a.key (if second then 2 else 1) 0 32 evm.accountMap evm.executionEnv := by
  cases second
  · exact WordArrayMemory.load hm 1 (by change 1 < 5; decide) hb
  · exact WordArrayMemory.load hm 2 (by change 2 < 5; decide) hb

end Benchmarks.UniswapV3.Pool
