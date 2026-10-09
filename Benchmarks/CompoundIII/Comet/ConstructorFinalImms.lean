import Benchmarks.CompoundIII.Comet.ConstructorFinalMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

-- LIBRARY CANDIDATE: division of two bounded natural words.
theorem u256_div_ofNat {a b : Nat} (ha : a < UInt256.size) (hb : b < UInt256.size) :
    UInt256.div (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat (a / b) := by
  apply u256_inj
  rw [udiv_toNat, UInt256.toNat_ofNat_of_lt ha, UInt256.toNat_ofNat_of_lt hb,
    UInt256.toNat_ofNat_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

set_option maxHeartbeats 800000 in
theorem constructorFinalImms_word {c : ConstructorConfig} {w assetList : UInt256} {i : Nat}
    (hi : i < 25) (hw : w.toNat ≤ 18) (ha : assetList.toNat < 2^160) :
    wordsOf (constructorFinalImms c w assetList)
      ((immutableReferences.map Prod.fst).getD i "") =
      (constructorImmutableValues c w assetList).getD i ⟨0⟩ := by
  have hrate (x : Fin (2^64)) :
      UInt256.div (UInt256.ofNat x.val) (UInt256.ofNat 31536000) =
        UInt256.ofNat (x.val / 31536000) :=
    u256_div_ofNat (lt_trans x.isLt (by decide)) (by decide)
  have hscale : UInt256.div (constructorScaleWord w) (UInt256.ofNat 1000000) =
      UInt256.ofNat (10^w.toNat / 1000000) :=
    u256_div_ofNat (lt_trans (constructorScale_bound hw) (by decide)) (by decide)
  have haddr : UInt256.ofNat (AccountAddress.ofUInt256 assetList).val = assetList := by
    rw [accountAddress_ofUInt256_eq_ofNat_toNat]
    exact addressWord_eq_ofNat_address ha
  interval_cases i <;>
    simp only [immutableReferences, List.map_cons, List.map_nil, List.getD_cons_zero,
      List.getD_cons_succ, wordsOf, constructorFinalImms, constructorRemainingImms,
      constructorScaleImms, constructorInitialImms, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, String.reduceBEq, Bool.false_eq_true, ite_false, ite_true] <;>
    simp only [valueToWord, wordOfInt_ofNat_toNat_gen,
      constructorImmutableValues, constructorRecordWord, ConstructorConfig.scalars,
      constructorAddressScalar, constructorUintScalar, constructorRateWord,
      List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ,
      Option.bind_some, Option.getD_some, pure, hscale, u256_ofNat_toNat]
  all_goals first | rfl | exact haddr | exact (hrate _).symm

set_option maxHeartbeats 800000 in
theorem constructorFinalImms_fit {c : ConstructorConfig} {w assetList : UInt256}
    (hw : w.toNat ≤ 18) (hn : c.assetConfigs.length ≤ 24) :
    immutablesFit contract (constructorFinalImms c w assetList) := by
  have hscale := constructorScale_bound hw
  intro d hd
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
  change i < 25 at hi
  interval_cases i <;>
    dsimp only [contract, Syntax.contractSyntax, List.getElem_cons_zero,
      List.getElem_cons_succ] <;>
    simp only [constructorFinalImms, constructorRemainingImms, constructorScaleImms,
      constructorInitialImms, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      String.reduceBEq, Bool.false_eq_true, ite_false, ite_true, Option.some.injEq] <;>
    refine ⟨_, rfl, ?_⟩ <;>
    simp only [elemValueFits, decide_eq_true_eq, Int.ofNat_eq_natCast] <;>
    refine ⟨Int.natCast_nonneg _, ?_⟩ <;> omega

end Benchmarks.CompoundIII.Comet
