import Benchmarks.Midnight.MarketCalldataHead

/-! Individual records in a successfully decoded calldata collateral array. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem decodeCollateralElements_get {n start : Nat} {bytes : ByteArray}
    {values : List CollateralData} (h : decodeCollateralElements n bytes start = some values)
    (i : Nat) (hi : i < values.length) :
    start + 128 * i + 128 ≤ bytes.size ∧
      CollateralData.canonicalAt bytes (start + 128 * i) ∧
      values[i] = CollateralData.at bytes (start + 128 * i) := by
  induction n generalizing start values i with
  | zero =>
    simp only [decodeCollateralElements, Option.some.injEq] at h
    subst values
    simp only [List.length_nil] at hi
    omega
  | succ n ih =>
    rw [decodeCollateralElements] at h
    split at h
    · rename_i hh
      cases hd : decodeCollateralElements n bytes (start + 128) with
      | none => simp [hd] at h
      | some rest =>
        simp only [hd, Option.map, Option.some.injEq] at h
        subst values
        cases i with
        | zero =>
          simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero]
          exact ⟨hh.1, hh.2, trivial⟩
        | succ i =>
          have hr := ih hd i (by simpa using hi)
          simpa only [List.getElem_cons_succ, Nat.mul_add, Nat.mul_one,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hr
    · cases h

theorem decodeCalldataMarket_data {bytes : ByteArray} {m : MarketData}
    (hd : decodeCalldataMarket bytes 4 = some m) :
    (calldataWord bytes 4).toNat < 2^64 ∧ bytes.size < 2^255 ∧
      decodeMarketData bytes (4 + (calldataWord bytes 4).toNat) = some m := by
  dsimp only [decodeCalldataMarket] at hd
  split at hd
  · cases hd
  · rename_i hh
    change ¬ (2^64 - 1 < _ ∨ 2^255 ≤ _) at hh
    exact ⟨by omega, by omega, hd⟩

theorem decodeCalldataMarket_collateralArray {bytes : ByteArray} {m : MarketData}
    (hd : decodeCalldataMarket bytes 4 = some m) :
    let base := 4 + (calldataWord bytes 4).toNat
    let relative := (calldataWord bytes (base + 96)).toNat
    let count := (calldataWord bytes (base + relative)).toNat
    relative < 2^64 ∧ count < 2^64 ∧
      base + relative + 32 + 128 * count ≤ bytes.size ∧
      m.collaterals.length = count ∧
      decodeCollateralElements count bytes (base + relative + 32) = some m.collaterals := by
  obtain ⟨_, _, hm⟩ := decodeCalldataMarket_data hd
  obtain ⟨_, _, ho, hh, hn, cs, hc, he⟩ := decodeMarketData_success hm
  have hl := decodeCollateralElements_length hc
  have hb := decodeCollateralElements_bound hc
  subst m
  exact ⟨ho, hn, by rcases hb with hz | hb <;> omega, hl, hc⟩

end Benchmarks.Midnight
