import Benchmarks.Midnight.LiquidateCollateralHead
import Benchmarks.Midnight.RuntimeBlocks_024

/-! Validated calldata lookup at the liquidation collateral index, reusable at every field read. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

-- GENERALIZES repeated collateral-array references using the already decoded market.
theorem midnightMarketCollateralReference {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret : UInt256} {m : MarketData} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 6 ≤ 1024)
    (hd : decodeCalldataMarket I.calldata 4 = some m)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨20488⟩
      ((⟨4⟩ + calldataWord I.calldata 4) :: (calldataWord I.calldata 4 + ⟨100⟩) :: ret :: R)
      mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD midnightBytecode I g s0 ret
      (UInt256.ofNat m.collaterals.length :: UInt256.ofNat (marketCollateralDataStart I.calldata) :: R)
      mem aw rdata σ k' C' := by
  obtain ⟨hr, hs, _⟩ := decodeCalldataMarket_data hd
  obtain ⟨ho, hn, he, hl, _⟩ := decodeCalldataMarket_collateralArray hd
  let base := UInt256.ofNat 4 + calldataWord I.calldata 4
  let field := calldataWord I.calldata 4 + UInt256.ofNat 100
  have hbase : base.toNat = 4 + (calldataWord I.calldata 4).toNat := by
    dsimp only [base]
    rw [u256_add_comm, uadd_word_ofNat_toNat _ 4 (by change _ < 2^256; omega)]
    omega
  have hfield : field.toNat = 4 + (calldataWord I.calldata 4).toNat + 96 := by
    dsimp only [field]
    rw [uadd_word_ofNat_toNat _ 100 (by change _ < 2^256; omega)]
    omega
  have hhead : (base + calldataWord I.calldata field.toNat).toNat =
      4 + (calldataWord I.calldata 4).toNat +
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat + 96)).toNat := by
    rw [uadd_toNat, hbase, hfield, Nat.mod_eq_of_lt (by change _ < 2^256; omega)]
  have hp : UInt256.ofNat 32 + (base + calldataWord I.calldata field.toNat) =
      UInt256.ofNat (marketCollateralDataStart I.calldata) := by
    apply u256_inj
    rw [u256_add_comm, uadd_word_ofNat_toNat _ 32 (by rw [hhead]; change _ < 2^256; omega),
      hhead, UInt256.toNat_ofNat_of_lt (by
        dsimp only [marketCollateralDataStart]; change _ < 2^256; omega)]
    rfl
  have hcount : calldataWord I.calldata (base + calldataWord I.calldata field.toNat).toNat =
      UInt256.ofNat m.collaterals.length := by
    rw [hhead, hl, u256_ofNat_toNat]
  obtain ⟨k1, C1, hc1, rd1⟩ := midnightCollateralArrayReference (R := R) (base := base) (field := field) hstack hs
    (by rw [hbase]; omega) (by rw [hfield]; exact ho) (by rw [hhead]; exact hn)
    (by rw [hhead]; exact he) hret rd
  rw [hp, hcount] at rd1
  exact ⟨k1, C1, hc1, rd1⟩

end Benchmarks.Midnight
