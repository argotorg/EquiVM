import Benchmarks.Midnight.MarketCollateralIndex
import Benchmarks.Midnight.CalldataAddressRead

/-! The selected collateral's token address in decoded market calldata. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem marketCollateralPointer_token {bytes : ByteArray} {m : MarketData} {index : UInt256}
    (hd : decodeCalldataMarket bytes 4 = some m) (hi : index.toNat < m.collaterals.length) :
    calldataWord bytes (marketCollateralPointer bytes index).toNat =
      UInt256.ofNat m.collaterals[index.toNat].token.val := by
  obtain ⟨he, _⟩ := marketCollateralPointer_bound hd hi
  obtain ⟨_, hc⟩ := decodeCalldataMarket_collateralsAt hd
  obtain ⟨_, hcanon, hat⟩ := decodeCollateralElements_get hc index.toNat hi
  rw [he, hat]
  exact (addressWord_eq_ofNat_address hcanon.1).symm

theorem midnightMarketCollateralToken {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {m : MarketData} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 8 ≤ 1024)
    (hd : decodeCalldataMarket I.calldata 4 = some m)
    (rd : RD midnightBytecode I g s0 ⟨5508⟩ R mem aw rdata σ k C) :
    (¬ (calldataWord I.calldata 36).toNat < m.collaterals.length ∧ RDrev midnightBytecode g s0) ∨
    ∃ hi : (calldataWord I.calldata 36).toNat < m.collaterals.length,
      ∃ k' C', C ≤ C' ∧ RD midnightBytecode I g s0 ⟨5548⟩
        (UInt256.ofNat m.collaterals[(calldataWord I.calldata 36).toNat].token.val :: R)
        mem aw rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_5508 (R := R) (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_5508_stack] at rd1
  rcases midnightMarketCollateralIndex (R := ⟨5548⟩ :: R)
    (by simp only [List.length_cons]; omega) hd (by jump_dest) rd1 with
      ⟨hbad, hr⟩ | ⟨hi, k2, C2, hc2, rd2⟩
  · exact Or.inl ⟨hbad, hr⟩
  · have rd3 := midnightBlocks.midnight_block_5543
      (by simp only [List.length_cons]; omega) (by jump_dest) rd2
    obtain ⟨k4, C4, hc4, rd4⟩ := midnightCalldataAddressDirectRead
      (by omega) (marketCollateralPointer_token hd hi) (by jump_dest) rd3
    exact Or.inr ⟨hi, k4, C4, by omega, rd4⟩

end Benchmarks.Midnight
