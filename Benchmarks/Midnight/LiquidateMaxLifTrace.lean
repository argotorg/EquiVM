import Benchmarks.Midnight.MarketCollateralIndex
import Benchmarks.Midnight.MaxLifGas
import Benchmarks.Midnight.RuntimeBlocks_026

/-! Read the selected collateral's parameters and compute its maximum liquidation incentive. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def LiquidateMaxLifSafe (m : MarketData) (index : UInt256) : Prop :=
  ∃ hi : index.toNat < m.collaterals.length,
    MaxLifSafe m.collaterals[index.toNat].lltv m.collaterals[index.toNat].liquidationCursor

theorem midnightLiquidateMaxLif {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {m : MarketData} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 10 ≤ 1024)
    (hd : decodeCalldataMarket I.calldata 4 = some m)
    (rd : RD midnightBytecode I g s0 ⟨6477⟩ R mem aw rdata σ k C) :
    (¬ LiquidateMaxLifSafe m (calldataWord I.calldata 36) ∧ RDrev midnightBytecode g s0) ∨
    ∃ hi : (calldataWord I.calldata 36).toNat < m.collaterals.length,
      let c := m.collaterals[(calldataWord I.calldata 36).toNat]
      MaxLifSafe c.lltv c.liquidationCursor ∧ ∃ k' C', C ≤ C' ∧
        RD midnightBytecode I g s0 ⟨6540⟩
          (maxLif c.lltv c.liquidationCursor :: c.lltv :: R) mem aw rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_6477 (R := R) (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_6477_stack] at rd1
  rcases midnightMarketCollateralIndex (R := ⟨32⟩ :: R)
    (by simp only [List.length_cons]; omega) hd (by jump_dest) rd1 with
    ⟨hbad, hrev⟩ | ⟨hi, k2, C2, hc2, rd2⟩
  · exact Or.inl ⟨fun h ↦ hbad h.1, hrev⟩
  · have hf := marketCollateralPointer_fields hd hi
    have rd3 := midnightBlocks.midnight_block_6502 (R := R) (by omega) (by jump_dest) rd2
    simp only [midnightBlocks.midnight_block_6502_stack] at rd3
    change RD midnightBytecode I g s0 ⟨20488⟩
      ((⟨4⟩ + calldataWord I.calldata 4) :: (calldataWord I.calldata 4 + ⟨100⟩) ::
        ⟨5534⟩ :: ⟨6532⟩ :: ⟨64⟩ :: ⟨6540⟩ ::
        calldataWord I.calldata
          (marketCollateralPointer I.calldata (calldataWord I.calldata 36) + UInt256.ofNat 32).toNat :: R)
      mem aw rdata σ _ _ at rd3
    rw [hf.1] at rd3
    rcases midnightMarketCollateralIndex
      (R := ⟨64⟩ :: ⟨6540⟩ :: m.collaterals[(calldataWord I.calldata 36).toNat].lltv :: R)
      (by simp only [List.length_cons]; omega) hd (by jump_dest) rd3 with
      ⟨hbad, _⟩ | ⟨_, k4, C4, hc4, rd4⟩
    · exact (hbad hi).elim
    · have rd5 := midnightBlocks.midnight_block_6532 (R := R) (by omega) (by jump_dest) rd4
      simp only [midnightBlocks.midnight_block_6532_stack] at rd5
      have hcursor := hf.2
      rw [show UInt256.ofNat 64 = (⟨64⟩ : UInt256) from rfl] at hcursor
      simp only [calldataWord] at hcursor
      rw [hcursor] at rd5
      rcases midnightMaxLif_mono (by simp only [List.length_cons]; omega) (by jump_dest) rd5 with
        ⟨hbad, hrev⟩ | ⟨hsafe, k6, C6, hc6, rd6⟩
      · exact Or.inl ⟨fun h ↦ hbad h.2, hrev⟩
      · exact Or.inr ⟨hi, hsafe, k6, C6, by omega, rd6⟩

end Benchmarks.Midnight
