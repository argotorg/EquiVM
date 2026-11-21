import Benchmarks.Midnight.LiquidateCollateralUpdateSource
import Benchmarks.Midnight.LiquidateCollateralUpdateTrace
import Benchmarks.Midnight.LiquidateLoopSourceEntry

/-! Paired execution of liquidation's checked collateral subtraction and write. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem liquidateCollateralUpdate {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {frame : Frame}
    {mem rdata : ByteArray} {aw id index seized repaid borrower mode bitmap maxDebt price
      originalDebt badDebt d0 d1 d2 d3 root : UInt256} {credit : Nat}
    {receiver callback : AccountAddress} {data : ByteArray} {m : MarketData}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 12 ≤ 1024)
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data)
    (ha : LiquidateAccumulators frame bitmap maxDebt price originalDebt badDebt)
    (hcanon : borrower.toNat < EVM.addressModulus) (hi : calldataWord I.calldata 36 = index)
    (hseized : memLoad ⟨640⟩ mem = seized) (hs : SourceState s0 I σ evm)
    (hb : TransferBudget root credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨6744⟩
      (d0 :: d1 :: d2 :: d3 :: positionSlot id borrower :: R) mem aw rdata σ k C) :
    (ExecBlock config frame evm liquidateCollateralUpdateBody .reverted ∧
      RDrev midnightBytecode g s0) ∨
    (ExecBlock config frame evm liquidateCollateralUpdateBody .staticViolation ∧
      RDstatic midnightBytecode g s0) ∨
    (I.perm = true ∧ index.toNat < 128 ∧ ∃ frame' evm' σ' value aw' k' C',
      ExecBlock config frame evm liquidateCollateralUpdateBody (.ok frame' evm') ∧
      LiquidateSourceFrame frame' m id index seized repaid borrower mode receiver callback data ∧
      LiquidateAccumulators frame' bitmap maxDebt price originalDebt badDebt ∧
      frame'.locals.get? "newCollateral" = some (.int value.toNat) ∧ value.toNat < 2^128 ∧
      SourceState s0 I σ' evm' ∧ TransferBudget root credit mem aw' C' ∧
      RD midnightBytecode I g s0 ⟨6820⟩
        (value :: uint128Mask :: positionSlot id borrower :: R) mem aw' rdata σ' k' C') := by
  have hsource := liquidateCollateralUpdateSource (evm := evm) hf hcanon
  have htrace := midnightLiquidateCollateralUpdate hstack hi hseized hb rd
  have hload : (fun slot ↦ solcSlotWordAt slot σ I) =
      Stele.EVM.storageLoad evm evm.executionEnv.codeOwner :=
    funext (fun slot ↦ (hs.storageRead slot).symm)
  dsimp only at hsource htrace
  rw [hload] at htrace
  rcases htrace with ⟨hbad, hrev⟩ | ⟨hsafe, hp, hstatic⟩ | ⟨hsafe, hp, aw', k', C', hb', rd'⟩
  · rcases hsource with ⟨_, hx⟩ | ⟨hsafe, _, _⟩ | ⟨hsafe, _, _⟩
    · exact Or.inl ⟨hx, hrev⟩
    · exact (hbad hsafe).elim
    · exact (hbad hsafe).elim
  · rcases hsource.resolve_left (fun h ↦ h.1 hsafe) with ⟨_, _, hx⟩ | ⟨_, hp', _⟩
    · exact Or.inr (Or.inl ⟨hx, hstatic⟩)
    · simp only [hs.env, hp, Bool.false_eq_true] at hp'
  · rcases hsource.resolve_left (fun h ↦ h.1 hsafe) with ⟨_, hp', _⟩ | ⟨_, _, hx⟩
    · simp only [hs.env, hp, Bool.true_eq_false] at hp'
    · let old := collateralWord (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner)
        id borrower index
      let value := UInt256.sub old seized
      refine Or.inr (Or.inr ⟨hp, hsafe.1, _, _, _, value, aw', k', C', hx,
        (hf.insert "__c27" (.int seized.toNat) (by decide)).insert
          "newCollateral" (.int value.toNat) (by decide),
        (ha.insert "__c27" (.int seized.toNat) (by decide)).insert
          "newCollateral" (.int value.toNat) (by decide), wordLocal_get _ _ _, ?_,
        SourceState.collateralWrite hs id borrower index value, hb', rd'⟩)
      dsimp only [value]
      rw [usub_toNat hsafe.2.2]
      change old.toNat - seized.toNat < 2^128
      have hold : old.toNat < 2^128 := low128_lt _
      omega

end Benchmarks.Midnight
