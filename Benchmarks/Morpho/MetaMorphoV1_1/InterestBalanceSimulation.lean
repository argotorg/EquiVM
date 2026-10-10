import Benchmarks.Morpho.MetaMorphoV1_1.AccruedBalanceSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.MarketInterestRoutines

/-! Taylor expansion, interest, asset updates, optional fees, and the final balances. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

theorem interestBalanceSimulation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem market : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr src rate elapsed ret : UInt256} {R : List UInt256}
    {frame : Frame} {evm : State}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 21 ≤ 1024)
    (hc : MarketChecks market) (hlo : 96 ≤ src.toNat)
    (hsep : src.toNat + 192 ≤ ptr.toNat) (hmem : ptr.toNat ≤ mem.size)
    (hfree : memLoad ⟨64⟩ mem = ptr)
    (hread : ∀ off, off + 32 ≤ 192 →
      memLoad (src + UInt256.ofNat off) mem = calldataWord market off)
    (hcontract : frame.contract = contract)
    (hm : frame.locals.get? "market" = some (marketValue market))
    (hp : frame.locals.get? cursorName = some (uint256Value ptr))
    (hr : frame.locals.get? "borrowRate" = some (uint256Value rate))
    (he : frame.locals.get? "elapsed" = some (uint256Value elapsed))
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨17239⟩
      (⟨17338⟩ :: elapsed :: (src + UInt256.ofNat 160) :: rate ::
        (src + UInt256.ofNat 64) :: (src + UInt256.ofNat 32) :: src :: ret :: R)
      mem aw rdata σ k C) :
    (ExecBlock config frame evm (marketAccrualBody.drop 2) .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    (∃ result : BalanceSnapshot market mem src.toNat,
      ExecBlock config frame evm (marketAccrualBody.drop 2) (.ok result.frame evm) ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret
        (calldataWord market 96 :: result.borrowAssets :: result.supplyShares ::
          result.supplyAssets :: R) result.memory aw' rdata σ k' C') := by
  rcases marketInterestSimulation v (by simp only [List.length_cons]; omega)
      hc.2.2.2.1 (hread 64 (by decide)) hcontract hm hr he rd with
    ⟨hbad, hrev⟩ | ⟨hsource, aw1, k1, C1, h1⟩
  · exact .inl ⟨hbad, hrev⟩
  let nextFrame := marketInterestFrame frame (calldataWord market 64) rate elapsed
  have hm' : nextFrame.locals.get? "market" = some (marketValue market) := by
    rw [show nextFrame = marketInterestFrame frame (calldataWord market 64) rate elapsed from rfl,
      marketInterestFrame, store_get_ne _ _ (by decide), marketTaylorFrame,
      store_get_ne _ _ (by decide)]
    exact hm
  have hp' : nextFrame.locals.get? cursorName = some (uint256Value ptr) := by
    rw [show nextFrame = marketInterestFrame frame (calldataWord market 64) rate elapsed from rfl,
      marketInterestFrame, store_get_ne _ _ (by decide), marketTaylorFrame,
      store_get_ne _ _ (by decide)]
    exact hp
  rcases accruedBalanceSimulation (frame := nextFrame) v hstack hc hlo hsep hmem hfree hread
      (by dsimp only [nextFrame, marketInterestFrame, marketTaylorFrame]; exact hcontract)
      hm' hp' (store_get_self _ _ _) hret h1 with
    ⟨hbad, hrev⟩ | ⟨result, hdone, hrd⟩
  · exact .inl ⟨hsource.run hbad, hrev⟩
  · exact .inr ⟨result, hsource.run hdone, hrd⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
