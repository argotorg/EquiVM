import Benchmarks.Morpho.MetaMorphoV1_1.BorrowRateSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.InterestBalanceSimulation

/-! The complete active-accrual path, sharing the actual rate-model call with the source. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

theorem marketAccrualSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem market : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr params src elapsed ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (hstack : R.length + 21 ≤ 1024)
    (hcontract : frame.contract = contract)
    (hp : frame.locals.get? "marketParams" = some p.value)
    (hm : frame.locals.get? "market" = some (marketValue market))
    (hcursor : frame.locals.get? cursorName = some (uint256Value ptr))
    (helapsed : frame.locals.get? "elapsed" = some (uint256Value elapsed))
    (hfree : memLoad ⟨64⟩ mem = ptr) (hptr : ptr.toNat < 2 ^ 64)
    (hin : ptr.toNat ≤ mem.size) (hparamslo : 96 ≤ params.toNat) (hsrclo : 96 ≤ src.toNat)
    (hparams : params.toNat + 160 ≤ ptr.toNat) (hsrc : src.toNat + 192 ≤ ptr.toNat)
    (hparamsRead : MarketParamsLoads mem params p) (hc : MarketChecks market)
    (hmarket : ∀ off, off + 32 ≤ 192 →
      memLoad (src + UInt256.ofNat off) mem = calldataWord market off)
    (hs : SourceState s0 I σ evm)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨17069⟩
      (params :: (src + UInt256.ofNat 128) :: elapsed :: src :: ret :: R)
      mem aw rdata σ k C) :
    (ExecBlock config frame evm marketAccrualBody .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    (∃ (evm' : State) (result : BalanceSnapshot market mem src.toNat) (out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧
      accountStorageStateEq evm.accountMap evm'.accountMap ∧
      ExecBlock config frame evm marketAccrualBody (.ok result.frame evm') ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret
        (calldataWord market 96 :: result.borrowAssets :: result.supplyShares ::
          result.supplyAssets :: R) result.memory aw' out evm'.accountMap k' C') := by
  rcases borrowRateSimulation v p (by simp only [List.length_cons]; omega)
      hcontract hp hm hcursor hfree hptr hin hparamslo hsrclo hparams hsrc hparamsRead
      hc hmarket hs rd with
    ⟨hbad, hrev⟩ | ⟨evm', out, hcall, hs', hlong, hbound, halloc, hsource,
      hfree', hmem', hprefix, aw1, k1, C1, h1⟩
  · exact .inl ⟨hbad, hrev⟩
  have hn : (nextCursor ptr ⟨32⟩).toNat = ptr.toNat + 32 := by
    have ha := (allocationFits_aligned ptr ⟨32⟩ (by decide +kernel)).mp halloc
    exact uadd_word_ofNat_toNat ptr 32 (by change _ < 2 ^ 256; omega)
  have hread : ∀ off, off + 32 ≤ 192 →
      memLoad (src + UInt256.ofNat off) (borrowRateReadMemory mem ptr p market out) =
        calldataWord market off := by
    intro off hoff
    rw [wordWindowPrefix_load hprefix hsrclo (by omega) hsrc
      (by change src.toNat + 192 < 2 ^ 256; omega) off hoff]
    exact hmarket off hoff
  let nextFrame := borrowRateReserveFrame frame ptr (calldataWord out 0)
  have hm' : nextFrame.locals.get? "market" = some (marketValue market) := by
    rw [show nextFrame = borrowRateReserveFrame frame ptr (calldataWord out 0) from rfl,
      borrowRateReserveFrame, store_get_ne _ _ (by decide), borrowRateFrame,
      store_get_ne _ _ (by decide)]
    exact hm
  have hr' : nextFrame.locals.get? "borrowRate" = some (uint256Value (calldataWord out 0)) := by
    rw [show nextFrame = borrowRateReserveFrame frame ptr (calldataWord out 0) from rfl,
      borrowRateReserveFrame, store_get_ne _ _ (by decide)]
    exact store_get_self _ _ _
  have he' : nextFrame.locals.get? "elapsed" = some (uint256Value elapsed) := by
    rw [show nextFrame = borrowRateReserveFrame frame ptr (calldataWord out 0) from rfl,
      borrowRateReserveFrame, store_get_ne _ _ (by decide), borrowRateFrame,
      store_get_ne _ _ (by decide)]
    exact helapsed
  rcases interestBalanceSimulation (frame := nextFrame) v hstack hc hsrclo
      (by rw [hn]; omega) hmem' hfree' hread
      (by dsimp only [nextFrame, borrowRateReserveFrame, borrowRateFrame]; exact hcontract)
      hm' (store_get_self _ _ _) hr' he' hret h1 with
    ⟨hbad, hrev⟩ | ⟨result, hdone, hrd⟩
  · exact .inl ⟨hsource _ hbad, hrev⟩
  · exact .inr ⟨evm', result.rebase (hprefix.mono (by omega)) (le_refl _), out,
      hs', typedCallViaEVM_static_accountStorageStateEq hcall, hsource _ hdone, hrd⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
