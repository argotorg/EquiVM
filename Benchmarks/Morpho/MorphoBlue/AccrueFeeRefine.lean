import Benchmarks.Morpho.MorphoBlue.AccrueFeePreservation
import Benchmarks.Morpho.MorphoBlue.AccrueFeeWrites
import Benchmarks.Morpho.MorphoBlue.AccrueSourceFinish

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

structure AccrueLocals (p : MarketParamsWords) (locals : Store) (rate interest shares : UInt256)
    extends MarketLocals p locals : Prop where
  rate : locals.get? "borrowRate" = some (.int (Int.ofNat rate.toNat))
  interest : locals.get? "interest" = some (.int (Int.ofNat interest.toNat))
  shares : locals.get? "feeShares" = some (.int (Int.ofNat shares.toNat))

theorem AccrueLocals.evalRate {p locals rate interest shares} (h : AccrueLocals p locals rate interest shares)
    (imms : Store) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm (.var "borrowRate") =
      .ok (.int (Int.ofNat rate.toNat)) := by simp only [evalExpr?, h.rate, EvalResult.ofOption]

theorem AccrueLocals.evalInterest {p locals rate interest shares} (h : AccrueLocals p locals rate interest shares)
    (imms : Store) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm (.var "interest") =
      .ok (.int (Int.ofNat interest.toNat)) := by simp only [evalExpr?, h.interest, EvalResult.ofOption]

theorem AccrueLocals.evalShares {p locals rate interest shares} (h : AccrueLocals p locals rate interest shares)
    (imms : Store) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm (.var "feeShares") =
      .ok (.int (Int.ofNat shares.toNat)) := by simp only [evalExpr?, h.shares, EvalResult.ofOption]

def accrueFeeFinalLocals (locals : Store) (σ : AccountMap) (I : ExecutionEnv) (id interest : UInt256) : Store :=
  (accrueFeeCalcLocals locals σ I id interest).insert "__c7"
    (.int (Int.ofNat (accrueFeeShares σ I id interest).toNat))

theorem accrueFeeFinalLocals_invariant {p locals rate interest shares}
    (h : AccrueLocals p locals rate interest shares) (σ : AccountMap) (I : ExecutionEnv) :
    AccrueLocals p (accrueFeeFinalLocals locals σ I p.id interest) rate interest
      (accrueFeeShares σ I p.id interest) := by
  refine ⟨(accrueFeeCalcLocals_market p locals σ I interest h.toMarketLocals).insert "__c7" _ (by decide), ?_, ?_, ?_⟩
  · simp only [accrueFeeFinalLocals, accrueFeeCalcLocals, store_get_ne (k := "__c7") (a := "borrowRate") _ _ (by decide), store_get_ne (k := "feeShares") (a := "borrowRate") _ _ (by decide), store_get_ne (k := "__c6") (a := "borrowRate") _ _ (by decide), store_get_ne (k := "feeAmount") (a := "borrowRate") _ _ (by decide), h.rate]
  · simp only [accrueFeeFinalLocals, accrueFeeCalcLocals, store_get_ne (k := "__c7") (a := "interest") _ _ (by decide), store_get_ne (k := "feeShares") (a := "interest") _ _ (by decide), store_get_ne (k := "__c6") (a := "interest") _ _ (by decide), store_get_ne (k := "feeAmount") (a := "interest") _ _ (by decide), h.interest]
  · simp only [accrueFeeFinalLocals, accrueFeeCalcLocals, store_get_ne (k := "__c7") (a := "feeShares") _ _ (by decide), store_get_self]

def accrueFeeMem (σ : AccountMap) (I : ExecutionEnv) (id : UInt256) (mem : ByteArray) : ByteArray :=
  accrueFeeWritesMem σ I id (twoWordHashMem id (UInt256.ofNat 3) (twoWordHashMem id (UInt256.ofNat 3) mem))

section Refine
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 evm : State}
  {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
  {rate interest ret fp : UInt256} {R : List UInt256} {spare : Nat}

theorem morphoAccrueFeeRefineWithFee (p : MarketParamsWords) (locals imms : Store)
    (hstack : R.length + 40 ≤ 1024) (hp : ee.perm = true)
    (hs : SourceState s0 ee σ evm) (hm : MorphoHeap mem fp spare) (hb : 64 ≤ spare)
    (hl : AccrueLocals p locals rate interest ⟨0⟩)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13738)
      ([wad, UInt256.ofNat 3, UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, p.id,
        UInt256.ofNat 32, solcAddrMask, interest, UInt256.ofNat 0, marketFieldWord σ ee p.id 5] ++
        accrueMathTail p.id rate ret R) mem aw rdata σ k C) :
    (ExecBlock config { contract := contract, locals := locals, immutables := imms } evm accrueFeeBody .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    (∃ shares locals' evm' σ' aw' k' C',
      ExecBlock config { contract := contract, locals := locals, immutables := imms } evm accrueFeeBody
        (.ok { contract := contract, locals := locals', immutables := imms } evm') ∧
      AccrueLocals p locals' rate interest shares ∧ SourceState s0 ee σ' evm' ∧
      MorphoHeap (accrueFeeMem σ ee p.id mem) (fp + UInt256.ofNat 64) (spare - 64) ∧
      (marketFieldWord evm.accountMap evm.executionEnv p.id 5 ≠ UInt256.ofNat 0 →
        marketFieldWord evm'.accountMap evm'.executionEnv p.id 5 ≠ UInt256.ofNat 0) ∧
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13863)
        ([interest, shares] ++ accrueMathTail p.id rate ret R) (accrueFeeMem σ ee p.id mem) aw' rdata σ' k' C') := by
  by_cases hf : AccrueFeeFits σ ee p.id interest
  · have hf' : AccrueFeeFits evm.accountMap evm.executionEnv p.id interest := by
      simpa only [hs.env, ← hs.accounts] using hf
    have ab := morphoAccrueFeeCalcSource p locals imms evm interest _ hl.toMarketLocals
      (hl.evalInterest imms evm) hl.shares hf'
    let l := accrueFeeCalcLocals locals σ ee p.id interest
    let shares := accrueFeeShares σ ee p.id interest
    have hml : MarketLocals p l := accrueFeeCalcLocals_market p locals σ ee interest hl.toMarketLocals
    have hes : evalExpr? config { contract := contract, locals := l, immutables := imms } evm
        (.var "feeShares") = .ok (.int (Int.ofNat shares.toNat)) :=
      accrueFeeCalcLocals_eval p locals imms σ ee interest evm
    obtain ⟨aw1, k1, C1, rd1⟩ := morphoAccrueFeeMathOk (v := v) hstack hf h
    have hm1 := (hm.hash p.id (UInt256.ofNat 3)).hash p.id (UInt256.ofNat 3)
    by_cases hw : AccrueFeeWritesFit evm p.id shares
    · obtain ⟨σ2, aw2, k2, C2, hs2, rd2⟩ := morphoAccrueFeeWritesOk (v := v) (by omega) hp hs hm1 hb hw rd1
      have hsource := morphoAccrueFeeWritesSourceOk p l imms evm shares hml hes hw
      have hab : ABlock config evm { contract := contract, locals := locals, immutables := imms } accrueFeeBody
          { contract := contract, locals := l, immutables := imms } (accrueFeeBody.drop 3) := by
        simpa only [hs.env, ← hs.accounts] using ab
      exact Or.inr ⟨shares, accrueFeeFinalLocals locals σ ee p.id interest, _, σ2, aw2, k2, C2,
        hab.run hsource, accrueFeeFinalLocals_invariant hl σ ee, hs2, hm1.feeWrites σ ee p.id hb, accrueFeeSharesState_fee_nonzero evm p.id shares hw, rd2⟩
    · refine Or.inl ⟨?_, morphoAccrueFeeWritesReverts (v := v) (by omega) hp hs hm1 hb hw rd1⟩
      apply ab.run
      simpa only [hs.env, ← hs.accounts] using
        morphoAccrueFeeWritesSourceReverts p l imms evm shares hml hes hw
  · refine Or.inl ⟨?_, morphoAccrueFeeMathReverts (v := v) hstack hf h⟩
    apply morphoAccrueFeeCalcSourceReverts p locals imms evm interest hl.toMarketLocals (hl.evalInterest imms evm)
    simpa only [hs.env, ← hs.accounts] using hf

theorem morphoAccrueFeeRefine (p : MarketParamsWords) (locals imms : Store)
    (hstack : R.length + 40 ≤ 1024) (hp : ee.perm = true)
    (hs : SourceState s0 ee σ evm) (hm : MorphoHeap mem fp spare) (hb : 64 ≤ spare)
    (hl : AccrueLocals p locals rate interest ⟨0⟩)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13738)
      ([wad, UInt256.ofNat 3, UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, p.id,
        UInt256.ofNat 32, solcAddrMask, interest, UInt256.ofNat 0, marketFieldWord σ ee p.id 5] ++
        accrueMathTail p.id rate ret R) mem aw rdata σ k C) :
    (ExecBlock config { contract := contract, locals := locals, immutables := imms } evm accrueFeeBody .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    (∃ shares locals' evm' σ' aw' k' C',
      ExecBlock config { contract := contract, locals := locals, immutables := imms } evm accrueFeeBody
        (.ok { contract := contract, locals := locals', immutables := imms } evm') ∧
      AccrueLocals p locals' rate interest shares ∧ SourceState s0 ee σ' evm' ∧
      MorphoHeap (accrueFeeMem σ ee p.id mem) (fp + UInt256.ofNat 64) (spare - 64) ∧
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13863)
        ([interest, shares] ++ accrueMathTail p.id rate ret R) (accrueFeeMem σ ee p.id mem) aw' rdata σ' k' C') := by
  rcases morphoAccrueFeeRefineWithFee p locals imms hstack hp hs hm hb hl h with hr | hok
  · exact Or.inl hr
  · obtain ⟨shares, locals', evm', σ', aw', k', C', he, hl', hs', hm', _, rd⟩ := hok
    exact Or.inr ⟨shares, locals', evm', σ', aw', k', C', he, hl', hs', hm', rd⟩

end Refine
end Benchmarks.Morpho.MorphoBlue
