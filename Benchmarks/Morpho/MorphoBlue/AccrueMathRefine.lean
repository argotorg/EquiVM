import Benchmarks.Morpho.MorphoBlue.AccrueAssetsRefine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

section Refine
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 evm : State}
  {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
  {rate elapsed ret fp : UInt256} {R : List UInt256} {spare : Nat}

theorem morphoAccrueMathRefineWithMemory (p : MarketParamsWords) (locals imms : Store)
    (hstack : R.length + 40 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem fp spare) (hb : 192 ≤ spare) (hl : MarketLocals p locals)
    (hr : locals.get? "borrowRate" = some (.int (Int.ofNat rate.toNat)))
    (he : locals.get? "elapsed" = some (.int (Int.ofNat elapsed.toNat)))
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13407)
      ([UInt256.ofNat 96, elapsed, solcAddrMask, p.id, UInt256.ofNat 32, UInt256.ofNat 3,
        UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, ret, rate] ++ R) mem aw rdata σ k C) :
    AccrueTailRefinesWithMemory v ee g s0 p imms locals evm (accrueIrmBody.drop 3) ret R (spare - 192) mem fp 128 := by
  have her : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm (.var "borrowRate") =
      .ok (.int (Int.ofNat rate.toNat)) := by simp only [evalExpr?, hr, EvalResult.ofOption]
  have hee : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm (.var "elapsed") =
      .ok (.int (Int.ofNat elapsed.toNat)) := by simp only [evalExpr?, he, EvalResult.ofOption]
  by_cases ht : TaylorFits rate elapsed
  · have hst := morphoAccrueTaylorStep locals imms rate elapsed evm her hee ht
    by_cases hi : (marketFieldWord σ ee p.id 2).toNat * (taylorWord rate elapsed).toNat < UInt256.size
    · have hi' : (marketFieldWord evm.accountMap evm.executionEnv p.id 2).toNat *
          (taylorWord rate elapsed).toNat < UInt256.size := by simpa only [hs.env, ← hs.accounts] using hi
      have hsi := morphoAccrueInterestStep p locals imms rate elapsed evm hl hi'
      obtain ⟨aw1, k1, C1, rd1⟩ := morphoAccrueInterestOk (v := v) hstack ht hi h
      let l := accrueCalcLocals locals rate elapsed (marketFieldWord σ ee p.id 2)
      have hab : StateBlock config { contract := contract, locals := locals, immutables := imms } evm
          (accrueIrmBody.drop 3) { contract := contract, locals := l, immutables := imms } evm (accrueIrmBody.drop 5) := by
        have hab : StateBlock config { contract := contract, locals := locals, immutables := imms } evm
            (accrueIrmBody.drop 3)
            { contract := contract, locals := accrueCalcLocals locals rate elapsed (marketFieldWord evm.accountMap evm.executionEnv p.id 2), immutables := imms }
            evm (accrueIrmBody.drop 5) := (StateBlock.start.step hst).step hsi
        simpa only [hs.env, ← hs.accounts] using hab
      have hl' : MarketLocals p l := accrueCalcLocals_market p locals rate elapsed _ hl
      have hr' : l.get? "borrowRate" = some (.int (Int.ofNat rate.toNat)) := by
        simp only [l, accrueCalcLocals, accrueTaylorLocals,
          store_get_ne (k := "interest") (a := "borrowRate") _ _ (by decide),
          store_get_ne (k := "__c1") (a := "borrowRate") _ _ (by decide), hr]
      have hi'' : l.get? "interest" = some (.int (Int.ofNat (accrueInterestWord σ ee p.id rate elapsed).toNat)) :=
        store_get_self _ _ _
      have hf := morphoAccrueAssetsRefineWithMemory (v := v) p l imms hstack hs (hm.hash p.id (UInt256.ofNat 3))
        hb hl' hr' hi'' hvalid rd1
      simpa only [Nat.zero_add] using
        (hf.memoryPrepend (heapAdvance_hash mem fp p.id (UInt256.ofNat 3))).prepend hab
    · refine .reverted (ExecBlock.consNormal hst (ExecBlock.consRevert ?_))
        (morphoAccrueMathReverts (v := v) hstack (Or.inr (Nat.le_of_not_gt hi)) h)
      apply morphoAccrueInterestReverts p locals imms rate elapsed evm hl
      simpa only [hs.env, ← hs.accounts] using Nat.le_of_not_gt hi
  · exact .reverted (ExecBlock.consRevert (morphoAccrueTaylorReverts locals imms rate elapsed evm her hee ht))
      (morphoAccrueMathReverts (v := v) hstack (Or.inl ht) h)

theorem morphoAccrueMathRefine (p : MarketParamsWords) (locals imms : Store)
    (hstack : R.length + 40 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem fp spare) (hb : 192 ≤ spare) (hl : MarketLocals p locals)
    (hr : locals.get? "borrowRate" = some (.int (Int.ofNat rate.toNat)))
    (he : locals.get? "elapsed" = some (.int (Int.ofNat elapsed.toNat)))
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13407)
      ([UInt256.ofNat 96, elapsed, solcAddrMask, p.id, UInt256.ofNat 32, UInt256.ofNat 3,
        UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, ret, rate] ++ R) mem aw rdata σ k C) :
    AccrueTailRefines v ee g s0 p imms locals evm (accrueIrmBody.drop 3) ret R (spare - 192) := by
  exact (morphoAccrueMathRefineWithMemory p locals imms hstack hs hm hb hl hr he hvalid h).forget

end Refine
end Benchmarks.Morpho.MorphoBlue
