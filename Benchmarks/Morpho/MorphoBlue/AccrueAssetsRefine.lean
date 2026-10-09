import Benchmarks.Morpho.MorphoBlue.AccrueTailRefines
import Benchmarks.Morpho.MorphoBlue.AccrueSupplyAssets

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- The arithmetic check is shared by both packed asset writes.
theorem accrueAssetSumClean {σ I id i interest}
    (h : (marketFieldWord σ I id i).toNat + interest.toNat < 2 ^ 128) :
    (marketFieldWord σ I id i + interest).toNat < 2 ^ 128 := by
  rw [uadd_toNat, Nat.mod_eq_of_lt (show (marketFieldWord σ I id i).toNat + interest.toNat < UInt256.size by
    change _ < 2 ^ 256; omega)]
  exact h

section Refine
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 evm : State}
  {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
  {rate interest ret fp : UInt256} {R : List UInt256} {spare : Nat}

theorem morphoAccrueAssetsRefineWithMemory (p : MarketParamsWords) (locals imms : Store)
    (hstack : R.length + 40 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem fp spare) (hb : 192 ≤ spare) (hl : MarketLocals p locals)
    (hr : locals.get? "borrowRate" = some (.int (Int.ofNat rate.toNat)))
    (hi : locals.get? "interest" = some (.int (Int.ofNat interest.toNat)))
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15480)
      ([interest, UInt256.ofNat 13574, UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, p.id,
        UInt256.ofNat 32, solcAddrMask, interest, UInt256.ofNat 3, wad] ++ accrueMathTail p.id rate ret R)
      mem aw rdata σ k C) :
    AccrueTailRefinesWithMemory v ee g s0 p imms locals evm (accrueIrmBody.drop 5) ret R (spare - 192) mem fp 128 := by
  have hei : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm (.var "interest") =
      .ok (.int (Int.ofNat interest.toNat)) := by simp only [evalExpr?, hi, EvalResult.ofOption]
  by_cases hc : interest.toNat < 2 ^ 128
  · have hn := morphoToUint128CallOk interest evm locals imms (.var "interest") "__c3" hei hc
    let l1 := locals.insert "__c3" (.int (Int.ofNat interest.toNat))
    have hl1 : MarketLocals p l1 := hl.insert "__c3" _ (by decide)
    have he1 : evalExpr? config { contract := contract, locals := l1, immutables := imms } evm (.var "__c3") =
        .ok (.int (Int.ofNat interest.toNat)) := by simp only [evalExpr?, l1, store_get_self, EvalResult.ofOption]
    have ab1 : StateBlock config { contract := contract, locals := locals, immutables := imms } evm
        (accrueIrmBody.drop 5) { contract := contract, locals := l1, immutables := imms } evm (accrueIrmBody.drop 6) :=
      StateBlock.start.step hn
    obtain ⟨aw1, k1, C1, rd1⟩ := morphoToUint128Ok (v := v)
      (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega)
      (by rw [morphoPatchedValidJumps v]; jump_dest) (hm.alloc64Guard (by omega)) hc h
    have hm1 := hm.narrow (by omega : 64 ≤ spare)
    by_cases hborr : (marketFieldWord σ ee p.id 2).toNat + interest.toNat < 2 ^ 128
    · have hborr' : (marketFieldWord evm.accountMap evm.executionEnv p.id 2).toNat + interest.toNat < 2 ^ 128 := by
        simpa only [hs.env, ← hs.accounts] using hborr
      have hass := morphoAccrueAssetsAssign p l1 imms evm ⟨2, by decide⟩ "__c3" interest hl1 he1 hborr'
      obtain ⟨aw2, k2, C2, rd2⟩ := morphoAccrueBorrowAddOk (v := v)
        (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega) hc hborr rd1
      have hm2 := hm1.hash p.id (UInt256.ofNat 3)
      by_cases hp : ee.perm = true
      · obtain ⟨k3, C3, rd3⟩ := morphoAccrueBorrowStore (v := v)
          (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega) hp (accrueAssetSumClean hborr) rd2
        let e1 := storeMarketField evm p.id ⟨2, by decide⟩ (marketFieldWord evm.accountMap evm.executionEnv p.id 2 + interest)
        have hs1 : SourceState s0 ee (accrueBorrowAssetsAccounts σ ee p.id interest) e1 := by
          simpa only [e1, hs.env, ← hs.accounts] using
            storeMarketField_bridge hs p.id ⟨2, by decide⟩ (marketFieldWord σ ee p.id 2 + interest)
        have ab2 : StateBlock config { contract := contract, locals := locals, immutables := imms } evm
            (accrueIrmBody.drop 5) { contract := contract, locals := l1, immutables := imms } e1 (accrueIrmBody.drop 7) :=
          ab1.step hass
        have hei1 : evalExpr? config { contract := contract, locals := l1, immutables := imms } e1 (.var "interest") =
            .ok (.int (Int.ofNat interest.toNat)) := by
          simp only [evalExpr?, l1, store_get_ne (k := "__c3") (a := "interest") _ _ (by decide), hi, EvalResult.ofOption]
        have hn2 := morphoToUint128CallOk interest e1 l1 imms (.var "interest") "__c4" hei1 hc
        let l2 := l1.insert "__c4" (.int (Int.ofNat interest.toNat))
        have hl2 : MarketLocals p l2 := hl1.insert "__c4" _ (by decide)
        have he2 : evalExpr? config { contract := contract, locals := l2, immutables := imms } e1 (.var "__c4") =
            .ok (.int (Int.ofNat interest.toNat)) := by simp only [evalExpr?, l2, store_get_self, EvalResult.ofOption]
        have ab3 : StateBlock config { contract := contract, locals := locals, immutables := imms } evm
            (accrueIrmBody.drop 5) { contract := contract, locals := l2, immutables := imms } e1 (accrueIrmBody.drop 8) :=
          ab2.step hn2
        obtain ⟨aw4, k4, C4, rd4⟩ := morphoToUint128Ok (v := v)
          (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega)
          (by rw [morphoPatchedValidJumps v]; jump_dest) (hm2.alloc64Guard (by omega)) hc rd3
        have hm4 := hm2.narrow (by omega : 64 ≤ spare - 64)
        by_cases hsupp : (marketFieldWord (accrueBorrowAssetsAccounts σ ee p.id interest) ee p.id 0).toNat + interest.toNat < 2 ^ 128
        · have hsupp' : (marketFieldWord e1.accountMap e1.executionEnv p.id 0).toNat + interest.toNat < 2 ^ 128 := by
            simpa only [hs1.env, ← hs1.accounts] using hsupp
          have hass2 := morphoAccrueAssetsAssign p l2 imms e1 ⟨0, by decide⟩ "__c4" interest hl2 he2 hsupp'
          obtain ⟨aw5, k5, C5, rd5⟩ := morphoAccrueSupplyAddOk (v := v)
            (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega) hc hsupp rd4
          obtain ⟨aw6, k6, C6, rd6⟩ := morphoAccrueSupplyStore (v := v)
            (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega) hp (accrueAssetSumClean hsupp) rd5
          let e2 := storeMarketField e1 p.id ⟨0, by decide⟩ (marketFieldWord e1.accountMap e1.executionEnv p.id 0 + interest)
          have hs2 : SourceState s0 ee (accrueSupplyAssetsAccounts (accrueBorrowAssetsAccounts σ ee p.id interest) ee p.id interest) e2 := by
            simpa only [e2, hs1.env, ← hs1.accounts] using storeMarketField_bridge hs1 p.id ⟨0, by decide⟩
              (marketFieldWord (accrueBorrowAssetsAccounts σ ee p.id interest) ee p.id 0 + interest)
          have ab4 : StateBlock config { contract := contract, locals := locals, immutables := imms } evm
              (accrueIrmBody.drop 5) { contract := contract, locals := l2, immutables := imms } e2 (accrueIrmBody.drop 9) :=
            ab3.step hass2
          let l3 := l2.insert "feeShares" (.int 0)
          have hz : ExecStmt config { contract := contract, locals := l2, immutables := imms } e2 accrueIrmBody[9]!
              (.ok { contract := contract, locals := l3, immutables := imms } e2) := ExecStmt.letDecl (by simp only [evalExpr?, pure])
          have ab5 : StateBlock config { contract := contract, locals := locals, immutables := imms } evm
              (accrueIrmBody.drop 5) { contract := contract, locals := l3, immutables := imms } e2 (accrueIrmBody.drop 10) :=
            ab4.step hz
          have hl3 : AccrueLocals p l3 rate interest ⟨0⟩ := by
            refine ⟨hl2.insert "feeShares" _ (by decide), ?_, ?_, ?_⟩
            · simp only [l3, l2, l1, store_get_ne (k := "feeShares") (a := "borrowRate") _ _ (by decide),
                store_get_ne (k := "__c4") (a := "borrowRate") _ _ (by decide),
                store_get_ne (k := "__c3") (a := "borrowRate") _ _ (by decide), hr]
            · simp only [l3, l2, l1, store_get_ne (k := "feeShares") (a := "interest") _ _ (by decide),
                store_get_ne (k := "__c4") (a := "interest") _ _ (by decide),
                store_get_ne (k := "__c3") (a := "interest") _ _ (by decide), hi]
            · exact store_get_self _ _ _
          have hf := morphoAccrueFinishTailWithMemory (v := v) p l3 imms hstack hp hs2
            ((hm4.hash p.id (UInt256.ofNat 3)).hash p.id (UInt256.ofNat 3)) (by omega) hl3 hvalid rd6
          have heq : spare - 64 - 64 - 64 = spare - 192 := by omega
          rw [heq] at hf
          have had := ((hm.narrowAdvance.trans (heapAdvance_hash _ _ p.id (UInt256.ofNat 3))).trans
            hm2.narrowAdvance).trans ((heapAdvance_hash _ _ p.id (UInt256.ofNat 3)).trans
              (heapAdvance_hash _ _ p.id (UInt256.ofNat 3)))
          simpa only [Nat.add_zero, Nat.reduceAdd] using (hf.memoryPrepend had).prepend ab5
        · apply AccrueTailRefinesWithMemory.reverted
          · apply ab3.reverts
            apply morphoAccrueAssetsAssignReverts p l2 imms e1 ⟨0, by decide⟩ "__c4" interest hl2 he2
            simpa only [hs1.env, ← hs1.accounts] using Nat.le_of_not_gt hsupp
          · exact morphoAccrueSupplyAddReverts (v := v)
              (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega) hc (Nat.le_of_not_gt hsupp) rd4
      · have hp' : ee.perm = false := Bool.eq_false_iff.mpr hp
        exact .static (ab1.static (execStmt_assign_static hass (by rw [hs.env]; exact hp')))
          (morphoAccrueBorrowStoreStatic (v := v)
            (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega) hp' rd2)
    · apply AccrueTailRefinesWithMemory.reverted
      · apply ab1.reverts
        apply morphoAccrueAssetsAssignReverts p l1 imms evm ⟨2, by decide⟩ "__c3" interest hl1 he1
        simpa only [hs.env, ← hs.accounts] using Nat.le_of_not_gt hborr
      · exact morphoAccrueBorrowAddReverts (v := v)
          (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega) hc (Nat.le_of_not_gt hborr) rd1
  · exact .reverted (ExecBlock.consRevert (morphoToUint128CallReverts interest evm locals imms
      (.var "interest") "__c3" hei (Nat.le_of_not_gt hc)))
      (morphoToUint128Reverts (v := v)
        (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega)
        (hm.alloc64Guard (by omega)) hm.size (by rw [hm.free]; exact hm.lower)
        hm.errorGap hm.errorHi (Nat.le_of_not_gt hc) h)

theorem morphoAccrueAssetsRefine (p : MarketParamsWords) (locals imms : Store)
    (hstack : R.length + 40 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem fp spare) (hb : 192 ≤ spare) (hl : MarketLocals p locals)
    (hr : locals.get? "borrowRate" = some (.int (Int.ofNat rate.toNat)))
    (hi : locals.get? "interest" = some (.int (Int.ofNat interest.toNat)))
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15480)
      ([interest, UInt256.ofNat 13574, UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, p.id,
        UInt256.ofNat 32, solcAddrMask, interest, UInt256.ofNat 3, wad] ++ accrueMathTail p.id rate ret R)
      mem aw rdata σ k C) :
    AccrueTailRefines v ee g s0 p imms locals evm (accrueIrmBody.drop 5) ret R (spare - 192) := by
  exact (morphoAccrueAssetsRefineWithMemory p locals imms hstack hs hm hb hl hr hi hvalid h).forget

end Refine
end Benchmarks.Morpho.MorphoBlue
