import Benchmarks.Morpho.MorphoBlue.LiquidateBadDebtReach
import Benchmarks.Morpho.MorphoBlue.LiquidateEventLocals
import Benchmarks.Morpho.MorphoBlue.SafeTransferSourceAllocation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: minimum is bounded by its first argument.
theorem minWord_le_left (x y : UInt256) : (minWord x y).toNat ≤ x.toNat := by
  unfold minWord
  split <;> omega

inductive LiquidateBadMathRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (assets seized shares account srcOff len : UInt256) (data : ByteArray)
    (locals imms : Store) (evm : EVM.State) (σ : AccountMap) (mem : ByteArray) (fp : UInt256) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm liquidateBadBody .reverted → RDrev (deployedRuntime v) g s0 →
      LiquidateBadMathRefines v ee g s0 p assets seized shares account srcOff len data locals imms evm σ mem fp R
  | ok {badAssets badShares locals' mem' fp' aw' out' k' C'} :
      ABlock config evm { contract := contract, locals := locals, immutables := imms }
        liquidateBadBody { contract := contract, locals := locals', immutables := imms }
        (liquidateBadBody.drop 6) → LiquidateEventLocals p account seized shares data assets badAssets badShares locals' →
      locals'.get? "__memory" = some (.int (Int.ofNat (fp'.toNat + 128))) →
      locals'.get? "__c18" = some (.int (Int.ofNat badAssets.toNat)) →
      badAssets.toNat < 2 ^ 128 → badShares.toNat < 2 ^ 128 →
      MorphoHeap mem' fp' 512 → HeapAdvance mem fp mem' fp' 64 →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 3014)
        (badAssets :: liquidateBadTail p.id assets seized shares badAssets badShares srcOff len R)
        mem' aw' out' σ k' C' →
      LiquidateBadMathRefines v ee g s0 p assets seized shares account srcOff len data locals imms evm σ mem fp R

theorem morphoLiquidateBadMathRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw fp assets seized shares account srcOff len : UInt256} {out mem data : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (p : MarketParamsWords) (locals imms : Store)
    (hstack : R.length + 48 ≤ 1024) (ha : account.toNat < EVM.addressModulus)
    (haccount : calldataWord ee.calldata 164 = account)
    (hl : LiquidateEventLocals p account seized shares data assets (UInt256.ofNat 0) (UInt256.ofNat 0) locals)
    (hs : SourceState s0 ee σ evm) (hm : MorphoHeap mem fp 576)
    (hget : locals.get? "__memory" = some (.int (Int.ofNat fp.toNat)))
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2873)
      (liquidateBadTail p.id assets seized shares (UInt256.ofNat 0) (UInt256.ofNat 0) srcOff len R) mem aw out σ k C) :
    LiquidateBadMathRefines v ee g s0 p assets seized shares account srcOff len data locals imms evm σ mem fp R := by
  let l1 := locals.insert "__memory" (.int (Int.ofNat (fp.toNat + 192)))
  have hl1 : LiquidateEventLocals p account seized shares data assets (UInt256.ofNat 0) (UInt256.ofNat 0) l1 :=
    hl.insert _ _ (by decide) (by decide) (by decide)
  have he1 : ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      liquidateBadBody[0]! (.ok { contract := contract, locals := l1, immutables := imms } evm) :=
    ExecStmt.assign (safeTransferMemoryAdd_eval hget 192) (assignLocalWord hget)
  let bds := positionFieldWord σ ee p.id account 1
  have hebds : evalExpr? config { contract := contract, locals := l1, immutables := imms } evm
      (.storage ⟨"position", [.mindex (.var "id"), .mindex (.var "borrower"), .field "borrowShares"]⟩) =
      .ok (.int (Int.ofNat bds.toNat)) := by
    simpa only [hs.env, ← hs.accounts] using hl1.evalPosition imms evm ⟨1, by decide⟩ ha
  let l2 := l1.insert "badDebtShares" (.int (Int.ofNat bds.toNat))
  have hl2 : LiquidateEventLocals p account seized shares data assets (UInt256.ofNat 0) bds l2 := hl1.setBadShares bds
  have he2 : ExecStmt config { contract := contract, locals := l1, immutables := imms } evm
      liquidateBadBody[1]! (.ok { contract := contract, locals := l2, immutables := imms } evm) :=
    ExecStmt.assign hebds (assignLocalWord hl1.badShares_eq)
  have ab2 : ABlock config evm { contract := contract, locals := locals, immutables := imms } liquidateBadBody
      { contract := contract, locals := l2, immutables := imms } (liquidateBadBody.drop 2) :=
    advancePureBlock (advancePureBlock ABlock.start he1) he2
  obtain ⟨a1, k1, C1, rd1⟩ := morphoLiquidateBadDebtReachAssets (v := v) (by omega) ha haccount h
  have heassets := hl2.evalField imms evm ⟨2, by decide⟩
  have heshares := hl2.evalField imms evm ⟨3, by decide⟩
  rw [hs.env, ← hs.accounts] at heassets heshares
  by_cases hf : AssetsUpFits bds (marketFieldWord σ ee p.id 2) (marketFieldWord σ ee p.id 3)
  swap
  · exact .reverted (ab2.run (ExecBlock.consRevert (morphoAssetsUpCallReverts _ _ _ evm l2 imms _ _ _ "__c16"
      (hl2.evalBadShares imms evm) heassets heshares hf)))
      (morphoAssetsUpReverts (v := v) (by change R.length + 11 + 14 ≤ 1024; omega) hf rd1)
  obtain ⟨k2, C2, rd2⟩ := morphoAssetsUpOk (v := v) (by change R.length + 11 + 14 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hf rd1
  let quote := assetsUpWord bds (marketFieldWord σ ee p.id 2) (marketFieldWord σ ee p.id 3)
  let l3 := l2.insert "__c16" (.int (Int.ofNat quote.toNat))
  have hl3 : LiquidateEventLocals p account seized shares data assets (UInt256.ofNat 0) bds l3 :=
    hl2.insert _ _ (by decide) (by decide) (by decide)
  have ab3 : ABlock config evm { contract := contract, locals := locals, immutables := imms } liquidateBadBody
      { contract := contract, locals := l3, immutables := imms } (liquidateBadBody.drop 3) :=
    advancePureBlock ab2 (morphoAssetsUpCallOk _ _ _ evm l2 imms _ _ _ "__c16"
      (hl2.evalBadShares imms evm) heassets heshares hf)
  let bda := minWord (marketFieldWord σ ee p.id 2) quote
  let l4 := l3.insert "__c17" (.int (Int.ofNat bda.toNat))
  have hl4 : LiquidateEventLocals p account seized shares data assets (UInt256.ofNat 0) bds l4 :=
    hl3.insert _ _ (by decide) (by decide) (by decide)
  have heassets3 := hl3.evalField imms evm ⟨2, by decide⟩
  rw [hs.env, ← hs.accounts] at heassets3
  have hequote : evalExpr? config { contract := contract, locals := l3, immutables := imms } evm
      (.var "__c16") = .ok (.int (Int.ofNat quote.toNat)) := by simp only [evalExpr?, l3, store_get_self, EvalResult.ofOption]
  have ab4 : ABlock config evm { contract := contract, locals := locals, immutables := imms } liquidateBadBody
      { contract := contract, locals := l4, immutables := imms } (liquidateBadBody.drop 4) :=
    advancePureBlock ab3 (morphoMinCall _ _ evm l3 imms _ _ "__c17" heassets3 hequote)
  let l5 := l4.insert "badDebtAssets" (.int (Int.ofNat bda.toNat))
  have hl5 : LiquidateEventLocals p account seized shares data assets bda bds l5 := hl4.setBadAssets bda
  have he5 : ExecStmt config { contract := contract, locals := l4, immutables := imms } evm
      liquidateBadBody[4]! (.ok { contract := contract, locals := l5, immutables := imms } evm) :=
    ExecStmt.assign (by simp only [evalExpr?, l4, store_get_self, EvalResult.ofOption]) (assignLocalWord hl4.badAssets_eq)
  have ab5 := advancePureBlock ab4 he5
  have hbda : bda.toNat < 2 ^ 128 :=
    lt_of_le_of_lt (minWord_le_left _ _) (halfWord_bound _ _)
  have hbds : bds.toNat < 2 ^ 128 := by change (halfWord false _).toNat < 2 ^ 128; exact halfWord_bound _ _
  have rd3 := morphoBlocks.morpho_block_2996 (immWords := wordsOf (immStore v))
    (by change R.length + 9 + 5 ≤ 1024; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  dsimp only [morphoBlocks.morpho_block_2996_stack] at rd3
  rw [minWord_evm_alt] at rd3
  have hm1 := ((hm.hash p.id (UInt256.ofNat 2)).hash account (solcMappingSlot ⟨2⟩ p.id)).hash p.id (UInt256.ofNat 3)
  obtain ⟨a4, k4, C4, rd4⟩ := morphoToUint128Ok (v := v) (by change R.length + 11 + 16 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (hm1.alloc64Guard (by decide)) hbda rd3
  have had := (((heapAdvance_hash mem fp p.id (UInt256.ofNat 2)).trans
    (heapAdvance_hash _ fp account (solcMappingSlot ⟨2⟩ p.id))).trans
    (heapAdvance_hash _ fp p.id (UInt256.ofNat 3))).trans hm1.narrowAdvance
  refine .ok (advancePureBlock ab5 (morphoToUint128CallOk bda evm l5 imms (.var "badDebtAssets") "__c18"
    (hl5.evalBadAssets imms evm) hbda)) (hl5.insert _ _ (by decide) (by decide) (by decide))
    ?_ (store_get_self _ _ _) hbda hbds (hm1.narrow (by decide)) ?_ rd4
  · simp only [l5, l4, l3, l2, l1,
      store_get_ne _ _ (show ("__c18" == "__memory") = false by decide),
      store_get_ne _ _ (show ("badDebtAssets" == "__memory") = false by decide),
      store_get_ne _ _ (show ("__c17" == "__memory") = false by decide),
      store_get_ne _ _ (show ("__c16" == "__memory") = false by decide),
      store_get_ne _ _ (show ("badDebtShares" == "__memory") = false by decide), store_get_self,
      hm1.narrowAdvance.cursor]
  · simpa only [Nat.zero_add] using had

end Benchmarks.Morpho.MorphoBlue
