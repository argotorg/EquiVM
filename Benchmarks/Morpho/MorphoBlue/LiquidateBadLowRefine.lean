import Benchmarks.Morpho.MorphoBlue.LiquidateBadLowReach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def liquidateBadLowIndex (borrow : Bool) : Nat := if borrow then 6 else 8
def liquidateBadLowName (borrow : Bool) : Ident := if borrow then "__c18" else "__c19"
def liquidateBadNextName (borrow : Bool) : Ident := if borrow then "__c19" else "__c20"
def liquidateBadNextValue (borrow : Bool) (badAssets badShares : UInt256) : UInt256 := if borrow then badAssets else badShares
def liquidateBadNextEntry (borrow : Bool) : UInt256 := if borrow then UInt256.ofNat 3077 else UInt256.ofNat 3140
def liquidateBadNextStack (borrow : Bool) (id assets seized shares badAssets badShares srcOff len : UInt256)
    (R : List UInt256) : List UInt256 :=
  (if borrow then [badAssets] else [badShares, UInt256.ofNat 3169]) ++
    liquidateBadTail id assets seized shares badAssets badShares srcOff len R

theorem liquidateBadLowAssign (borrow : Bool) (p : MarketParamsWords) (locals imms : Store)
    (evm : EVM.State) (badAssets : UInt256) (hl : MarketLocals p locals)
    (he : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var (liquidateBadLowName borrow)) = .ok (.int (Int.ofNat badAssets.toNat)))
    (hf : badAssets.toNat ≤ (marketFieldWord evm.accountMap evm.executionEnv p.id (liquidateBadLowField borrow)).toNat) :
    StateBlock config { contract := contract, locals := locals, immutables := imms } evm
      (liquidateBadBody.drop (liquidateBadLowIndex borrow)) { contract := contract, locals := locals, immutables := imms }
      (storeMarketField evm p.id (liquidateBadLowField borrow)
        (UInt256.sub (marketFieldWord evm.accountMap evm.executionEnv p.id (liquidateBadLowField borrow)) badAssets))
      (liquidateBadBody.drop (liquidateBadLowIndex borrow + 1)) := by
  have hass := morphoMarketSubtractAssign p locals imms evm (liquidateBadLowField borrow) (liquidateBadLowName borrow)
    badAssets hl he hf
  cases borrow <;> exact StateBlock.start.step hass

theorem liquidateBadLowAssignReverts (borrow : Bool) (p : MarketParamsWords) (locals imms : Store)
    (evm : EVM.State) (badAssets : UInt256) (hl : MarketLocals p locals)
    (he : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var (liquidateBadLowName borrow)) = .ok (.int (Int.ofNat badAssets.toNat)))
    (hf : (marketFieldWord evm.accountMap evm.executionEnv p.id (liquidateBadLowField borrow)).toNat < badAssets.toNat) :
    ExecBlock config { contract := contract, locals := locals, immutables := imms } evm
      (liquidateBadBody.drop (liquidateBadLowIndex borrow)) .reverted := by
  have hass := morphoMarketSubtractAssignReverts p locals imms evm (liquidateBadLowField borrow)
    (liquidateBadLowName borrow) badAssets hl he hf
  cases borrow <;> exact ExecBlock.consRevert hass

theorem liquidateBadNextCast (borrow : Bool) (locals imms : Store) (evm : EVM.State)
    (badAssets badShares : UInt256)
    (ha : locals.get? "badDebtAssets" = some (.int (Int.ofNat badAssets.toNat)))
    (hs : locals.get? "badDebtShares" = some (.int (Int.ofNat badShares.toNat)))
    (hba : badAssets.toNat < 2 ^ 128) (hbs : badShares.toNat < 2 ^ 128) :
    StateBlock config { contract := contract, locals := locals, immutables := imms } evm
      (liquidateBadBody.drop (liquidateBadLowIndex borrow + 1))
      { contract := contract, locals := locals.insert (liquidateBadNextName borrow)
          (.int (Int.ofNat (liquidateBadNextValue borrow badAssets badShares).toNat)), immutables := imms } evm
      (liquidateBadBody.drop (liquidateBadLowIndex borrow + 2)) := by
  cases borrow
  · exact StateBlock.start.step (morphoToUint128CallOk badShares evm locals imms (.var "badDebtShares") "__c20"
      (by simp only [evalExpr?, hs, EvalResult.ofOption]) hbs)
  · exact StateBlock.start.step (morphoToUint128CallOk badAssets evm locals imms (.var "badDebtAssets") "__c19"
      (by simp only [evalExpr?, ha, EvalResult.ofOption]) hba)

theorem morphoLiquidateBadNextCastReach {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw fp id assets seized shares badAssets badShares srcOff len : UInt256} {σ : AccountMap}
    {k C spare : Nat} {R : List UInt256} (borrow : Bool) (hstack : R.length + 40 ≤ 1024)
    (hm : MorphoHeap mem fp spare) (hspare : 64 ≤ spare)
    (hba : badAssets.toNat < 2 ^ 128) (hbs : badShares.toNat < 2 ^ 128)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15480)
      (liquidateBadNextCastStack borrow id assets seized shares badAssets badShares srcOff len R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (liquidateBadNextEntry borrow)
      (liquidateBadNextStack borrow id assets seized shares badAssets badShares srcOff len R)
      (uint128ErrorMem mem) aw' out σ k' C' := by
  cases borrow
  · simpa only [liquidateBadNextCastStack, liquidateBadNextEntry, liquidateBadNextStack,
      Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append] using
      (morphoToUint128Ok (v := v) (x := badShares) (ret := UInt256.ofNat 3140)
        (R := UInt256.ofNat 3169 :: liquidateBadTail id assets seized shares badAssets badShares srcOff len R)
        (by change R.length + 12 + 16 ≤ 1024; omega)
        (by rw [morphoPatchedValidJumps v]; jump_dest) (hm.alloc64Guard hspare) hbs h)
  · simpa only [liquidateBadNextCastStack, liquidateBadNextEntry, liquidateBadNextStack,
      ↓reduceIte, List.cons_append, List.nil_append] using
      (morphoToUint128Ok (v := v) (x := badAssets) (ret := UInt256.ofNat 3077)
        (R := liquidateBadTail id assets seized shares badAssets badShares srcOff len R)
        (by change R.length + 11 + 16 ≤ 1024; omega)
        (by rw [morphoPatchedValidJumps v]; jump_dest) (hm.alloc64Guard hspare) hba h)

theorem liquidateBadLowStore_valid (v : MorphoImmutables) (borrow : Bool) :
    (D_J (deployedRuntime v) 0).contains (liquidateBadLowStore borrow) = true := by
  cases borrow <;> rw [morphoPatchedValidJumps v] <;> jump_dest

inductive LiquidateBadLowRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (borrow : Bool) (p : MarketParamsWords) (assets seized shares account badAssets badShares srcOff len : UInt256)
    (data : ByteArray) (locals imms : Store) (evm : EVM.State) (mem : ByteArray) (fp : UInt256) (spare : Nat) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (liquidateBadBody.drop (liquidateBadLowIndex borrow)) .reverted → RDrev (deployedRuntime v) g s0 →
      LiquidateBadLowRefines v ee g s0 borrow p assets seized shares account badAssets badShares srcOff len data locals imms evm mem fp spare R
  | ok {locals' evm' σ' mem' fp' aw' out' k' C'} :
      StateBlock config { contract := contract, locals := locals, immutables := imms }
        evm (liquidateBadBody.drop (liquidateBadLowIndex borrow))
        { contract := contract, locals := locals', immutables := imms }
        evm' (liquidateBadBody.drop (liquidateBadLowIndex borrow + 2)) →
      LiquidateEventLocals p account seized shares data assets badAssets badShares locals' →
      locals'.get? "__memory" = locals.get? "__memory" →
      locals'.get? (liquidateBadNextName borrow) = some (.int (Int.ofNat (liquidateBadNextValue borrow badAssets badShares).toNat)) →
      SourceState s0 ee σ' evm' → MorphoHeap mem' fp' (spare - 64) → HeapAdvance mem fp mem' fp' 64 →
      RD (deployedRuntime v) ee g s0 (liquidateBadNextEntry borrow)
        (liquidateBadNextStack borrow p.id assets seized shares badAssets badShares srcOff len R) mem' aw' out' σ' k' C' →
      LiquidateBadLowRefines v ee g s0 borrow p assets seized shares account badAssets badShares srcOff len data locals imms evm mem fp spare R

theorem morphoLiquidateBadLowRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw fp assets seized shares account badAssets badShares srcOff len : UInt256} {out mem data : ByteArray}
    {σ : AccountMap} {k C spare : Nat} {R : List UInt256} (borrow : Bool) (p : MarketParamsWords) (locals imms : Store)
    (hstack : R.length + 48 ≤ 1024) (hperm : ee.perm = true)
    (hl : LiquidateEventLocals p account seized shares data assets badAssets badShares locals) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem fp spare) (hspare : 64 ≤ spare)
    (hget : locals.get? (liquidateBadLowName borrow) = some (.int (Int.ofNat badAssets.toNat)))
    (hba : badAssets.toNat < 2 ^ 128) (hbs : badShares.toNat < 2 ^ 128)
    (h : RD (deployedRuntime v) ee g s0 (liquidateBadLowEntry borrow)
      (badAssets :: liquidateBadTail p.id assets seized shares badAssets badShares srcOff len R) mem aw out σ k C) :
    LiquidateBadLowRefines v ee g s0 borrow p assets seized shares account badAssets badShares srcOff len data locals imms evm mem fp spare R := by
  have hecast : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var (liquidateBadLowName borrow)) = .ok (.int (Int.ofNat badAssets.toNat)) := by
    simp only [evalExpr?, hget, EvalResult.ofOption]
  obtain ⟨a1, k1, C1, rd1⟩ := morphoLiquidateBadLowReachSub (v := v) borrow (by omega) h
  have hb : (marketFieldWord σ ee p.id (liquidateBadLowField borrow)).toNat < 2 ^ 128 := halfWord_bound _ _
  by_cases hf : badAssets.toNat ≤ (marketFieldWord σ ee p.id (liquidateBadLowField borrow)).toNat
  swap
  · exact .reverted (liquidateBadLowAssignReverts borrow p locals imms evm badAssets hl.toMarketLocals hecast
      (by simpa only [hs.env, ← hs.accounts] using Nat.lt_of_not_ge hf))
      (morphoCheckedSub128Reverts (v := v) (ret := liquidateBadLowStore borrow)
        (R := liquidateBadLowStoreTail borrow σ ee p.id assets seized shares badAssets badShares srcOff len R) (by change R.length + 15 + 6 ≤ 1024; omega) hb hba (Nat.lt_of_not_ge hf) rd1)
  let value := UInt256.sub (marketFieldWord evm.accountMap evm.executionEnv p.id (liquidateBadLowField borrow)) badAssets
  let e1 := storeMarketField evm p.id (liquidateBadLowField borrow) value
  let σ1 := storeMarketFieldAccounts σ ee p.id (liquidateBadLowField borrow)
    (UInt256.sub (marketFieldWord σ ee p.id (liquidateBadLowField borrow)) badAssets)
  have hs1 : SourceState s0 ee σ1 e1 := by
    simpa only [e1, σ1, value, hs.env, ← hs.accounts] using storeMarketField_bridge hs p.id (liquidateBadLowField borrow)
      (UInt256.sub (marketFieldWord σ ee p.id (liquidateBadLowField borrow)) badAssets)
  have ab1 := liquidateBadLowAssign borrow p locals imms evm badAssets hl.toMarketLocals hecast
    (by simpa only [hs.env, ← hs.accounts] using hf)
  obtain ⟨k2, C2, rd2⟩ := morphoCheckedSub128Ok (v := v) (ret := liquidateBadLowStore borrow)
    (R := liquidateBadLowStoreTail borrow σ ee p.id assets seized shares badAssets badShares srcOff len R) (by change R.length + 15 + 6 ≤ 1024; omega)
    (liquidateBadLowStore_valid v borrow) hb hba hf rd1
  obtain ⟨a3, k3, C3, rd3⟩ := morphoLiquidateBadLowStore (v := v) borrow (by omega) hperm (by rw [usub_toNat hf]; omega) rd2
  have ab2 : StateBlock config { contract := contract, locals := locals, immutables := imms } evm
      (liquidateBadBody.drop (liquidateBadLowIndex borrow))
      { contract := contract, locals := locals.insert (liquidateBadNextName borrow)
          (.int (Int.ofNat (liquidateBadNextValue borrow badAssets badShares).toNat)), immutables := imms }
      e1 (liquidateBadBody.drop (liquidateBadLowIndex borrow + 2)) :=
    ⟨fun tail ↦ ab1.run ((liquidateBadNextCast borrow locals imms e1 badAssets badShares hl.badAssets_eq hl.badShares_eq hba hbs).run tail)⟩
  have hm1 := hm.hash p.id (UInt256.ofNat 3)
  obtain ⟨a4, k4, C4, rd4⟩ := morphoLiquidateBadNextCastReach (v := v) borrow (by omega) hm1 hspare hba hbs rd3
  exact .ok (evm' := e1) (σ' := σ1) ab2 (hl.insert _ _ (by cases borrow <;> decide) (by cases borrow <;> decide) (by cases borrow <;> decide))
    (store_get_ne _ _ (by cases borrow <;> decide)) (store_get_self _ _ _) hs1 (hm1.narrow hspare)
    (by simpa only [Nat.zero_add] using (heapAdvance_hash mem fp p.id (UInt256.ofNat 3)).trans hm1.narrowAdvance) rd4

end Benchmarks.Morpho.MorphoBlue
