import Benchmarks.Morpho.MorphoBlue.AccrueMemoryAdvance
import Benchmarks.Morpho.MorphoBlue.AccrueFeeRefine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem MorphoHeap.weaken {mem fp spare spare'} (h : MorphoHeap mem fp spare) (hs : spare' ≤ spare) :
    MorphoHeap mem fp spare' := by
  refine ⟨h.size, h.free, h.lower, ?_, ?_⟩
  · have hg := h.gap; omega
  · have hb := h.space; omega

theorem accrueTimestamp_bridge {s0 : State} {I : ExecutionEnv} {σ : AccountMap} {evm : State}
    (hs : SourceState s0 I σ evm) (id : UInt256) :
    SourceState s0 I (storeMarketFieldAccounts σ I id ⟨4, by decide⟩
      (halfWord false (UInt256.ofNat I.header.timestamp)))
      (storeMarketLastUpdate evm id (halfWord false (UInt256.ofNat evm.executionEnv.header.timestamp))) := by
  have h := storeMarketField_bridge hs id ⟨4, by decide⟩ (halfWord false (UInt256.ofNat I.header.timestamp))
  simpa only [hs.env] using h

section Refine
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 evm : State}
  {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
  {rate interest ret fp : UInt256} {R : List UInt256} {spare : Nat}

theorem morphoAccrueFinishRefineWithMemory (p : MarketParamsWords) (locals imms : Store)
    (hstack : R.length + 40 ≤ 1024) (hp : ee.perm = true)
    (hs : SourceState s0 ee σ evm) (hm : MorphoHeap mem fp spare) (hb : 64 ≤ spare)
    (hl : AccrueLocals p locals rate interest ⟨0⟩)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0
      (if marketFieldWord σ ee p.id 5 = ⟨0⟩ then UInt256.ofNat 13706 else UInt256.ofNat 13738)
      ([wad, UInt256.ofNat 3, UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, p.id,
        UInt256.ofNat 32, solcAddrMask, interest, UInt256.ofNat 0, marketFieldWord σ ee p.id 5] ++
        accrueMathTail p.id rate ret R) mem aw rdata σ k C) :
    (ExecBlock config { contract := contract, locals := locals, immutables := imms } evm
      (accrueIrmBody.drop 10) .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    (∃ locals' evm' σ' mem' fp' aw' k' C',
      ExecBlock config { contract := contract, locals := locals, immutables := imms } evm (accrueIrmBody.drop 10)
        (.ok { contract := contract, locals := locals', immutables := imms } evm') ∧
      MarketLocals p locals' ∧ SourceState s0 ee σ'
        (storeMarketLastUpdate evm' p.id (halfWord false (UInt256.ofNat evm'.executionEnv.header.timestamp))) ∧
      MorphoHeap mem' fp' (spare - 64) ∧
      HeapAdvance mem fp mem' fp' (if marketFieldWord σ' ee p.id 5 = ⟨0⟩ then 0 else 64) ∧
      RD (deployedRuntime v) ee g s0 ret R mem' aw' rdata σ' k' C') := by
  have hfeeLast (σx : AccountMap) := marketFee_storeField σx ee p.id ⟨4, by decide⟩
    (halfWord false (UInt256.ofNat ee.header.timestamp)) (by decide) (halfWord_bound _ _)
  have he := morphoAccrueFeeCondition p locals imms evm hl.toMarketLocals
  by_cases hf : marketFieldWord σ ee p.id 5 = ⟨0⟩
  · rw [if_pos hf] at h
    have hz : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
        (.binary .ne (.storage ⟨"market", [.mindex (.var "id"), .field "fee"]⟩) (.intLit 0)) = .ok (.bool false) := by
      simpa only [hs.env, ← hs.accounts, hf, ne_eq, not_true_eq_false, decide_false] using he
    have hem := morphoAccrueEmit p locals imms evm rate interest ⟨0⟩ hl.toMarketLocals
      (hl.evalRate imms evm) (hl.evalInterest imms evm) (hl.evalShares imms evm)
    obtain ⟨aw1, k1, C1, rd1⟩ := morphoAccrueLogReturn (v := v) (by omega) hp hvalid h
    have had := (hm.eventAdvance rate interest ⟨0⟩).trans
      (heapAdvance_hash _ fp p.id (UInt256.ofNat 3))
    refine Or.inr ⟨locals, evm, _, _, fp, aw1, k1, C1,
      ExecBlock.consNormal (ExecStmt.iteFalse hz ExecBlock.nil) (ExecBlock.consNormal hem ExecBlock.nil),
      hl.toMarketLocals, accrueTimestamp_bridge hs p.id,
      ((hm.event rate interest ⟨0⟩).hash p.id (UInt256.ofNat 3)).weaken (Nat.sub_le spare 64), ?_, rd1⟩
    simpa only [hfeeLast σ, hf, ↓reduceIte, Nat.add_zero] using had
  · rw [if_neg hf] at h
    have hn : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
        (.binary .ne (.storage ⟨"market", [.mindex (.var "id"), .field "fee"]⟩) (.intLit 0)) = .ok (.bool true) := by
      simpa only [hs.env, ← hs.accounts, decide_eq_true hf] using he
    rcases morphoAccrueFeeRefineWithFee (v := v) p locals imms hstack hp hs hm hb hl h with hr | hok
    · exact Or.inl ⟨ExecBlock.consRevert (ExecStmt.iteTrue hn hr.1), hr.2⟩
    · obtain ⟨shares, locals', evm', σ', aw1, k1, C1, hsolm, hl', hs', hm', hnfee, rd1⟩ := hok
      have hem := morphoAccrueEmit p locals' imms evm' rate interest shares hl'.toMarketLocals
        (hl'.evalRate imms evm') (hl'.evalInterest imms evm') (hl'.evalShares imms evm')
      obtain ⟨aw2, k2, C2, rd2⟩ := morphoAccrueFeeLogReturn (v := v) (by omega) hp hvalid rd1
      have hnf : marketFieldWord σ' ee p.id 5 ≠ ⟨0⟩ := by
        have hh := hnfee (by simpa only [hs.env, ← hs.accounts] using hf)
        simpa only [hs'.env, ← hs'.accounts] using hh
      have had := (hm.feeMemAdvance σ ee p.id).trans
        ((hm'.eventAdvance rate interest shares).trans
          (heapAdvance_hash _ (fp + UInt256.ofNat 64) p.id (UInt256.ofNat 3)))
      refine Or.inr ⟨locals', evm', _, _, _, aw2, k2, C2,
        ExecBlock.consNormal (ExecStmt.iteTrue hn hsolm) (ExecBlock.consNormal hem ExecBlock.nil),
        hl'.toMarketLocals, accrueTimestamp_bridge hs' p.id,
        (hm'.event rate interest shares).hash p.id (UInt256.ofNat 3), ?_, rd2⟩
      simpa only [hfeeLast σ', if_neg hnf, Nat.add_zero] using had

theorem morphoAccrueFinishRefine (p : MarketParamsWords) (locals imms : Store)
    (hstack : R.length + 40 ≤ 1024) (hp : ee.perm = true)
    (hs : SourceState s0 ee σ evm) (hm : MorphoHeap mem fp spare) (hb : 64 ≤ spare)
    (hl : AccrueLocals p locals rate interest ⟨0⟩)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0
      (if marketFieldWord σ ee p.id 5 = ⟨0⟩ then UInt256.ofNat 13706 else UInt256.ofNat 13738)
      ([wad, UInt256.ofNat 3, UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, p.id,
        UInt256.ofNat 32, solcAddrMask, interest, UInt256.ofNat 0, marketFieldWord σ ee p.id 5] ++
        accrueMathTail p.id rate ret R) mem aw rdata σ k C) :
    (ExecBlock config { contract := contract, locals := locals, immutables := imms } evm
      (accrueIrmBody.drop 10) .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    (∃ locals' evm' σ' mem' fp' aw' k' C',
      ExecBlock config { contract := contract, locals := locals, immutables := imms } evm (accrueIrmBody.drop 10)
        (.ok { contract := contract, locals := locals', immutables := imms } evm') ∧
      MarketLocals p locals' ∧ SourceState s0 ee σ'
        (storeMarketLastUpdate evm' p.id (halfWord false (UInt256.ofNat evm'.executionEnv.header.timestamp))) ∧
      MorphoHeap mem' fp' (spare - 64) ∧
      RD (deployedRuntime v) ee g s0 ret R mem' aw' rdata σ' k' C') := by
  rcases morphoAccrueFinishRefineWithMemory p locals imms hstack hp hs hm hb hl hvalid h with hr | hok
  · exact Or.inl hr
  · obtain ⟨locals', evm', σ', mem', fp', aw', k', C', he, hl', hs', hm', _, rd⟩ := hok
    exact Or.inr ⟨locals', evm', σ', mem', fp', aw', k', C', he, hl', hs', hm', rd⟩

end Refine
end Benchmarks.Morpho.MorphoBlue
