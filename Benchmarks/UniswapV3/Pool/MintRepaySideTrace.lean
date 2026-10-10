import Benchmarks.UniswapV3.Pool.MintRepayMathTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem mintRepaySideX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat}
    {aw p before0 before1 amount0 amount1 junk0 junk1 junk2 junk3 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (second : Bool) (a : MintArgs) (locals : Store)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 (mintRepayEntryPC second)
      (mintRepayEntryWords second junk0 junk1 junk2 junk3 before0 before1 amount0 amount1 R)
      mem aw rdata σ k C) (hv : MintCallValues locals a amount0 amount1 before0 before1)
    (hm : HeapMemory mem aw p) (hsize : 128 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hb : p.toNat + 2 ^ 138 + 163 ≤ 2 ^ 200) (hov : R.length + 24 ≤ 1024) :
    (ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
        (mintRepayStmt second) .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    (∃ evm' σ' out mem' aw' free locals' k' C', SourceState s0 ee σ' evm' ∧
      ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
        (mintRepayStmt second)
        (.ok {contract := contract, locals := locals', immutables := immStore v} evm') ∧
      MintCallValues locals' a amount0 amount1 before0 before1 ∧
      RD (deployedRuntime v) ee g s0 (mintRepayNextPC second)
        (mintRepayWords before0 before1 amount0 amount1 R) mem' aw' out σ' k' C' ∧
      HeapMemory mem' aw' free ∧ 128 ≤ mem'.size ∧
      memLoad (UInt256.ofNat 96) mem' = ⟨0⟩ ∧ free.toNat ≤ p.toNat + 2 ^ 138 + 131) := by
  have hAmount : locals.get? (poolAmountName second) =
      some (.int (Int.ofNat (if second then amount1 else amount0).toNat)) := by
    cases second
    · exact hv.core.amount0
    · exact hv.core.amount1
  rcases mintRepayEntryX (v := v) second rd (by omega) with
    ⟨hz, k0, C0, r0⟩ | ⟨hp, k0, C0, r0⟩
  · exact Or.inr ⟨evm, σ, rdata, mem, aw, p, locals, k0, C0, hs,
      mintRepaySkip v locals evm second (by simpa only [hz] using hAmount),
      hv, r0, hm, hsize, hzero, by omega⟩
  have hguard : evalExpr? config {contract := contract, locals := locals, immutables := immStore v}
      evm (.binary .gt (.var (poolAmountName second)) (.intLit 0)) = .ok (.bool true) := by
    simpa only [hp, decide_true] using evalFlashTransferGuard v locals evm second _ hAmount
  rcases balanceX (v := v) second r0 hs hm hsize hzero hb
      (by rw [uniswapV3PoolPatchedValidJumps v]; cases second <;> native_decide)
      (by change R.length + 6 + 18 ≤ 1024; omega) with ⟨rr, hbad⟩ |
      ⟨evm1, σ1, out1, mem1, aw1, p1, k1, C1, hs1, hc, r1, hm1, hmem1, hp1⟩
  · exact Or.inl ⟨ExecStmt.iteTrue hguard (ExecBlock.consRevert
      (poolBalanceReverts v locals (mintAfterBalanceTemp second) evm second hbad)), rr⟩
  let locals1 := locals.insert (mintAfterBalanceTemp second) (.int (Int.ofNat (balanceValue out1).toNat))
  have hv1 : MintCallValues locals1 a amount0 amount1 before0 before1 :=
    hv.insert (mintAfterBalanceTemp second) _ (by cases second <;> decide)
  have hb1 : locals1.get? (mintBeforeBalanceName second) =
      some (.int (Int.ofNat (if second then before1 else before0).toNat)) := by
    cases second
    · exact hv1.before0
    · exact hv1.before1
  have ha1 : locals1.get? (poolAmountName second) =
      some (.int (Int.ofNat (if second then amount1 else amount0).toNat)) := by
    cases second
    · exact hv1.core.amount0
    · exact hv1.core.amount1
  have hr1 : locals1.get? (mintAfterBalanceTemp second) =
      some (.int (Int.ofNat (balanceValue out1).toNat)) := by simp [locals1]
  have hcall := poolBalanceReturns v locals (mintAfterBalanceTemp second) evm evm1 second
    (balanceValue out1) (balanceCallFrame v second true out1) hc
  rcases mintRepayMathX (v := v) second r1 (by omega) with ⟨hbad, rr⟩ | ⟨hgood, k2, C2, r2⟩
  · exact Or.inl ⟨ExecStmt.iteTrue hguard (ExecBlock.consNormal hcall
      (mintRepayReverts v locals1 evm1 second _ _ _ hb1 ha1 hr1 hbad)), rr⟩
  let finalFrame := mintRepayFrame v locals1 second
    (if second then before1 else before0) (if second then amount1 else amount0)
  have hv2 : MintCallValues finalFrame.locals a amount0 amount1 before0 before1 :=
    hv1.insert (mintRepayName second) _ (by cases second <;> decide)
  refine Or.inr ⟨evm1, σ1, out1, mem1, aw1, p1, finalFrame.locals, k2, C2, hs1,
    ExecStmt.iteTrue hguard (ExecBlock.consNormal hcall
      (mintRepayReturns v locals1 evm1 second _ _ _ hb1 ha1 hr1 hgood)), hv2, r2, hm1,
    le_trans hsize hmem1.size, ?_, hp1⟩
  rw [MemoryPrefix.memLoad hmem1 (UInt256.ofNat 96) (by decide) hm.lower hsize, hzero]

end Benchmarks.UniswapV3.Pool
