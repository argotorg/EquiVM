import Benchmarks.Midnight.LiquidatorGateHead
import Benchmarks.Midnight.LiquidatorGateCall
import Benchmarks.Midnight.LiquidatorGateSource

/-! The optional liquidator gate, including its source require and all runtime failures. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

set_option maxRecDepth 2000000

theorem midnightLiquidatorGate {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {m : MarketData} {mem rdata : ByteArray}
    {aw root budgetRoot w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : UInt256} {credit : Nat}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 20 ≤ 1024) (hroot : root.toNat + 36 < 2^64)
    (hlower : 832 ≤ root.toNat) (hm : 832 ≤ mem.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hmarket : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hd : decodeCalldataMarket I.calldata 4 = some m)
    (hs : SourceState s0 I σ evm) (hb : TransferBudget budgetRoot credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨5275⟩
      ([w0, w1, w2, w3, w4, w5, w6, w7, w8, w9] ++ R) mem aw rdata σ k C) :
    (ExecStmt config frame evm liquidatorGateStatement .reverted ∧
      RDrev midnightBytecode g s0) ∨
    ∃ (frame' : Frame) (evm' : State) (σ' : AccountMap) (mem' rdata' : ByteArray)
      (root' aw' : UInt256) (k' C' : Nat),
      ExecStmt config frame evm liquidatorGateStatement (.ok frame' evm') ∧
      (frame' = frame ∨ frame' = liquidatorGateAllowedFrame frame ⟨1⟩) ∧
      SourceState s0 I σ' evm' ∧ accountStorageStateEq evm.accountMap evm'.accountMap ∧
      MemoryPrefix mem mem' root.toNat ∧
      root.toNat ≤ root'.toNat ∧ root'.toNat ≤ root.toNat + 32 ∧
      memLoad (UInt256.ofNat 64) mem' = root' ∧ TransferBudget budgetRoot credit mem' aw' C' ∧
      RD midnightBytecode I g s0 ⟨5311⟩
        ([w0, w1, w2, w3, w4, w5, w6, w7, w8, w9] ++ R) mem' aw' rdata' σ' k' C' := by
  rcases midnightLiquidatorGateHead (by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega) hd rd with
    ⟨hzero, k1, C1, hc1, rd1⟩ | ⟨hnonzero, k1, C1, hc1, rd1⟩
  · exact Or.inr ⟨frame, evm, σ, mem, rdata, root, aw, k1, C1,
      liquidatorGateSkipped hmarket hzero, Or.inl rfl, hs, accountStorageStateEq_refl _,
      MemoryPrefix.refl _ _, le_rfl, by omega, hfree, hb.mono hc1, rd1⟩
  · rcases midnightLiquidatorGateCall (by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega)
        hroot hlower hm hfree hz (evalMarketLiquidatorGate hmarket) hs (hb.mono hc1) rd1 with
      ⟨hcall, hrev⟩ | ⟨evm', σ', out, aw2, k2, C2, hcall, htyped, hs', h32, hbool,
        hp, hfree2, hb2, rd2⟩
    · exact Or.inl ⟨liquidatorGateFailed hmarket hnonzero hcall, hrev⟩
    · simp only [List.cons_append, List.nil_append] at rd2
      have rd3 := midnight_block_8398 (by omega)
        (by jump_dest) rd2
      have rd4 := midnight_block_8358 (by simp only [List.length_cons]; omega)
        (by jump_dest) rd3
      simp only [midnight_block_8358_stack] at rd4
      have hb4 := transferBudgetAt rd4 (hb2.mono (by omega))
      rcases hbool with hfalse | htrue
      · have rd5 := midnight_block_5305_taken (by simp only [List.length_cons]; omega)
          (by rw [hfalse]; decide) (by jump_dest) rd4
        have hrev := midnight_block_8267 (by
          simp only [midnight_block_5305_taken_stack, List.length_cons]; omega) rd5
        have hsource := liquidatorGateDenied hmarket hnonzero (by
          simpa only [hfalse] using hcall)
        exact Or.inl ⟨hsource, hrev⟩
      · have rd5 := midnight_block_5305_fallthrough (by simp only [List.length_cons]; omega)
          (by rw [htrue]; decide) rd4
        have hb5 := transferBudgetAt rd5 (hb4.mono (by omega))
        have hsource := liquidatorGateAllowed hmarket hnonzero (by
          simpa only [htrue] using hcall)
        have hr : (root + UInt256.ofNat 32).toNat = root.toNat + 32 :=
          uadd_word_ofNat_toNat _ 32 (by change _ < 2^256; omega)
        exact Or.inr ⟨liquidatorGateAllowedFrame frame ⟨1⟩, evm', σ',
          liquidatorGateResultMemory mem root I.source out, out, root + UInt256.ofNat 32,
          _, _, _, hsource, Or.inr rfl, hs',
          typedCallViaEVM_static_accountStorageStateEq htyped,
          hp, by rw [hr]; omega, by rw [hr], hfree2, hb5, rd5⟩

end Benchmarks.Midnight
