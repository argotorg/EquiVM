import Benchmarks.Midnight.LiquidatorGateMemory
import Benchmarks.Midnight.LiquidatorGateReturn
import Benchmarks.Midnight.StaticCallBridgeGas
import Benchmarks.Midnight.WordReplyMemory

variable {fork : Ethereum.Fork}

/-! The liquidator gate's STATICCALL agrees with the source's opaque external call. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

theorem midnightLiquidatorGateCall {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {receiver : Expr} {mem rdata : ByteArray}
    {aw root budgetRoot : UInt256} {credit : Nat} {gate : AccountAddress}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024) (hroot : root.toNat + 36 < 2^64)
    (hlower : 832 ≤ root.toNat) (hm : 832 ≤ mem.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (heval : evalExpr? config frame evm receiver = .ok (.address gate))
    (hs : SourceState s0 I σ evm) (hb : TransferBudget budgetRoot credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨8315⟩
      (UInt256.ofNat gate.val :: solcAddrMask :: UInt256.ofNat 32 :: UInt256.ofNat 36 :: R)
      mem aw rdata σ k C) :
    (ExecStmt fork config frame evm
        (.externalCall receiver "canLiquidate" (.intLit 0) [.env .caller] "allowed" false)
        .reverted ∧ RDrev fork midnightBytecode g s0) ∨
    ∃ (evm' : State) (σ' : AccountMap) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      ExecStmt fork config frame evm
        (.externalCall receiver "canLiquidate" (.intLit 0) [.env .caller] "allowed" false)
        (.ok { frame with locals := (frame.locals.insert "allowed"
          (wordToElem .bool (calldataWord out 0))) } evm') ∧
      typedCallViaEVM fork config evm gate "canLiquidate" 0 [.address I.source]
        (true, evm', out) false ∧
      SourceState s0 I σ' evm' ∧ 32 ≤ out.size ∧
      (calldataWord out 0 = ⟨0⟩ ∨ calldataWord out 0 = ⟨1⟩) ∧
      MemoryPrefix mem (liquidatorGateResultMemory mem root I.source out) root.toNat ∧
      memLoad (UInt256.ofNat 64) (liquidatorGateResultMemory mem root I.source out) =
        root + UInt256.ofNat 32 ∧
      TransferBudget budgetRoot credit (liquidatorGateResultMemory mem root I.source out) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨8398⟩ (calldataWord out 0 :: R)
        (liquidatorGateResultMemory mem root I.source out) aw' out σ' k' C' := by
  have ha : evalExprs? config frame evm [.env .caller] = .ok [.address I.source] := by
    simp [evalExprs?, evalExpr?, envValue, hs.env, bind, pure, EvalResult.bind]
  have rd1 := midnight_block_8315 (by omega) rd
  have hb1 := transferBudgetAt (root := budgetRoot) (credit := credit) rd1 (by
    simp only [midnight_block_8315_memory]
    transfer_budget hb)
  have hclean : UInt256.land (UInt256.ofNat gate.val) solcAddrMask = UInt256.ofNat gate.val :=
    addressWord_val_clean gate
  simp only [midnight_block_8315_stack, hfree, hclean] at rd1
  have hmem : midnight_block_8315_memory (ee := I) (mem := mem) =
      liquidatorGateCallMemory mem root I.source := by
    simp only [midnight_block_8315_memory, hfree,
      uadd_word_ofNat_toNat root 4 (by change _ < 2^256; omega)]
    rfl
  rw [hmem] at rd1 hb1
  simp only [hfree] at hb1
  obtain ⟨evm', σ', success, out, k2, C2, hcall, hs', hc2, rd2, hout⟩ :=
    typedStaticCallBridgeMono (cfg := config) (name := "canLiquidate") (args := [.address I.source])
      (R := root :: R) rd1 hs (by native_decide)
      (by change _ = some ((liquidatorGateCallMemory mem root I.source).readWithPadding root.toNat 36)
          rw [liquidatorGateCallMemory_read]; exact encodeLiquidatorGate _)
      (by decide) (by simp only [List.length_cons]; omega)
  have hb2 := transferBudgetAt (root := budgetRoot) (credit := credit) rd2 (by
    rcases hb1 with hsmall | ⟨halign, hf⟩
    · exact Or.inl hsmall
    · refine Or.inr ⟨halign, staticCallMemoryFunding hf hc2 ?_ ?_⟩
      all_goals
        have hcov := hf.covered
        simp only [MemoryCovered, liquidatorGateCallMemory_size] at hcov
        change root.toNat + _ ≤ _
        simp only [show (UInt256.ofNat 36).toNat = 36 from rfl,
          show (UInt256.ofNat 32).toNat = 32 from rfl]
        omega)
  have hout' : out.size < UInt256.size := by change out.size < 2^256; omega
  rw [wordReplyMemory_eq _ _ _ hout'] at rd2 hb2
  have hcovered : root.toNat + 32 ≤ (liquidatorGateCallMemory mem root I.source).size := by
    rw [liquidatorGateCallMemory_size]; omega
  have hz2 : memLoad (UInt256.ofNat 800)
      (wordReplyMemory (liquidatorGateCallMemory mem root I.source) out root) = ⟨0⟩ := by
    rw [wordReplyMemory_load_before _ _ _ _ hcovered (by exact hlower),
      (liquidatorGateCallMemory_prefix mem root I.source).load
        (UInt256.ofNat 800) (by decide) hlower hm, hz]
  have hword : 32 ≤ out.size → memLoad root
      (writeWord (wordReplyMemory (liquidatorGateCallMemory mem root I.source) out root)
        64 (root + UInt256.ofNat 32)) = calldataWord out 0 := by
    intro h32
    rw [memLoad_writeWord_preserved _ _ _ _ (by
      rw [wordReplyMemory_size _ _ _ hcovered]; exact hcovered) (Or.inr (by omega)),
      wordReplyMemory_load _ _ _ hcovered h32]
  simp only [accountAddress_roundtrip] at hcall
  have hsourceCall : typedCallViaEVM fork config evm (EVM.address gate.val) "canLiquidate" 0
      [.address I.source] (success, evm', out) false := by
    simpa only [address_of_val] using hcall
  rcases midnightLiquidatorGateReturn success hstack hout' (by omega) hz2 hword hb2 rd2 with
    ⟨hbad, hrev⟩ | ⟨htrue, h32, hbool, aw3, k3, C3, hb3, rd3⟩
  · refine Or.inl ⟨?_, hrev⟩
    rcases hbad with hfalse | hdecode
    · subst success
      exact ExecStmt.externalCallFailure (Or.inl wordOfInt_zero) heval
        (by simp only [evalExpr?, pure]) ha hsourceCall
    · cases success with
      | false =>
        exact ExecStmt.externalCallFailure (Or.inl wordOfInt_zero) heval
          (by simp only [evalExpr?, pure]) ha hsourceCall
      | true =>
        exact ExecStmt.externalCallReturnDecodeRevert (Or.inl wordOfInt_zero) heval
          (by simp only [evalExpr?, pure]) ha hsourceCall
          (by rw [decodeLiquidatorGate, if_neg hdecode])
  · subst success
    simp only [wordReplyMemory, Nat.min_eq_left h32] at rd3 hb3
    have hp := liquidatorGateResultMemory_properties mem root I.source h32 (by omega)
    refine Or.inr ⟨evm', σ', out, aw3, k3, C3, ?_, hcall, hs', h32, hbool,
      hp.2.2.2, hp.2.1, hb3, rd3⟩
    exact ExecStmt.externalCallSuccess (value := [wordToElem .bool (calldataWord out 0)])
      (Or.inl wordOfInt_zero) heval
      (by simp only [evalExpr?, pure]) ha hsourceCall
      (by rw [decodeLiquidatorGate, if_pos ⟨h32, hbool⟩])

end Benchmarks.Midnight
