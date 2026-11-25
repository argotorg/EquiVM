import Benchmarks.Midnight.SupplyOracleReturn
import Benchmarks.Midnight.StaticCallBridgeGas
import Benchmarks.Midnight.AddressDecode
import Benchmarks.Midnight.RuntimeBlocks_064

variable {fork : Ethereum.Fork}

/-! The oracle call made when a position first receives a collateral token. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem supplyOracleCall {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {receiver : Expr} {mem rdata : ByteArray}
    {aw cell root cp base budgetRoot : UInt256} {credit : Nat}
    {oracle : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024) (hroot : root.toNat + 32 < 2^64)
    (hlower : 96 ≤ root.toNat) (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hcp : memLoad cell mem = cp)
    (horacle : memLoad (cp + UInt256.ofNat 96) mem = UInt256.ofNat oracle.val)
    (heval : evalExpr? config frame evm receiver = .ok (.address oracle))
    (hs : SourceState s0 I σ evm) (hb : TransferBudget budgetRoot credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨17240⟩
      ([cell, UInt256.ofNat 96, solcAddrMask, UInt256.ofNat 32, UInt256.ofNat 4, base] ++ R)
      mem aw rdata σ k C) :
    (ExecStmt fork config frame evm
        (.externalCall receiver "price" (.intLit 0) [] "__c1" false) .reverted ∧
      RDrev fork midnightBytecode g s0) ∨
    ∃ (evm' : State) (σ' : AccountMap) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      ExecStmt fork config frame evm
        (.externalCall receiver "price" (.intLit 0) [] "__c1" false)
        (.ok { frame with locals := frame.locals.insert "__c1" (.int (calldataWord out 0).toNat) }
          evm') ∧
      typedCallViaEVM fork config evm oracle "price" 0 [] (true, evm', out) false ∧
      SourceState s0 I σ' evm' ∧ 32 ≤ out.size ∧
      MemoryPrefix mem (oraclePriceMemory mem root out) root.toNat ∧
      memLoad (UInt256.ofNat 64) (oraclePriceMemory mem root out) = root + UInt256.ofNat 32 ∧
      TransferBudget budgetRoot credit (oraclePriceMemory mem root out) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨17274⟩ (UInt256.ofNat 255 :: base :: R)
        (oraclePriceMemory mem root out) aw' out σ' k' C' := by
  have rd1 := midnightBlocks.midnight_block_17240 (R := base :: R)
    (by simp only [List.length_cons]; omega) rd
  have hb1 := transferBudgetAt (root := budgetRoot) (credit := credit) rd1 (by
    simp only [midnightBlocks.midnight_block_17240_memory]
    transfer_budget hb)
  have hclean : UInt256.land (UInt256.ofNat oracle.val) solcAddrMask =
      UInt256.ofNat oracle.val := addressWord_val_clean oracle
  simp only [midnightBlocks.midnight_block_17240_stack, hcp, horacle, hfree, hclean] at rd1
  simp only [hcp, hfree] at hb1
  have hmem : midnightBlocks.midnight_block_17240_memory (mem := mem) =
      oracleCallMemory mem root := by
    simp only [midnightBlocks.midnight_block_17240_memory, hfree]
    rfl
  rw [hmem] at rd1 hb1
  obtain ⟨evm', σ', success, out, k2, C2, hcall, hs', hc2, rd2, hout⟩ :=
    typedStaticCallBridgeMono (cfg := config) (name := "price") (args := [])
      (R := root :: base :: R) rd1 hs (by native_decide)
      (by change _ = some ((oracleCallMemory mem root).readWithPadding root.toNat 4)
          rw [oracleCallMemory_read]; exact encodeOraclePrice)
      (by decide) (by simp only [List.length_cons]; omega)
  have hb2 := transferBudgetAt (root := budgetRoot) (credit := credit) rd2 (by
    rcases hb1 with hsmall | ⟨halign, hf⟩
    · exact Or.inl hsmall
    · refine Or.inr ⟨halign, staticCallMemoryFunding hf hc2 ?_ ?_⟩
      all_goals
        have hcov := hf.covered
        simp only [MemoryCovered, oracleCallMemory, writeWord_sparse_size] at hcov
        simp only [show (UInt256.ofNat 4).toNat = 4 from rfl,
          show (UInt256.ofNat 32).toNat = 32 from rfl]
        omega)
  simp only [accountAddress_roundtrip] at hcall
  have hsourceCall : typedCallViaEVM fork config evm (EVM.address oracle.val) "price" 0 []
      (success, evm', out) false := by simpa only [address_of_val] using hcall
  rcases supplyOracleReturn (R := R) success (by omega) (by change out.size < 2^256; omega)
      hroot hb2 rd2 with ⟨hbad, hrev⟩ | ⟨htrue, h32, aw3, k3, C3, hb3, rd3⟩
  · refine Or.inl ⟨?_, hrev⟩
    rcases hbad with hfalse | hshort
    · subst success
      exact ExecStmt.externalCallFailure (Or.inl wordOfInt_zero) heval
        (by simp only [evalExpr?, pure]) (by rfl) hsourceCall
    · cases success with
      | false =>
        exact ExecStmt.externalCallFailure (Or.inl wordOfInt_zero) heval
          (by simp only [evalExpr?, pure]) (by rfl) hsourceCall
      | true =>
        exact ExecStmt.externalCallReturnDecodeRevert (Or.inl wordOfInt_zero) heval
          (by simp only [evalExpr?, pure]) (by rfl) hsourceCall (decodeOraclePrice_short hshort)
  · subst success
    have hn : (UInt256.ofNat out.size).toNat = out.size :=
      UInt256.toNat_ofNat_of_lt (by change out.size < 2^256; omega)
    have hmin : min (UInt256.ofNat 32) (UInt256.ofNat out.size) = UInt256.ofNat 32 := by
      change (if UInt256.ofNat 32 ≤ UInt256.ofNat out.size then UInt256.ofNat 32
        else UInt256.ofNat out.size) = _
      rw [if_pos (show UInt256.ofNat 32 ≤ UInt256.ofNat out.size from by
        change 32 ≤ (UInt256.ofNat out.size).toNat
        rw [hn]
        exact h32)]
    simp only [hmin] at rd3 hb3
    have hp := oraclePriceMemory_properties mem root h32 hlower
    refine Or.inr ⟨evm', σ', out, aw3, k3, C3, ?_, hcall, hs', h32, hp.2.2.2,
      hp.2.1, hb3, rd3⟩
    exact ExecStmt.externalCallSuccess (Or.inl wordOfInt_zero) heval
      (by simp only [evalExpr?, pure]) (by rfl) hsourceCall (decodeOraclePrice h32)

end Benchmarks.Midnight
