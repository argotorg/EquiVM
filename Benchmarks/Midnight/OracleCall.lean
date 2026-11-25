import Benchmarks.Midnight.OracleReturnTrace
import Benchmarks.Midnight.AddressDecode
import Reasoning.VyperCalls

variable {fork : Ethereum.Fork}

/-! The oracle call in the health-check loop, paired with its source statement. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightOracleCall {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {receiver : Expr} {mem rdata : ByteArray}
    {aw cell root cp bitmap maxDebt base market index : UInt256}
    {oracle : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024) (hroot : root.toNat + 32 < 2^64)
    (hlower : 96 ≤ root.toNat) (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hcp : memLoad cell mem = cp)
    (horacle : memLoad (cp + UInt256.ofNat 96) mem = UInt256.ofNat oracle.val)
    (heval : evalExpr? config frame evm receiver = .ok (.address oracle))
    (hs : SourceState s0 I σ evm)
    (rd : RD fork midnightBytecode I g s0 ⟨19885⟩
      ([cell, bitmap, maxDebt, base, market, index] ++ R) mem aw rdata σ k C) :
    (ExecStmt fork config frame evm
        (.externalCall receiver "price" (.intLit 0) [] "price" false) .reverted ∧
      RDrev fork midnightBytecode g s0) ∨
    ∃ (evm' : State) (σ' : AccountMap) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      ExecStmt fork config frame evm
        (.externalCall receiver "price" (.intLit 0) [] "price" false)
        (.ok { frame with locals := frame.locals.insert "price" (.int (calldataWord out 0).toNat) }
          evm') ∧
      typedCallViaEVM fork config evm oracle "price" 0 [] (true, evm', out) false ∧
      SourceState s0 I σ' evm' ∧ 32 ≤ out.size ∧
      MemoryPrefix mem (oraclePriceMemory mem root out) root.toNat ∧
      memLoad (UInt256.ofNat 64) (oraclePriceMemory mem root out) = root + UInt256.ofNat 32 ∧
      RD fork midnightBytecode I g s0 ⟨19940⟩
        ([⟨20011⟩, base, index, calldataWord out 0, cp, bitmap, maxDebt, base, market, index] ++ R)
        (oraclePriceMemory mem root out) aw' out σ' k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := midnightBlocks.midnight_block_19885_packed
    (R := bitmap :: maxDebt :: base :: market :: index :: R)
    (by simp only [List.length_cons]; omega) rd
  have hclean : UInt256.land (UInt256.ofNat oracle.val) solcAddrMask =
      UInt256.ofNat oracle.val := addressWord_val_clean oracle
  simp only [midnightBlocks.midnight_block_19885_stack, hcp, horacle, hfree,
    addressMask_computed, hclean] at rd1
  have hmem : midnightBlocks.midnight_block_19885_memory (mem := mem) =
      oracleCallMemory mem root := by
    simp only [midnightBlocks.midnight_block_19885_memory, hfree]
    rfl
  rw [hmem] at rd1
  obtain ⟨evm', σ', success, out, k2, C2, hcall, hs', rd2, hout⟩ :=
    Reasoning.VyperCalls.typedStaticCallBridge (cfg := config) (name := "price") (args := [])
      (R := root :: cp :: bitmap :: maxDebt :: base :: market :: index :: R)
      rd1 hs (by native_decide)
      (by change _ = some ((oracleCallMemory mem root).readWithPadding root.toNat 4)
          rw [oracleCallMemory_read]; exact encodeOraclePrice)
      (by decide) (by simp only [List.length_cons]; omega)
  simp only [accountAddress_roundtrip] at hcall
  have hsourceCall : typedCallViaEVM fork config evm (EVM.address oracle.val) "price" 0 []
      (success, evm', out) false := by simpa only [address_of_val] using hcall
  rcases midnightOracleReturn (R := R) success (by omega) (by change out.size < 2^256; omega)
      hroot rd2 with ⟨hbad, hrev⟩ | ⟨htrue, h32, aw3, k3, C3, rd3⟩
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
    simp only [hmin] at rd3
    change RD fork midnightBytecode I g s0 ⟨19940⟩
      ([⟨20011⟩, base, index, memLoad root (oraclePriceMemory mem root out), cp, bitmap,
        maxDebt, base, market, index] ++ R)
      (oraclePriceMemory mem root out) aw3 out σ' k3 C3 at rd3
    have hp := oraclePriceMemory_properties mem root h32 hlower
    rw [hp.2.2.1] at rd3
    refine Or.inr ⟨evm', σ', out, aw3, k3, C3, ?_, hcall, hs', h32, hp.2.2.2, hp.2.1, rd3⟩
    exact ExecStmt.externalCallSuccess (Or.inl wordOfInt_zero) heval
      (by simp only [evalExpr?, pure]) (by rfl) hsourceCall (decodeOraclePrice h32)

end Benchmarks.Midnight
