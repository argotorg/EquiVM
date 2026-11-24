import Benchmarks.CurveVault.MutationConversion
import Benchmarks.CurveVault.CreditSource
import Benchmarks.CurveVault.RuntimeBlocks_011

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultDepositConversionBody : List Stmt :=
  [.internalCall "_convert_to_shares" [.var "_assets", .boolLit true, .var "total_assets"] "to_mint",
    .require (.binary .gt (.var "to_mint") (.intLit 0))]

theorem vaultDepositConversion {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {total : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hsize : 672 ≤ mem.size)
    (ha : locals.get? "_assets" = some (.int (Int.ofNat (calldataWord I.calldata 4).toNat)))
    (ht : locals.get? "total_assets" = some (.int (Int.ofNat total.toNat)))
    (hmt : memLoad (UInt256.ofNat 640) mem = total) (hstack : R.length + 14 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 2498) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (mem' out : ByteArray) (shares aw' : UInt256) (k' C' : Nat),
      ExecBlock fork config {contract := contract, locals := locals} evm vaultDepositConversionBody
        (.ok {contract := contract, locals := locals.insert "to_mint" (.int (Int.ofNat shares.toNat))} evm') ∧
      SourceState s0 I σ' evm' ∧ WordMemoryRange mem mem' 576 672 ∧ 704 ≤ mem'.size ∧
      memLoad (UInt256.ofNat 672) mem' = shares ∧
      RD fork vaultBytecode I g s0 (UInt256.ofNat 2666) R mem' aw' out σ' k' C') ∨
    (ExecBlock fork config {contract := contract, locals := locals} evm vaultDepositConversionBody
      .reverted ∧ RDrev fork vaultBytecode g s0) := by
  let assets := calldataWord I.calldata 4
  have hargs : evalExprs? config {contract := contract, locals := locals} evm
      [.var "_assets", .boolLit true, .var "total_assets"] =
      .ok [.int (Int.ofNat assets.toNat), .bool true, .int (Int.ofNat total.toNat)] := by
    simp only [evalExprs?, evalExpr?, ha, ht, EvalResult.ofOption, EvalResult.bind, bind, pure]
    rfl
  rcases vaultMutationConversion .deposit (retVar := "to_mint") hs hsize hmt hargs hstack h with
    ⟨evm1, σ1, returned, shares, aw1, out, k1, C1, hcall, hs1, hframe, hsize1, hread, rdCheck⟩ | ⟨hcall, hrev⟩
  swap
  · exact Or.inr ⟨ExecBlock.consRevert hcall, hrev⟩
  let prepared := shares.toByteArray.write 0 returned 672 32
  have hgap (m : ByteArray) (off : Nat) (hoff : off ≤ 704) : off - m.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize off (by omega))
  have hread' : memLoad (UInt256.ofNat 672) prepared = shares :=
    memLoad_write_back _ _ 672 (by decide +kernel) (hgap _ _ (by omega))
  have hget : (locals.insert "to_mint" (.int (Int.ofNat shares.toNat))).get? "to_mint" =
      some (.int (Int.ofNat shares.toNat)) := store_get_self _ _ _
  have heval := evalExpr_gt_zero (evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm1) hget)
  by_cases hz : shares = ⟨0⟩
  · obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_2530_fallthrough_packed (by omega)
      (by
        change memLoad (UInt256.ofNat 672) ((memLoad (UInt256.ofNat 704) returned).toByteArray.write 0 returned 672 32) = _
        rw [hread, hread', hz]; rfl) rdCheck
    have hrev := vaultBlocks.vault_block_2547 (by omega) rdFail
    refine Or.inr ⟨ExecBlock.consNormal hcall (ExecBlock.consRevert (ExecStmt.requireFalse ?_)), hrev⟩
    simpa only [hz, show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.lt_irrefl, decide_false] using heval
  have hpos : 0 < shares.toNat := by
    have hne : shares.toNat ≠ 0 := fun heq => hz (u256_inj heq)
    omega
  obtain ⟨aw2, k2, C2, rdNext⟩ := vaultBlocks.vault_block_2530_taken_packed (by omega)
    (by
      change memLoad (UInt256.ofNat 672) ((memLoad (UInt256.ofNat 704) returned).toByteArray.write 0 returned 672 32) ≠ _
      rw [hread, hread']; exact hz) (by native_decide) rdCheck
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 2666) R
    ((memLoad (UInt256.ofNat 704) returned).toByteArray.write 0 returned 672 32) aw2 out σ1 k2 C2 at rdNext
  rw [hread] at rdNext
  have hfinalFrame : WordMemoryRange mem prepared 576 672 :=
    hframe.trans (wordMemoryRange_write returned shares 672 576 672 (hgap _ _ (by omega)) (Or.inl (by omega)))
  exact Or.inl ⟨evm1, σ1, prepared, out, shares, aw2, k2, C2,
    ExecBlock.consNormal hcall (ExecBlock.consNormal (ExecStmt.requireTrue
      (by simpa only [hpos, decide_true] using heval)) ExecBlock.nil), hs1, hfinalFrame,
    toByteArray_write_size_ge_off_add32 _ _ 672 (hgap _ _ (by omega)), hread', rdNext⟩

end Benchmarks.CurveVault
