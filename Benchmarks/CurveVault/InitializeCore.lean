import Benchmarks.CurveVault.InitializeLocals
import Benchmarks.CurveVault.InitializeStart
import Benchmarks.CurveVault.InitializePrecision
import Benchmarks.CurveVault.InitializeConfig
import Benchmarks.CurveVault.InitializeSymbolCall
import Benchmarks.CurveVault.InitializeStringWrites

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultInitializeAfterGuard {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {amm controller token collateral : UInt256} {R : List UInt256}
    (hs : SourceState s0 I σ evm)
    (ha : amm.toNat < EVM.addressModulus) (hc : controller.toNat < EVM.addressModulus)
    (ht : token.toNat < EVM.addressModulus) (hl : collateral.toNat < EVM.addressModulus)
    (hmem : mem.size = 192)
    (hma : memLoad (UInt256.ofNat 64) mem = amm) (hmc : memLoad (UInt256.ofNat 96) mem = controller)
    (hmt : memLoad (UInt256.ofNat 128) mem = token) (hml : memLoad (UInt256.ofNat 160) mem = collateral)
    (hperm : I.perm = true) (haw : aw.toNat ≤ 10) (hstack : R.length + 7 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 221) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (locals' : Store),
      ExecBlock fork config {contract := contract, locals := vaultInitializeLocals amm controller token collateral} evm
        (initializeTransition.body.drop 2) (.ok {contract := contract, locals := locals'} evm') ∧
      SourceState s0 I σ' evm' ∧ RDret fork vaultBytecode g s0 σ' ByteArray.empty) ∨
    (ExecBlock fork config {contract := contract, locals := vaultInitializeLocals amm controller token collateral} evm
      (initializeTransition.body.drop 2) .reverted ∧ RDrev fork vaultBytecode g s0) := by
  let locals := vaultInitializeLocals amm controller token collateral
  rcases vaultInitializeBorrowedDecimals (locals := locals) hs
    (by simp only [locals, vaultInitializeLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl)
    (by simp only [locals, vaultInitializeLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl)
    hmt ht hperm haw hstack h with
    ⟨evm1, σ1, decimals, mem1, out1, aw1, k1, C1, _, haw1, s1, hs1, hmem1, hmem1eq, hf1, rd294⟩ | ⟨s1, hrev⟩
  swap
  · refine Or.inr ⟨?_, hrev⟩
    change ExecBlock fork _ _ _ ((initializeTransition.body.drop 2 |>.take 2) ++ initializeTransition.body.drop 4) _
    exact execBlock_reverted_append s1
  let locals1 := locals.insert "__c0" (.int (Int.ofNat decimals.toNat))
  rcases vaultInitializePrecision (evm := evm1) (locals := locals1) (by simp [locals1]) haw1 (by omega) rd294 with
    ⟨_, aw2, k2, C2, haw2, s2, rd327⟩ | ⟨s2, hrev⟩
  swap
  · refine Or.inr ⟨?_, hrev⟩
    change ExecBlock fork _ _ _ ((initializeTransition.body.drop 2 |>.take 2) ++ initializeTransition.body.drop 4) _
    exact execBlock_append s1 (ExecBlock.consRevert s2)
  let power := UInt256.exp ⟨10⟩ (UInt256.sub ⟨18⟩ decimals)
  let locals2 := locals1.insert "borrowed_precision" (.int (Int.ofNat power.toNat))
  let mem2 := decimals.toByteArray.write 0 mem1 288 32
  have hgap : 288 - mem1.size < USize.size := lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 288 (by omega))
  have hmem2 : mem2.size = 320 := by
    change (writeWord mem1 288 decimals).size = 320
    rw [writeWord_size _ _ _ hgap, hmem1eq, hmem]
    rfl
  have hf2 : WordMemoryRange mem mem2 0 192 :=
    (hf1.mono (by omega) (by omega)).trans (wordMemoryRange_write mem1 decimals 288 0 192 hgap (Or.inl (by omega)))
  have hloads (off : Nat) (hoff : off + 32 ≤ 192) : memLoad (UInt256.ofNat off) mem2 = memLoad (UInt256.ofNat off) mem :=
    hf2.load off (by omega) hoff (by omega) (by change off < 2 ^ 256; omega)
  obtain ⟨evm2, σ2, mem3, gasArg, aw3, k3, C3, s3, hs2, haw3, hmem3, _, hcd, rd388⟩ :=
    vaultInitializeConfigWrites (locals := locals2) hs1
      (by simp only [locals2, locals1, locals, vaultInitializeLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl)
      (by simp only [locals2, locals1, locals, vaultInitializeLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl)
      (by simp only [locals2, locals1, locals, vaultInitializeLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl)
      (by exact store_get_self _ _ _)
      (by
        intro name hn
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl | rfl | rfl | rfl <;>
          simp only [locals2, locals1, locals, vaultInitializeLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty] <;> rfl)
      ha hc hl hmem2 ((hloads 64 (by omega)).trans hma) ((hloads 96 (by omega)).trans hmc)
      ((hloads 128 (by omega)).trans hmt) ((hloads 160 (by omega)).trans hml) hperm haw2 hstack rd327
  rcases vaultInitializeSymbolCall (locals := locals2) hs2
    (by simp only [locals2, locals1, locals, vaultInitializeLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl)
    hcd hmem3 haw3 hstack rd388 with
    ⟨evm3, σ3, size, ptr, mem4, out4, aw4, k4, C4, s4, hs3, hn, hp, hfull, hbound, hheader, rd476⟩ | ⟨s4, hrev⟩
  swap
  · refine Or.inr ⟨?_, hrev⟩
    change ExecBlock fork _ _ _ ((initializeTransition.body.drop 2 |>.take 2) ++ initializeTransition.body.drop 4) _
    apply execBlock_append s1 (ExecBlock.consNormal s2 ?_)
    change ExecBlock fork _ _ _ ((initializeTransition.body.drop 5 |>.take 5) ++ initializeTransition.body.drop 10) _
    exact execBlock_append s3 (ExecBlock.consRevert s4)
  let word := memLoad (UInt256.ofNat (ptr.toNat + 32)) mem4
  have hword : word.toByteArray = mem4.readWithPadding (ptr.toNat + 32) 32 := by
    rw [memLoad_toByteArray, ulit_toNat' _ (by change ptr.toNat + 32 < 2 ^ 256; omega)]
  let locals3 := locals2.insert "borrowed_symbol" (vaultBorrowedSymbol size.toNat word.toByteArray)
  rw [← hword] at s4
  obtain ⟨s5, hs4⟩ := vaultInitializeStringSource (fork := fork) (hperm := by assumption) (locals := locals3) hs3 (by exact store_get_self _ _ _)
    (by
      intro name hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl <;>
        simp only [locals3, locals2, locals1, locals, vaultInitializeLocals,
          Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty] <;> rfl) hn
  have hret := vaultInitializeStringWrites hperm hstack hn hbound hp hfull hheader rd476
  refine Or.inl ⟨_, _, vaultInitializeStringLocals locals3 size word, ?_, hs4, hret⟩
  change ExecBlock fork _ _ _ ((initializeTransition.body.drop 2 |>.take 2) ++ initializeTransition.body.drop 4) _
  apply execBlock_append s1 (ExecBlock.consNormal s2 ?_)
  change ExecBlock fork _ _ _ ((initializeTransition.body.drop 5 |>.take 5) ++ initializeTransition.body.drop 10) _
  exact execBlock_append s3 (ExecBlock.consNormal s4 s5)

end Benchmarks.CurveVault
