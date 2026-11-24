import Benchmarks.CurveVault.MutationConversionSetup
import Benchmarks.CurveVault.ConversionForward

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultMutationConversion (flow : VaultFlow) {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {total : UInt256} {R : List UInt256} {locals : Store} {args : List Expr} {retVar : Ident}
    (hs : SourceState s0 I σ evm) (hsize : flow.conversionTotalOffset + 32 ≤ mem.size)
    (hmt : memLoad (UInt256.ofNat flow.conversionTotalOffset) mem = total)
    (hargs : evalExprs? config {contract := contract, locals := locals} evm args =
      .ok [.int (Int.ofNat (calldataWord I.calldata 4).toNat), .bool flow.conversionFloor, .int (Int.ofNat total.toNat)])
    (hstack : R.length + 14 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat flow.conversionEntry) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (mem' : ByteArray) (value aw' : UInt256) (out : ByteArray) (k' C' : Nat),
      ExecStmt fork config {contract := contract, locals := locals} evm
        (.internalCall (vaultConversionFunction flow.conversionToShares).name args retVar)
        (.ok {contract := contract, locals := locals.insert retVar (.int (Int.ofNat value.toNat))} evm') ∧
      SourceState s0 I σ' evm' ∧
      WordMemoryRange (vaultMutationConversionBase flow mem total) mem' 576 672 ∧
      736 ≤ mem'.size ∧ memLoad (UInt256.ofNat 704) mem' = value ∧
      RD fork vaultBytecode I g s0 (UInt256.ofNat flow.conversionNext) R mem' aw' out σ' k' C') ∨
    (ExecStmt fork config {contract := contract, locals := locals} evm
      (.internalCall (vaultConversionFunction flow.conversionToShares).name args retVar) .reverted ∧
      RDrev fork vaultBytecode g s0) := by
  obtain ⟨aw0, k0, C0, rdCall⟩ := vaultMutationConversionSetup flow hsize hmt (by omega) h
  let baseMem := vaultMutationConversionBase flow mem total
  let flag : UInt256 := if flow.conversionFloor then ⟨1⟩ else ⟨0⟩
  obtain ⟨hargsSize, hmi, hmf, hmt'⟩ := vaultConversionArgsMemory_reads baseMem (calldataWord I.calldata 4) flag total
  rcases vaultConversionForward flow.conversionToShares flow.conversionFloor hs hargsSize hmi hmf hmt' hargs
    hstack (by cases flow <;> native_decide) rdCall with
    ⟨evm1, σ1, scratch, value, aw1, out, k1, C1, hcall, hs1, hframe, rdNext⟩ | ⟨hcall, hrev⟩
  swap
  · exact Or.inr ⟨hcall, hrev⟩
  have hgap : 704 - scratch.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 704 (by omega))
  have hframe0 := vaultConversionArgsMemory_frame baseMem (calldataWord I.calldata 4) flag total
  exact Or.inl ⟨evm1, σ1, _, value, aw1, out, k1, C1, hcall, hs1,
    ((hframe0.mono (by omega) (by decide +kernel)).trans (hframe.mono (le_refl _) (by decide +kernel))).trans
      (wordMemoryRange_write scratch value 704 576 672 hgap (Or.inl (by omega))),
    toByteArray_write_size_ge_off_add32 _ _ 704 hgap,
    memLoad_write_back _ _ 704 (by decide +kernel) hgap, rdNext⟩

end Benchmarks.CurveVault
