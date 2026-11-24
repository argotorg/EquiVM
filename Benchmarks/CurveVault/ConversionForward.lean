import Benchmarks.CurveVault.ConvertAssetsInternal
import Benchmarks.CurveVault.ConversionArguments

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

abbrev vaultConversionFunction (toShares : Bool) : FunctionDecl :=
  if toShares then vaultConvertSharesFunction else vaultConvertAssetsFunction

theorem vaultConversionForward (toShares isFloor : Bool) {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {input total dest returnPc : UInt256} {R : List UInt256} {locals : Store}
    {args : List Expr} {retVar : Ident}
    (hs : SourceState s0 I σ evm) (hsize : 416 ≤ mem.size)
    (hmi : memLoad (UInt256.ofNat 320) mem = input)
    (hmf : memLoad (UInt256.ofNat 352) mem = if isFloor then ⟨1⟩ else ⟨0⟩)
    (hmt : memLoad (UInt256.ofNat 384) mem = total)
    (hargs : evalExprs? config {contract := contract, locals := locals} evm args =
      .ok [.int (Int.ofNat input.toNat), .bool isFloor, .int (Int.ofNat total.toNat)])
    (hstack : R.length + 14 ≤ 1024) (hvalid : (D_J vaultBytecode 0).contains returnPc = true)
    (h : RD fork vaultBytecode I g s0 (if toShares then UInt256.ofNat 7108 else UInt256.ofNat 7332)
      (dest :: returnPc :: R) mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (scratch : ByteArray) (value aw' : UInt256)
        (out : ByteArray) (k' C' : Nat),
      ExecStmt fork config {contract := contract, locals := locals} evm
        (.internalCall (vaultConversionFunction toShares).name args retVar)
        (.ok {contract := contract, locals := locals.insert retVar (.int (Int.ofNat value.toNat))} evm') ∧
      SourceState s0 I σ' evm' ∧ WordMemoryRange mem scratch 576 UInt256.size ∧
      RD fork vaultBytecode I g s0 returnPc R (value.toByteArray.write 0 scratch dest.toNat 32) aw' out σ' k' C') ∨
    (ExecStmt fork config {contract := contract, locals := locals} evm
      (.internalCall (vaultConversionFunction toShares).name args retVar) .reverted ∧ RDrev fork vaultBytecode g s0) := by
  have hcallee : vaultConversionRoutineOutcome fork s0 evm I g (vaultConversionFunction toShares)
      (vaultConversionLocals (if toShares then "_assets" else "_shares") input isFloor total) mem dest returnPc R := by
    cases toShares
    · exact vaultConvertAssetsRoutine hs hsize hmi hmf hmt hstack hvalid h
    · exact vaultConvertSharesRoutine hs hsize hmi hmf hmt hstack hvalid h
  rcases hcallee with ⟨evm', σ', calleeLocals, scratch, value, aw', out, k', C', hbody, hs', hframe, rd⟩ | ⟨hbody, hrev⟩
  · exact Or.inl ⟨evm', σ', scratch, value, aw', out, k', C',
      internalCallFunctionReturn (callee := vaultConversionFunction toShares) hargs
        (by cases toShares <;> rfl) (by cases toShares <;> rfl) hbody, hs', hframe, rd⟩
  · exact Or.inr ⟨internalCallFunctionRevert (callee := vaultConversionFunction toShares) hargs
      (by cases toShares <;> rfl) (by cases toShares <;> rfl) hbody, hrev⟩

end Benchmarks.CurveVault
