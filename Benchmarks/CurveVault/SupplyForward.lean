import Benchmarks.CurveVault.MintInternal
import Benchmarks.CurveVault.BurnInternal

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

abbrev vaultSupplyFunction (isMint : Bool) : FunctionDecl :=
  if isMint then vaultMintFunction else vaultBurnFunction

def vaultSupplyLocals (isMint : Bool) (owner : AccountAddress) (value : UInt256) : Store :=
  if isMint then vaultMintLocals owner value else vaultBurnLocals owner value

theorem vaultSupplyForward (isMint : Bool) {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {owner value returnPc : UInt256} {R : List UInt256} {locals : Store}
    {args : List Expr} {retVar : Ident}
    (hs : SourceState s0 I σ evm) (hsize : 128 ≤ mem.size)
    (hmo : memLoad (UInt256.ofNat 64) mem = owner)
    (hmv : memLoad (UInt256.ofNat 96) mem = value) (hcanon : owner.toNat < EVM.addressModulus)
    (hargs : evalExprs? config {contract := contract, locals := locals} evm args =
      .ok [.address (AccountAddress.ofNat owner.toNat), .int (Int.ofNat value.toNat)])
    (hperm : I.perm = true) (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J vaultBytecode 0).contains returnPc = true)
    (h : RD fork vaultBytecode I g s0 (if isMint then UInt256.ofNat 7682 else UInt256.ofNat 8024)
      (returnPc :: R) mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (aw' : UInt256) (k' C' : Nat),
      ExecStmt fork config {contract := contract, locals := locals} evm
        (.internalCall (vaultSupplyFunction isMint).name args retVar)
        (.ok {contract := contract, locals := locals.insert retVar .unit} evm') ∧
      SourceState s0 I σ' evm' ∧
      RD fork vaultBytecode I g s0 returnPc R (vaultSupplyMemory mem owner value) aw' rdata σ' k' C') ∨
    (ExecStmt fork config {contract := contract, locals := locals} evm
      (.internalCall (vaultSupplyFunction isMint).name args retVar) .reverted ∧ RDrev fork vaultBytecode g s0) := by
  let calleeLocals := vaultSupplyLocals isMint (AccountAddress.ofNat owner.toNat) value
  have hcallee :
      (∃ (evm' : State) (σ' : AccountMap) (aw' : UInt256) (k' C' : Nat),
        ExecFuncBody fork config {contract := contract, locals := calleeLocals} evm (vaultSupplyFunction isMint).body
          (.returned {contract := contract, locals := calleeLocals} evm' none) ∧ SourceState s0 I σ' evm' ∧
        RD fork vaultBytecode I g s0 returnPc R (vaultSupplyMemory mem owner value) aw' rdata σ' k' C') ∨
      (ExecFuncBody fork config {contract := contract, locals := calleeLocals} evm (vaultSupplyFunction isMint).body
        .reverted ∧ RDrev fork vaultBytecode g s0) := by
    cases isMint with
    | false =>
      exact vaultBurnRoutine hs hsize hmo hmv hcanon
        (by simp [calleeLocals, vaultSupplyLocals, vaultBurnLocals, Std.HashMap.getElem?_insert])
        (by simp [calleeLocals, vaultSupplyLocals, vaultBurnLocals, Std.HashMap.getElem?_insert])
        (by simp [calleeLocals, vaultSupplyLocals, vaultBurnLocals])
        (by simp only [calleeLocals, vaultSupplyLocals, Bool.false_eq_true, if_false, vaultBurnLocals,
          Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl) hperm hstack hvalid h
    | true =>
      exact vaultMintRoutine hs hsize hmo hmv hcanon
        (by simp [calleeLocals, vaultSupplyLocals, vaultMintLocals, Std.HashMap.getElem?_insert])
        (by simp [calleeLocals, vaultSupplyLocals, vaultMintLocals, Std.HashMap.getElem?_insert])
        (by simp [calleeLocals, vaultSupplyLocals, vaultMintLocals])
        (by simp only [calleeLocals, vaultSupplyLocals, if_true, vaultMintLocals,
          Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl) hperm hstack hvalid h
  rcases hcallee with ⟨evm', σ', aw', k', C', hbody, hs', rd⟩ | ⟨hbody, hrev⟩
  · exact Or.inl ⟨evm', σ', aw', k', C',
      internalCallFunctionReturn (callee := vaultSupplyFunction isMint) hargs
        (by cases isMint <;> rfl) (by cases isMint <;> rfl) hbody, hs', rd⟩
  · exact Or.inr ⟨internalCallFunctionRevert (callee := vaultSupplyFunction isMint) hargs
      (by cases isMint <;> rfl) (by cases isMint <;> rfl) hbody, hrev⟩

end Benchmarks.CurveVault
