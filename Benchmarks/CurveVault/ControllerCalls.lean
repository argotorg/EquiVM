import Benchmarks.CurveVault.Storage
import Benchmarks.CurveVault.StaticWordCalls

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

def vaultControllerCall (controllerLocal resultLocal callName : Ident) : List Stmt :=
  [.letDecl controllerLocal (some (.elem .address))
    (.cast (.storage {base := "_controller", steps := []}) (.elem .address)),
   .externalCall (.var controllerLocal) callName (.intLit 0) [] resultLocal (perm := false)]

def vaultControllerCallLocals (locals : Store) (evm : EVM.State) (controllerLocal resultLocal : Ident)
    (value : Value) : Store :=
  (locals.insert controllerLocal (.address (AccountAddress.ofUInt256
    (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)))).insert resultLocal value

theorem vaultControllerRead (evm : EVM.State) (locals : Store) (hbase : locals.get? "_controller" = none) :
    evalExpr? config {contract := contract, locals := locals} evm
      (.cast (.storage {base := "_controller", steps := []}) (.elem .address)) =
      .ok (.address (AccountAddress.ofUInt256 (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩))) := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  exact vaultControllerEval evm locals hbase

theorem vaultControllerCallSuccess {evm evm' : EVM.State} {locals : Store} {value : Value}
    {controllerLocal resultLocal callName : Ident} {out : ByteArray}
    (hbase : locals.get? "_controller" = none)
    (hcall : typedCallViaEVM fork config evm
      (AccountAddress.ofUInt256 (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩))
      callName 0 [] (true, evm', out) false)
    (hdecode : config.externalABI.decode? callName out = some [value]) :
    ExecBlock fork config {contract := contract, locals := locals} evm
      (vaultControllerCall controllerLocal resultLocal callName)
      (.ok {contract := contract, locals := vaultControllerCallLocals locals evm controllerLocal resultLocal value} evm') := by
  apply ExecBlock.consNormal (ExecStmt.letDecl (vaultControllerRead evm locals hbase))
  apply ExecBlock.consNormal (ExecStmt.externalCallSuccess (fork := fork) (hperm := Or.inl rfl) (target := AccountAddress.ofUInt256 (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩))
    (sendVal := 0) (argVals := []) (value := [value])
    (by simp [evalExpr?, EvalResult.ofOption])
    (by simp [evalExpr?, pure]) (by simp [evalExprs?, pure])
    (by simpa only [address_of_val] using hcall) hdecode)
  exact ExecBlock.nil

theorem vaultControllerCallFailure {evm evm' : EVM.State} {locals : Store}
    {controllerLocal resultLocal callName : Ident} {out : ByteArray}
    (hbase : locals.get? "_controller" = none)
    (hcall : typedCallViaEVM fork config evm
      (AccountAddress.ofUInt256 (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩))
      callName 0 [] (false, evm', out) false) :
    ExecBlock fork config {contract := contract, locals := locals} evm
      (vaultControllerCall controllerLocal resultLocal callName) .reverted := by
  apply ExecBlock.consNormal (ExecStmt.letDecl (vaultControllerRead evm locals hbase))
  exact ExecBlock.consRevert (ExecStmt.externalCallFailure (fork := fork) (hperm := Or.inl rfl) (target := AccountAddress.ofUInt256 (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩))
    (sendVal := 0) (argVals := [])
    (by simp [evalExpr?, EvalResult.ofOption])
    (by simp [evalExpr?, pure]) (by simp [evalExprs?, pure])
    (by simpa only [address_of_val] using hcall))

theorem vaultControllerCallDecodeFailure {evm evm' : EVM.State} {locals : Store}
    {controllerLocal resultLocal callName : Ident} {out : ByteArray}
    (hbase : locals.get? "_controller" = none)
    (hcall : typedCallViaEVM fork config evm
      (AccountAddress.ofUInt256 (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩))
      callName 0 [] (true, evm', out) false)
    (hdecode : config.externalABI.decode? callName out = none) :
    ExecBlock fork config {contract := contract, locals := locals} evm
      (vaultControllerCall controllerLocal resultLocal callName) .reverted := by
  apply ExecBlock.consNormal (ExecStmt.letDecl (vaultControllerRead evm locals hbase))
  exact ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert (fork := fork) (hperm := Or.inl rfl) (target := AccountAddress.ofUInt256 (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩))
    (sendVal := 0) (argVals := [])
    (by simp [evalExpr?, EvalResult.ofOption])
    (by simp [evalExpr?, pure]) (by simp [evalExprs?, pure])
    (by simpa only [address_of_val] using hcall) hdecode)

def vaultControllerCallOutcome (fork : Ethereum.Fork) (s0 evm : State) (I : ExecutionEnv) (g : Sat256)
    (locals : Store) (controllerLocal resultLocal callName : Ident) (next : UInt256)
    (R : List UInt256) (mem : ByteArray) (outOffset : UInt256) : Prop :=
  (∃ (evm' : State) (σ' : AccountMap) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      32 ≤ out.size ∧ out.size < UInt256.size ∧
      ExecBlock fork config {contract := contract, locals := locals} evm
        (vaultControllerCall controllerLocal resultLocal callName)
        (.ok {contract := contract, locals := vaultControllerCallLocals locals evm controllerLocal resultLocal (.int (Int.ofNat (retWord out).toNat))} evm') ∧
      SourceState s0 I σ' evm' ∧
      RD fork vaultBytecode I g s0 next R
        ((retWord out).toByteArray.write 0 mem outOffset.toNat 32) aw' out σ' k' C') ∨
    (ExecBlock fork config {contract := contract, locals := locals} evm
      (vaultControllerCall controllerLocal resultLocal callName) .reverted ∧ RDrev fork vaultBytecode g s0)

theorem vaultControllerWordCall {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {pc next gasArg inOffset outOffset : UInt256} {R : List UInt256}
    {locals : Store} {controllerLocal resultLocal callName : Ident}
    (hs : SourceState s0 I σ evm) (hbase : locals.get? "_controller" = none)
    (hstack : R.length + 1 ≤ 1024)
    (hpc : decode vaultBytecode pc = some (.STATICCALL, .none))
    (hcd : config.externalABI.encode? callName [] = some (mem.readWithPadding inOffset.toNat 4))
    (hbuffer : outOffset.toNat + 32 ≤ mem.size)
    (hdecode : ∀ out, 32 ≤ out.size → config.externalABI.decode? callName out =
      some [.int (Int.ofNat (retWord out).toNat)])
    (hdecodeShort : ∀ out, out.size < 32 → config.externalABI.decode? callName out = none)
    (hpass : ∀ {mem' aw' out σ' k' C'}, 32 ≤ out.size → out.size < UInt256.size →
      RD fork vaultBytecode I g s0 (pc + ⟨1⟩) (⟨1⟩ :: R) mem' aw' out σ' k' C' →
      ∃ k'' C'', RD fork vaultBytecode I g s0 next R mem' aw' out σ' k'' C'')
    (hfail : ∀ {mem' aw' out σ' k' C'},
      RD fork vaultBytecode I g s0 (pc + ⟨1⟩) (⟨0⟩ :: R) mem' aw' out σ' k' C' → RDrev fork vaultBytecode g s0)
    (hshort : ∀ {mem' aw' out σ' k' C'}, out.size < 32 →
      RD fork vaultBytecode I g s0 (pc + ⟨1⟩) (⟨1⟩ :: R) mem' aw' out σ' k' C' → RDrev fork vaultBytecode g s0)
    (h : RD fork vaultBytecode I g s0 pc
      (gasArg :: codeOwnerStorageWord I σ ⟨3⟩ :: inOffset :: ⟨4⟩ :: outOffset :: ⟨32⟩ :: R)
      mem aw rdata σ k C) :
    vaultControllerCallOutcome fork s0 evm I g locals controllerLocal resultLocal callName next R mem outOffset := by
  have hread : Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩ =
      codeOwnerStorageWord I σ ⟨3⟩ := hs.storageRead _
  rcases staticWordCallBridge (nextStack := fun _ => R) hs hstack hpc hcd hbuffer hpass hfail hshort h with
    ⟨evm', σ', out, aw', k', C', h32, hout, hcall, hs', rdNext⟩ |
    ⟨evm', out, hcall, hrev⟩ | ⟨evm', out, hcall, hlt, hrev⟩
  · rw [← hread] at hcall
    exact Or.inl ⟨evm', σ', out, aw', k', C', h32, hout,
      vaultControllerCallSuccess hbase hcall (hdecode out h32), hs', rdNext⟩
  · rw [← hread] at hcall
    exact Or.inr ⟨vaultControllerCallFailure hbase hcall, hrev⟩
  · rw [← hread] at hcall
    exact Or.inr ⟨vaultControllerCallDecodeFailure hbase hcall (hdecodeShort out hlt), hrev⟩

end Benchmarks.CurveVault
