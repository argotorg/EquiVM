import Benchmarks.CompoundIII.Comet.InternalOutcome

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def reentrancySlot : UInt256 :=
  UInt256.ofNat 91163063775796598582698250372395185889154745920815755245223157833676084630444

def reentrancyWord (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner reentrancySlot

def reentrancyValue (enter : Bool) : UInt256 := if enter then ⟨1⟩ else ⟨0⟩

def reentrancyState (evm : EVM.State) (enter : Bool) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner reentrancySlot (reentrancyValue enter)

def reentrancyWriteOutcome (evm : EVM.State) (enter : Bool) : InternalOutcome :=
  if evm.executionEnv.perm then .ok (reentrancyState evm enter) else .staticViolation

def reentrancyOutcome (evm : EVM.State) (enter : Bool) : InternalOutcome :=
  if enter && decide ((reentrancyWord evm).toNat = 1) then .reverted
  else reentrancyWriteOutcome evm enter

theorem reentrancyOutcome_perm {evm evm' : EVM.State} {enter : Bool}
    (h : reentrancyOutcome evm enter = .ok evm') : evm.executionEnv.perm = true := by
  cases hp : evm.executionEnv.perm
  · simp only [reentrancyOutcome, reentrancyWriteOutcome, hp, Bool.false_eq_true, if_false] at h
    split_ifs at h <;> cases h
  · rfl

def reentrancyName (enter : Bool) : Ident :=
  if enter then "nonReentrantBefore" else "nonReentrantAfter"

def reentrancyWriteStmt (enter : Bool) : Stmt :=
  .assign .storage ⟨"__reentrancyGuard", []⟩ (.intLit (if enter then 1 else 0))

def reentrancyCallable (enter : Bool) : CallableDecl :=
  { params := [], returnType := [],
    body := if enter then
      [.letDecl "status" (some (.elem (.int (.uint ⟨256, by decide⟩))))
        (.storage ⟨"__reentrancyGuard", []⟩),
       .require (.binary .ne (.var "status") (.intLit 1)), reentrancyWriteStmt true]
    else [reentrancyWriteStmt false] }

theorem reentrancyCallable_lookup (enter : Bool) :
    lookupCallable? contract (reentrancyName enter) = some (reentrancyCallable enter) := by
  cases enter <;> rfl

end Benchmarks.CompoundIII.Comet
