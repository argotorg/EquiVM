import Benchmarks.Safe.OwnerValidation
import Benchmarks.Safe.OwnerStorage
import Benchmarks.Safe.Blocks.Runtime_014

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

def canAddOwnerArgs (key : UInt256) : Store :=
  (∅ : Store).insert "owner" (.address (AccountAddress.ofNat key.toNat))

def canAddOwnerFrame (key : UInt256) : Frame :=
  { contract := contract, locals := canAddOwnerArgs key }

def canRemoveOwnerArgs (prev key : UInt256) : Store :=
  ((∅ : Store).insert "owner" (.address (AccountAddress.ofNat key.toNat))).insert
    "prevOwner" (.address (AccountAddress.ofNat prev.toNat))

def canRemoveOwnerFrame (prev key : UInt256) : Frame :=
  { contract := contract, locals := canRemoveOwnerArgs prev key }

theorem safeEvalCanAddOwner (evm : EVM.State) (key : UInt256) :
    evalExpr? config (canAddOwnerFrame key) evm (.var "owner") =
      .ok (.address (AccountAddress.ofNat key.toNat)) := by
  simp [canAddOwnerFrame, canAddOwnerArgs, evalExpr?, EvalResult.ofOption]

theorem safeCanAddOwnerEmpty (evm : EVM.State) (key : UInt256)
    (hc : key.toNat < EVM.addressModulus) :
    evalExpr? config (canAddOwnerFrame key) evm
      (eqE (.storage (ownersRef (.var "owner"))) zeroAddr) =
      .ok (.bool (decide (ownerLink evm key = ⟨0⟩))) :=
  evalAddressZero (solcAddrMask_result_canonical _)
    (safeEvalOwnerLink evm _ _ key (by simp [canAddOwnerArgs]) hc (safeEvalCanAddOwner evm key))

theorem safeCanAddOwnerSource (evm : EVM.State) (key : UInt256)
    (hc : key.toNat < EVM.addressModulus) (hv : validOwner evm.accountMap evm.executionEnv key)
    (he : ownerLink evm key = ⟨0⟩) :
    ExecFuncBody config (canAddOwnerFrame key) evm requireCanAddOwnerFunction.body
      (.returned (canAddOwnerFrame key) evm none) :=
  .execBlockOK (.consNormal (.requireTrue (by
      simpa only [hv, decide_true] using
        safeEvalValidOwner evm _ _ key hc (safeEvalCanAddOwner evm key)))
    (.consNormal (.requireTrue (by
      simpa only [he, decide_true] using
        safeCanAddOwnerEmpty evm key hc)) .nil))

theorem safeCanAddOwnerSourceInvalid (evm : EVM.State) (key : UInt256)
    (hc : key.toNat < EVM.addressModulus) (hv : ¬validOwner evm.accountMap evm.executionEnv key) :
    ExecFuncBody config (canAddOwnerFrame key) evm requireCanAddOwnerFunction.body .reverted :=
  .execBlockRevert (.consRevert (.requireFalse (by
    simpa only [hv, decide_false] using
      safeEvalValidOwner evm _ _ key hc (safeEvalCanAddOwner evm key))))

theorem safeCanAddOwnerSourceExisting (evm : EVM.State) (key : UInt256)
    (hc : key.toNat < EVM.addressModulus) (hv : validOwner evm.accountMap evm.executionEnv key)
    (he : ownerLink evm key ≠ ⟨0⟩) :
    ExecFuncBody config (canAddOwnerFrame key) evm requireCanAddOwnerFunction.body .reverted :=
  .execBlockRevert (.consNormal (.requireTrue (by
      simpa only [hv, decide_true] using
        safeEvalValidOwner evm _ _ key hc (safeEvalCanAddOwner evm key)))
    (.consRevert (.requireFalse (by
      simpa only [he, decide_false] using
        safeCanAddOwnerEmpty evm key hc))))

theorem safeEvalCanRemoveOwner (evm : EVM.State) (prev key : UInt256) :
    evalExpr? config (canRemoveOwnerFrame prev key) evm (.var "owner") =
      .ok (.address (AccountAddress.ofNat key.toNat)) := by
  simp [canRemoveOwnerFrame, canRemoveOwnerArgs, evalExpr?, EvalResult.ofOption,
    Std.HashMap.getElem_insert]

theorem safeEvalCanRemovePrevOwner (evm : EVM.State) (prev key : UInt256) :
    evalExpr? config (canRemoveOwnerFrame prev key) evm (.var "prevOwner") =
      .ok (.address (AccountAddress.ofNat prev.toNat)) := by
  simp [canRemoveOwnerFrame, canRemoveOwnerArgs, evalExpr?, EvalResult.ofOption,
    Std.HashMap.getElem_insert]

theorem safeCanRemoveOwnerLinked (evm : EVM.State) (prev key : UInt256)
    (hp : prev.toNat < EVM.addressModulus) (hc : key.toNat < EVM.addressModulus) :
    evalExpr? config (canRemoveOwnerFrame prev key) evm
      (eqE (.storage (ownersRef (.var "prevOwner"))) (.var "owner")) =
      .ok (.bool (decide (ownerLink evm prev = key))) :=
  evalAddressEq (solcAddrMask_result_canonical _) hc
    (safeEvalOwnerLink evm _ _ prev (by simp [canRemoveOwnerArgs, Std.HashMap.getElem_insert]) hp
      (safeEvalCanRemovePrevOwner evm prev key)) (safeEvalCanRemoveOwner evm prev key)

theorem safeCanRemoveOwnerSource (evm : EVM.State) (prev key : UInt256)
    (hp : prev.toNat < EVM.addressModulus) (hc : key.toNat < EVM.addressModulus)
    (hv : validOwner evm.accountMap evm.executionEnv key) (hl : ownerLink evm prev = key) :
    ExecFuncBody config (canRemoveOwnerFrame prev key) evm requireCanRemoveOwnerFunction.body
      (.returned (canRemoveOwnerFrame prev key) evm none) :=
  .execBlockOK (.consNormal (.requireTrue (by
      simpa only [hv, decide_true] using
        safeEvalValidOwner evm _ _ key hc (safeEvalCanRemoveOwner evm prev key)))
    (.consNormal (.requireTrue (by
      simpa only [hl, decide_true] using
        safeCanRemoveOwnerLinked evm prev key hp hc)) .nil))

theorem safeCanRemoveOwnerSourceInvalid (evm : EVM.State) (prev key : UInt256)
    (hc : key.toNat < EVM.addressModulus) (hv : ¬validOwner evm.accountMap evm.executionEnv key) :
    ExecFuncBody config (canRemoveOwnerFrame prev key) evm requireCanRemoveOwnerFunction.body
      .reverted :=
  .execBlockRevert (.consRevert (.requireFalse (by
    simpa only [hv, decide_false] using
      safeEvalValidOwner evm _ _ key hc (safeEvalCanRemoveOwner evm prev key))))

theorem safeCanRemoveOwnerSourceUnlinked (evm : EVM.State) (prev key : UInt256)
    (hp : prev.toNat < EVM.addressModulus) (hc : key.toNat < EVM.addressModulus)
    (hv : validOwner evm.accountMap evm.executionEnv key) (hl : ownerLink evm prev ≠ key) :
    ExecFuncBody config (canRemoveOwnerFrame prev key) evm requireCanRemoveOwnerFunction.body
      .reverted :=
  .execBlockRevert (.consNormal (.requireTrue (by
      simpa only [hv, decide_true] using
        safeEvalValidOwner evm _ _ key hc (safeEvalCanRemoveOwner evm prev key)))
    (.consRevert (.requireFalse (by
      simpa only [hl, decide_false] using
        safeCanRemoveOwnerLinked evm prev key hp hc))))

end Benchmarks.Safe
