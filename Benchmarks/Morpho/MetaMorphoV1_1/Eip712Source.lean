import Benchmarks.Morpho.MetaMorphoV1_1.Eip712SourcePrefix

/-! Success and revert outcomes for the complete `eip712Domain` source body. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000
set_option autoImplicit false

def eip712ReturnValues (evm : State) (v : MetaMorphoV1_1Immutables) : List Value :=
  [.fixedBytes 0 [15], .bytes (domainStringBytes v false evm),
   .bytes (domainStringBytes v true evm), .int (Int.ofNat Ethereum.chainId),
   .address evm.executionEnv.codeOwner, .fixedBytes 31 (List.replicate 32 0), .array []]

def eip712FinalLocals (evm : State) (v : MetaMorphoV1_1Immutables) : Store :=
  (eip712VersionAllocatedLocals evm v).insert "__solcExtensionsEnd"
    (uint256Value (nextCursor (UInt256.ofNat (eip712VersionEnd evm v)) ⟨32⟩))

theorem eip712ExtensionsAllocationFits (evm : State) (v : MetaMorphoV1_1Immutables)
    (hversionFit : eip712VersionEnd evm v < 2 ^ 64) :
    allocationFits (UInt256.ofNat (eip712VersionEnd evm v)) ⟨32⟩ ↔
      eip712VersionEnd evm v + 32 < 2 ^ 64 := by
  rw [allocationFits_iff_sum_lt,
    UInt256.toNat_ofNat_of_lt (lt_trans hversionFit (by decide))]
  rfl

theorem eip712ExtensionsCursor (evm : State) (v : MetaMorphoV1_1Immutables) :
    evalExpr? config (domainFrame v (eip712VersionAllocatedLocals evm v)) evm
      (.var "__solcVersionEnd") = .ok (uint256Value (UInt256.ofNat (eip712VersionEnd evm v))) := by
  simp only [evalExpr?, domainFrame, eip712VersionAllocatedLocals, store_get_self,
    EvalResult.ofOption]

theorem eip712BodyReturns (evm : State) (v : MetaMorphoV1_1Immutables)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hname : domainStringValid v false evm) (hnameFit : eip712NameEnd evm v < 2 ^ 64)
    (hversion : domainStringValid v true evm) (hversionFit : eip712VersionEnd evm v < 2 ^ 64)
    (hextensionsFit : eip712VersionEnd evm v + 32 < 2 ^ 64) :
    ExecTransitionBody config contract evm ∅ eip712DomainTransition.body
      (.returned (domainFrame v (eip712FinalLocals evm v)) evm (some (eip712ReturnValues evm v)))
      (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply (eip712VersionAllocatedPrefix evm v hwv hhi hname hnameFit hversion hversionFit).run
  apply ExecBlock.consNormal (allocateCallReturns "__solcExtensionsEnd" rfl
    (eip712ExtensionsCursor evm v) (by simp only [evalExpr?, pure]; rfl)
    ((eip712ExtensionsAllocationFits evm v hversionFit).mpr hextensionsFit))
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp [evalExprs?, evalExpr?, defaultValue?, domainFrame, Std.HashMap.getElem_insert,
    eip712VersionAllocatedLocals, eip712VersionLocals, eip712NameAllocatedLocals, eip712NameLocals,
    eip712ReturnValues, envValue, EvalResult.ofOption, pure, bind, EvalResult.bind]

theorem eip712RevertsName (evm : State) (v : MetaMorphoV1_1Immutables)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hbad : ¬ domainStringValid v false evm) :
    ExecTransitionBody config contract evm ∅ eip712DomainTransition.body .reverted (immStore v) :=
    by
  apply ExecFuncBody.execBlockRevert
  apply (eip712InitialPrefix evm v hwv hhi).run
  exact ExecBlock.consRevert (domainStringCallReverts evm v false _ "__c0" hbad)

theorem eip712RevertsNameAllocation (evm : State) (v : MetaMorphoV1_1Immutables)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hname : domainStringValid v false evm) (hbad : ¬ eip712NameEnd evm v < 2 ^ 64) :
    ExecTransitionBody config contract evm ∅ eip712DomainTransition.body .reverted (immStore v) :=
    by
  apply ExecFuncBody.execBlockRevert
  apply (eip712NamePrefix evm v hwv hhi hname).run
  apply ExecBlock.consRevert
  exact domainStringAllocationReverts evm v false _ (.intLit 128) (UInt256.ofNat 128)
    "__c0" "__solcNameEnd" _ (by simp only [evalExpr?, pure]; rfl) (store_get_self _ _ _)
    (by have := domainStringBytes_bound evm v false; change _ < 2 ^ 256; omega)
    (fun hfit ↦ hbad ((domainStringAllocationFits evm v false 128 (by decide)).mp hfit))

theorem eip712RevertsVersion (evm : State) (v : MetaMorphoV1_1Immutables)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hname : domainStringValid v false evm) (hnameFit : eip712NameEnd evm v < 2 ^ 64)
    (hbad : ¬ domainStringValid v true evm) :
    ExecTransitionBody config contract evm ∅ eip712DomainTransition.body .reverted (immStore v) :=
    by
  apply ExecFuncBody.execBlockRevert
  apply (eip712NameAllocatedPrefix evm v hwv hhi hname hnameFit).run
  exact ExecBlock.consRevert (domainStringCallReverts evm v true _ "__c1" hbad)

theorem eip712RevertsVersionAllocation (evm : State) (v : MetaMorphoV1_1Immutables)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hname : domainStringValid v false evm) (hnameFit : eip712NameEnd evm v < 2 ^ 64)
    (hversion : domainStringValid v true evm) (hbad : ¬ eip712VersionEnd evm v < 2 ^ 64) :
    ExecTransitionBody config contract evm ∅ eip712DomainTransition.body .reverted (immStore v) :=
    by
  apply ExecFuncBody.execBlockRevert
  apply (eip712VersionPrefix evm v hwv hhi hname hnameFit hversion).run
  apply ExecBlock.consRevert
  exact domainStringAllocationReverts evm v true _ (.var "__solcNameEnd")
    (UInt256.ofNat (eip712NameEnd evm v)) "__c1" "__solcVersionEnd" _
    (eip712VersionCursor evm v) (store_get_self _ _ _)
    (by have := domainStringBytes_bound evm v true; change _ < 2 ^ 256; omega)
    (fun hfit ↦ hbad
      ((domainStringAllocationFits evm v true (eip712NameEnd evm v) hnameFit).mp hfit))

theorem eip712RevertsExtensions (evm : State) (v : MetaMorphoV1_1Immutables)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hname : domainStringValid v false evm) (hnameFit : eip712NameEnd evm v < 2 ^ 64)
    (hversion : domainStringValid v true evm) (hversionFit : eip712VersionEnd evm v < 2 ^ 64)
    (hbad : ¬ eip712VersionEnd evm v + 32 < 2 ^ 64) :
    ExecTransitionBody config contract evm ∅ eip712DomainTransition.body .reverted (immStore v) :=
    by
  apply ExecFuncBody.execBlockRevert
  apply (eip712VersionAllocatedPrefix evm v hwv hhi hname hnameFit hversion hversionFit).run
  exact ExecBlock.consRevert (allocateCallReverts "__solcExtensionsEnd" rfl
    (eip712ExtensionsCursor evm v) (by simp only [evalExpr?, pure]; rfl)
    (fun hfit ↦ hbad ((eip712ExtensionsAllocationFits evm v hversionFit).mp hfit)))

end Benchmarks.Morpho.MetaMorphoV1_1
