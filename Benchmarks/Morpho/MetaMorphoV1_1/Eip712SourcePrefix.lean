import Benchmarks.Morpho.MetaMorphoV1_1.Eip712StringMemory

/-! Source frames and the ordered string/allocation prefix of `eip712Domain`. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000
set_option autoImplicit false

def eip712NameEnd (evm : State) (v : MetaMorphoV1_1Immutables) : Nat :=
  domainStringEnd evm v false 128

def eip712VersionEnd (evm : State) (v : MetaMorphoV1_1Immutables) : Nat :=
  domainStringEnd evm v true (eip712NameEnd evm v)

def eip712InitialLocals (evm : State) : Store :=
  let locals := (∅ : Store).insert "__calldata" (.bytes evm.executionEnv.calldata)
  let locals := locals.insert "fields" (.fixedBytes 0 [0])
  let locals := locals.insert "name" (.bytes ByteArray.empty)
  let locals := locals.insert "version" (.bytes ByteArray.empty)
  let locals := locals.insert "chainId" (.int 0)
  let locals := locals.insert "verifyingContract" (.address (AccountAddress.ofNat 0))
  let locals := locals.insert "salt" (.fixedBytes 31 (List.replicate 32 0))
  locals.insert "extensions" (.array [])

def eip712NameLocals (evm : State) (v : MetaMorphoV1_1Immutables) : Store :=
  (eip712InitialLocals evm).insert "__c0" (.bytes (domainStringBytes v false evm))

def eip712NameAllocatedLocals (evm : State) (v : MetaMorphoV1_1Immutables) : Store :=
  (eip712NameLocals evm v).insert "__solcNameEnd"
    (uint256Value (UInt256.ofNat (eip712NameEnd evm v)))

def eip712VersionLocals (evm : State) (v : MetaMorphoV1_1Immutables) : Store :=
  (eip712NameAllocatedLocals evm v).insert "__c1" (.bytes (domainStringBytes v true evm))

def eip712VersionAllocatedLocals (evm : State) (v : MetaMorphoV1_1Immutables) : Store :=
  (eip712VersionLocals evm v).insert "__solcVersionEnd"
    (uint256Value (UInt256.ofNat (eip712VersionEnd evm v)))

theorem eip712InitialPrefix (evm : State) (v : MetaMorphoV1_1Immutables)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ABlock config evm (domainFrame v ∅) eip712DomainTransition.body
      (domainFrame v (eip712InitialLocals evm)) (eip712DomainTransition.body.drop 10) := by
  refine (((((((nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).letStep
    ?_).letStep ?_).letStep ?_).letStep ?_).letStep ?_).letStep ?_).letStep ?_
  all_goals simp only [evalExpr?, defaultValue?, pure, bind, EvalResult.bind] <;> rfl

theorem eip712NamePrefix (evm : State) (v : MetaMorphoV1_1Immutables)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hvalid : domainStringValid v false evm) :
    ABlock config evm (domainFrame v ∅) eip712DomainTransition.body
      (domainFrame v (eip712NameLocals evm v)) (eip712DomainTransition.body.drop 11) := by
  refine ⟨fun h ↦ (eip712InitialPrefix evm v hwv hhi).run ?_⟩
  exact ExecBlock.consNormal (domainStringCallReturns evm v false _ "__c0" hvalid) h

theorem eip712NameAllocation (evm : State) (v : MetaMorphoV1_1Immutables)
    (hfit : eip712NameEnd evm v < 2 ^ 64) :
    ExecStmt config (domainFrame v (eip712NameLocals evm v)) evm
      (domainStringAllocation false (.intLit 128) "__c0" "__solcNameEnd")
      (.ok (domainFrame v (eip712NameAllocatedLocals evm v)) evm) := by
  have hs : (domainStringBytes v false evm).size + 32 < UInt256.size := by
    have := domainStringBytes_bound evm v false
    change _ < 2 ^ 256
    omega
  have h := domainStringAllocationReturns evm v false (eip712NameLocals evm v)
    (.intLit 128) (UInt256.ofNat 128) "__c0" "__solcNameEnd" _
    (by simp only [evalExpr?, pure]; rfl) (store_get_self _ _ _) hs
    ((domainStringAllocationFits evm v false 128 (by decide)).mpr hfit)
  simpa only [domainStringNextCursor, eip712NameAllocatedLocals, eip712NameEnd] using h

theorem eip712NameAllocatedPrefix (evm : State) (v : MetaMorphoV1_1Immutables)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hvalid : domainStringValid v false evm) (hfit : eip712NameEnd evm v < 2 ^ 64) :
    ABlock config evm (domainFrame v ∅) eip712DomainTransition.body
      (domainFrame v (eip712NameAllocatedLocals evm v)) (eip712DomainTransition.body.drop 12) := by
  refine ⟨fun h ↦ (eip712NamePrefix evm v hwv hhi hvalid).run ?_⟩
  exact ExecBlock.consNormal (eip712NameAllocation evm v hfit) h

theorem eip712VersionPrefix (evm : State) (v : MetaMorphoV1_1Immutables)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hname : domainStringValid v false evm) (hnameFit : eip712NameEnd evm v < 2 ^ 64)
    (hvalid : domainStringValid v true evm) :
    ABlock config evm (domainFrame v ∅) eip712DomainTransition.body
      (domainFrame v (eip712VersionLocals evm v)) (eip712DomainTransition.body.drop 13) := by
  refine ⟨fun h ↦ (eip712NameAllocatedPrefix evm v hwv hhi hname hnameFit).run ?_⟩
  exact ExecBlock.consNormal (domainStringCallReturns evm v true _ "__c1" hvalid) h

theorem eip712VersionCursor (evm : State) (v : MetaMorphoV1_1Immutables) :
    evalExpr? config (domainFrame v (eip712VersionLocals evm v)) evm (.var "__solcNameEnd") =
      .ok (uint256Value (UInt256.ofNat (eip712NameEnd evm v))) := by
  simp only [evalExpr?, domainFrame, eip712VersionLocals, eip712NameAllocatedLocals,
    store_get_ne _ _ (by decide : ("__c1" == "__solcNameEnd") = false), store_get_self,
    EvalResult.ofOption]

theorem eip712VersionAllocation (evm : State) (v : MetaMorphoV1_1Immutables)
    (hnameFit : eip712NameEnd evm v < 2 ^ 64) (hfit : eip712VersionEnd evm v < 2 ^ 64) :
    ExecStmt config (domainFrame v (eip712VersionLocals evm v)) evm
      (domainStringAllocation true (.var "__solcNameEnd") "__c1" "__solcVersionEnd")
      (.ok (domainFrame v (eip712VersionAllocatedLocals evm v)) evm) := by
  have hs : (domainStringBytes v true evm).size + 32 < UInt256.size := by
    have := domainStringBytes_bound evm v true
    change _ < 2 ^ 256
    omega
  have h := domainStringAllocationReturns evm v true (eip712VersionLocals evm v)
    (.var "__solcNameEnd") (UInt256.ofNat (eip712NameEnd evm v)) "__c1" "__solcVersionEnd" _
    (eip712VersionCursor evm v) (store_get_self _ _ _) hs
    ((domainStringAllocationFits evm v true (eip712NameEnd evm v) hnameFit).mpr hfit)
  simpa only [domainStringNextCursor, eip712VersionAllocatedLocals, eip712VersionEnd] using h

theorem eip712VersionAllocatedPrefix (evm : State) (v : MetaMorphoV1_1Immutables)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hname : domainStringValid v false evm) (hnameFit : eip712NameEnd evm v < 2 ^ 64)
    (hversion : domainStringValid v true evm) (hversionFit : eip712VersionEnd evm v < 2 ^ 64) :
    ABlock config evm (domainFrame v ∅) eip712DomainTransition.body
      (domainFrame v (eip712VersionAllocatedLocals evm v))
      (eip712DomainTransition.body.drop 14) := by
  refine ⟨fun h ↦ (eip712VersionPrefix evm v hwv hhi hname hnameFit hversion).run ?_⟩
  exact ExecBlock.consNormal (eip712VersionAllocation evm v hnameFit hversionFit) h

end Benchmarks.Morpho.MetaMorphoV1_1
