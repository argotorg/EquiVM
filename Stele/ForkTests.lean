import Stele.Interp

/-! The interpreter's call and create oracles run the callee under the caller's fork. -/

open Ethereum Ethereum.EVM Stele.Interp

namespace Stele.ForkTests

private def caller : AccountAddress := 0x1000
private def target : AccountAddress := 0x2000
private def delegate : AccountAddress := 0x3000
private def return42 : ByteArray := ⟨#[0x60, 0x2a, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3]⟩

private def accounts : AccountMap :=
  (default : AccountMap).insert caller default
    |>.insert target { (default : Account) with code := delegationDesignation delegate }
    |>.insert delegate { (default : Account) with code := return42 }

private def state : EVM.State :=
  { (default : EVM.State) with
    accountMap := accounts
    σ₀ := accounts
    executionEnv :=
      { (default : ExecutionEnv) with
        codeOwner := caller
        source := caller
        sender := caller
        perm := true } }

private def delegatedCall (fork : Fork) : CallResult :=
  thetaCall fork ⟨100000⟩ default
    { kind := .call, target, value := 0, calldata := .empty, calleePerm := true } state

-- Stele's oracle must execute the callee using the caller's fork.
#guard !(delegatedCall .cancun).success
#guard (delegatedCall .prague).success
#guard (delegatedCall .prague).output = (⟨42⟩ : UInt256).toByteArray
#guard (delegatedCall .osaka).success
#guard (delegatedCall .osaka).output = (⟨42⟩ : UInt256).toByteArray

private def depthLimitedCall (fork : Fork) : Bool :=
  let evm := { state with executionEnv.depth := 1024 }
  match callViaEVMRun fork (thetaOracle fork ⟨100000⟩) () evm target 0 .empty true with
  | .ok ((false, evm', _), _) => evm'.substate.accessedAccounts.contains delegate
  | _ => false

-- Prague also warms the delegation target when the depth limit prevents the call.
#guard !depthLimitedCall .cancun
#guard depthLimitedCall .prague

private def depthLimitedDelegateCall (fork : Fork) : Bool :=
  let evm := { state with executionEnv.depth := 1024 }
  match delegateCallViaEVMRun fork (thetaOracle fork ⟨100000⟩) () evm target .empty with
  | .ok ((false, evm', _), _) => evm'.substate.accessedAccounts.contains delegate
  | _ => false

#guard !depthLimitedDelegateCall .cancun
#guard depthLimitedDelegateCall .prague

-- CLZ is available from Osaka. Creation must pass the caller's fork to the initcode.
private def createWithClz (fork : Fork) : CreateResult :=
  lambdaCreate fork ⟨100000⟩ default
    { value := 0, initCode := ⟨#[0x5f, 0x1e, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3]⟩,
      salt := none } state

#guard !(createWithClz .cancun).success
#guard !(createWithClz .prague).success
#guard (createWithClz .osaka).success
#guard (createWithClz .bpo4).success
#guard ((createWithClz .osaka).accounts.get? (createWithClz .osaka).address |>.getD default).code =
  (⟨256⟩ : UInt256).toByteArray

end Stele.ForkTests
