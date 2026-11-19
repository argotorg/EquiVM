import Stele.Interp

/-! Regression checks for the fork-parametric, pure-Lean EVMLean dependency. -/

open Ethereum Ethereum.EVM Stele.Interp

namespace Tests.EVMLean

-- Missing PUSH bytes are low-order zero bytes, including a wholly missing operand.
#guard decode ⟨#[0x61, 0xab]⟩ ⟨0⟩ = some (.Push .PUSH2, some (⟨0xab00⟩, 2))
#guard decode ⟨#[0x7f]⟩ ⟨0⟩ = some (.Push .PUSH32, some (⟨0⟩, 32))
#guard decode ⟨#[0x61, 0xab, 0xcd]⟩ ⟨0⟩ = some (.Push .PUSH2, some (⟨0xabcd⟩, 2))

private def caller : AccountAddress := 0x1000
private def target : AccountAddress := 0x2000
private def delegate : AccountAddress := 0x3000
private def return42 : ByteArray := ⟨#[0x60, 0x2a, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3]⟩

private def accounts : AccountMap :=
  (default : AccountMap).insert caller default
    |>.insert target { (default : Account) with code := delegationDesignation delegate }
    |>.insert delegate { (default : Account) with code := return42 }

private def state (fork : Fork) : EVM.State :=
  { (default : EVM.State) with
    accountMap := accounts
    σ₀ := accounts
    executionEnv :=
      { (default : ExecutionEnv) with
        fork := fork
        codeOwner := caller
        source := caller
        sender := caller
        perm := true } }

private def delegatedCall (fork : Fork) : CallResult :=
  thetaCall ⟨100000⟩ default
    { kind := .call, target, value := 0, calldata := .empty, calleePerm := true } (state fork)

-- Stele's oracle must execute the callee using the caller's fork.
#guard !(delegatedCall .cancun).success
#guard (delegatedCall .prague).success
#guard (delegatedCall .prague).output = (⟨42⟩ : UInt256).toByteArray
#guard (delegatedCall .osaka).success
#guard (delegatedCall .osaka).output = (⟨42⟩ : UInt256).toByteArray

private def depthLimitedCall (fork : Fork) : Bool :=
  let evm := { state fork with executionEnv.depth := 1024 }
  match callViaEVMRun (thetaOracle ⟨100000⟩) () evm target 0 .empty true with
  | .ok ((false, evm', _), _) => evm'.substate.accessedAccounts.contains delegate
  | _ => false

-- Prague also warms the delegation target when the depth limit prevents the call.
#guard !depthLimitedCall .cancun
#guard depthLimitedCall .prague

private def depthLimitedDelegateCall (fork : Fork) : Bool :=
  let evm := { state fork with executionEnv.depth := 1024 }
  match delegateCallViaEVMRun (thetaOracle ⟨100000⟩) () evm target .empty with
  | .ok ((false, evm', _), _) => evm'.substate.accessedAccounts.contains delegate
  | _ => false

#guard !depthLimitedDelegateCall .cancun
#guard depthLimitedDelegateCall .prague

-- CLZ is available from Osaka. Creation must pass the caller's fork to the initcode.
private def createWithClz (fork : Fork) : CreateResult :=
  lambdaCreate ⟨100000⟩ default
    { value := 0, initCode := ⟨#[0x5f, 0x1e, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3]⟩,
      salt := none } (state fork)

#guard !(createWithClz .cancun).success
#guard !(createWithClz .prague).success
#guard (createWithClz .osaka).success
#guard (createWithClz .bpo4).success
#guard ((createWithClz .osaka).accounts.get? (createWithClz .osaka).address |>.getD default).code =
  (⟨256⟩ : UInt256).toByteArray

end Tests.EVMLean
