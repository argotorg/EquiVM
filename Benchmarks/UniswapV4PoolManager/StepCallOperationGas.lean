import Benchmarks.UniswapV4PoolManager.RecursiveOperationGas

open Ethereum Ethereum.EVM Reasoning.Theory
namespace Benchmarks.UniswapV4PoolManager

-- GENERALIZES the CALL cases of step_gas_decreases_of_cost_eq_C' to retain 100 gas.
theorem step_call_gas_100 {gasCost : Nat} {arg : Option (UInt256 × Nat)} {s s' : State}
    (hle : gasCost ≤ s.machineState.gasAvailable.toNat)
    (hcost : gasCost = C' s .CALL)
    (h : step gasCost (.CALL, arg) s = .ok s') :
    s'.machineState.gasAvailable.toNat+100 ≤ s.machineState.gasAvailable.toNat := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat (first | simp at h | split at h)
  rename_i _ vPop hPop _ vCall hCall
  rcases vCall with ⟨xCall, stateCall⟩
  let sExec : State := { s with
    machineState.execLength := s.machineState.execLength + 1 }
  have hPop' : s.machineState.stack.pop7 = some vPop := by
    exact option_liftM_eq_some hPop
  have hidx := Stack.pop7_get! hPop'
  rcases hidx with ⟨h0, h1, h2⟩
  have hnet :
      Ccallgas (AccountAddress.ofUInt256 vPop.2.2.1)
        (AccountAddress.ofUInt256 vPop.2.2.1) vPop.2.2.2.1 vPop.2.1
        sExec.accountMap sExec.machineState sExec.substate+100 ≤ gasCost := by
    have hbase :
        Ccallgas (AccountAddress.ofUInt256 vPop.2.2.1)
          (AccountAddress.ofUInt256 vPop.2.2.1) vPop.2.2.2.1 vPop.2.1
          s.accountMap s.machineState s.substate+100 ≤
        Ccall (AccountAddress.ofUInt256 vPop.2.2.1)
          (AccountAddress.ofUInt256 vPop.2.2.1) vPop.2.2.2.1 vPop.2.1
          s.accountMap s.machineState s.substate :=
      Ccallgas_add_100_le _ _ _ _ _ _ _
    rw [hcost]
    simpa [sExec, C', Ccallgas, Cgascap, h0, h1, h2] using hbase
  have hdec := call_gas_minimum
    (s := sExec)
    (x := xCall)
    (s' := stateCall)
    (hpaid := by simpa [sExec] using hle)
    (hnet := hnet)
    (h := by simpa [sExec] using hCall)
  rw [← h]
  simpa [sExec] using hdec

theorem step_callcode_gas_100 {gasCost : Nat} {arg : Option (UInt256 × Nat)} {s s' : State}
    (hle : gasCost ≤ s.machineState.gasAvailable.toNat)
    (hcost : gasCost = C' s .CALLCODE)
    (h : step gasCost (.CALLCODE, arg) s = .ok s') :
    s'.machineState.gasAvailable.toNat+100 ≤ s.machineState.gasAvailable.toNat := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat (first | simp at h | split at h)
  rename_i _ vPop hPop _ vCall hCall
  rcases vCall with ⟨xCall, stateCall⟩
  let sExec : State := { s with
    machineState.execLength := s.machineState.execLength + 1 }
  have hPop' : s.machineState.stack.pop7 = some vPop := by
    exact option_liftM_eq_some hPop
  have hidx := Stack.pop7_get! hPop'
  rcases hidx with ⟨h0, h1, h2⟩
  have hnet :
      Ccallgas (AccountAddress.ofUInt256 vPop.2.2.1)
        (AccountAddress.ofUInt256 (UInt256.ofNat s.executionEnv.codeOwner.val))
        vPop.2.2.2.1 vPop.2.1
        sExec.accountMap sExec.machineState sExec.substate+100 ≤ gasCost := by
    have hbase :
        Ccallgas (AccountAddress.ofUInt256 vPop.2.2.1)
          s.executionEnv.codeOwner vPop.2.2.2.1 vPop.2.1
          s.accountMap s.machineState s.substate+100 ≤
        Ccall (AccountAddress.ofUInt256 vPop.2.2.1)
          s.executionEnv.codeOwner vPop.2.2.2.1 vPop.2.1
          s.accountMap s.machineState s.substate :=
      Ccallgas_add_100_le _ _ _ _ _ _ _
    rw [hcost]
    simpa [sExec, C', Ccallgas, Cgascap, h0, h1, h2,
      AccountAddress.ofUInt256_ofNat] using hbase
  have hdec := call_gas_minimum
    (s := sExec)
    (x := xCall)
    (s' := stateCall)
    (hpaid := by simpa [sExec] using hle)
    (hnet := hnet)
    (h := by simpa [sExec] using hCall)
  rw [← h]
  simpa [sExec] using hdec

theorem step_delegatecall_gas_100 {gasCost : Nat} {arg : Option (UInt256 × Nat)} {s s' : State}
    (hle : gasCost ≤ s.machineState.gasAvailable.toNat)
    (hcost : gasCost = C' s .DELEGATECALL)
    (h : step gasCost (.DELEGATECALL, arg) s = .ok s') :
    s'.machineState.gasAvailable.toNat+100 ≤ s.machineState.gasAvailable.toNat := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat (first | simp at h | split at h)
  rename_i _ vPop hPop _ vCall hCall
  rcases vCall with ⟨xCall, stateCall⟩
  let sExec : State := { s with
    machineState.execLength := s.machineState.execLength + 1 }
  have hPop' : s.machineState.stack.pop6 = some vPop := by
    exact option_liftM_eq_some hPop
  have hidx := Stack.pop6_get! hPop'
  rcases hidx with ⟨h0, h1⟩
  have hnet :
      Ccallgas (AccountAddress.ofUInt256 vPop.2.2.1)
        (AccountAddress.ofUInt256 (UInt256.ofNat s.executionEnv.codeOwner.val))
        (⟨0⟩ : UInt256) vPop.2.1
        sExec.accountMap sExec.machineState sExec.substate+100 ≤ gasCost := by
    have hbase :
        Ccallgas (AccountAddress.ofUInt256 vPop.2.2.1)
          s.executionEnv.codeOwner (⟨0⟩ : UInt256) vPop.2.1
          s.accountMap s.machineState s.substate+100 ≤
        Ccall (AccountAddress.ofUInt256 vPop.2.2.1)
          s.executionEnv.codeOwner (⟨0⟩ : UInt256) vPop.2.1
          s.accountMap s.machineState s.substate :=
      Ccallgas_add_100_le _ _ _ _ _ _ _
    rw [hcost]
    simpa [sExec, C', Ccallgas, Cgascap, h0, h1,
      AccountAddress.ofUInt256_ofNat] using hbase
  have hdec := call_gas_minimum
    (s := sExec)
    (x := xCall)
    (s' := stateCall)
    (hpaid := by simpa [sExec] using hle)
    (hnet := hnet)
    (h := by simpa [sExec] using hCall)
  rw [← h]
  simpa [sExec] using hdec

theorem step_staticcall_gas_100 {gasCost : Nat} {arg : Option (UInt256 × Nat)} {s s' : State}
    (hle : gasCost ≤ s.machineState.gasAvailable.toNat)
    (hcost : gasCost = C' s .STATICCALL)
    (h : step gasCost (.STATICCALL, arg) s = .ok s') :
    s'.machineState.gasAvailable.toNat+100 ≤ s.machineState.gasAvailable.toNat := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat (first | simp at h | split at h)
  rename_i _ vPop hPop _ vCall hCall
  rcases vCall with ⟨xCall, stateCall⟩
  let sExec : State := { s with
    machineState.execLength := s.machineState.execLength + 1 }
  have hPop' : s.machineState.stack.pop6 = some vPop := by
    exact option_liftM_eq_some hPop
  have hidx := Stack.pop6_get! hPop'
  rcases hidx with ⟨h0, h1⟩
  have hnet :
      Ccallgas (AccountAddress.ofUInt256 vPop.2.2.1)
        (AccountAddress.ofUInt256 vPop.2.2.1)
        (⟨0⟩ : UInt256) vPop.2.1
        sExec.accountMap sExec.machineState sExec.substate+100 ≤ gasCost := by
    have hbase :
        Ccallgas (AccountAddress.ofUInt256 vPop.2.2.1)
          (AccountAddress.ofUInt256 vPop.2.2.1) (⟨0⟩ : UInt256) vPop.2.1
          s.accountMap s.machineState s.substate+100 ≤
        Ccall (AccountAddress.ofUInt256 vPop.2.2.1)
          (AccountAddress.ofUInt256 vPop.2.2.1) (⟨0⟩ : UInt256) vPop.2.1
          s.accountMap s.machineState s.substate :=
      Ccallgas_add_100_le _ _ _ _ _ _ _
    rw [hcost]
    simpa [sExec, C', Ccallgas, Cgascap, h0, h1] using hbase
  have hdec := call_gas_minimum
    (s := sExec)
    (x := xCall)
    (s' := stateCall)
    (hpaid := by simpa [sExec] using hle)
    (hnet := hnet)
    (h := by simpa [sExec] using hCall)
  rw [← h]
  simpa [sExec] using hdec

end Benchmarks.UniswapV4PoolManager
