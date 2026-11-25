import Benchmarks.Midnight.Create2Step
import Benchmarks.Midnight.MemoryFunding

variable {fork : Ethereum.Fork}

/-! CREATE2 charges its caller's memory expansion before entering initialization code. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: the parent-memory charge is retained across a continuing CREATE2.
theorem create2MemoryCharge {s s' : State} {offset size salt : UInt256} {R : List UInt256}
    (hd : decode s.executionEnv.code s.machineState.pc = some (.CREATE2, .none))
    (hstk : s.machineState.stack = ⟨0⟩ :: offset :: size :: salt :: R)
    (hstep : Xstep fork (D_J s.executionEnv.code 0) s = .ok (s', none)) :
    s'.machineState.activeWords = M s.machineState.activeWords offset size ∧
      s'.machineState.gasAvailable.toNat + memoryExpansionCost s .CREATE2 ≤
        s.machineState.gasAvailable.toNat := by
  have st := step_create2 (fork := fork) s hd
  rw [hstk] at st
  let charged := create2Charged s size
  let initCode := s.machineState.memory.readWithPadding offset.toNat size.toNat
  change Xstep fork (D_J s.executionEnv.code 0) s =
    if s.machineState.gasAvailable.toNat < memoryExpansionCost s .CREATE2 then .error .OutOfGass
    else if (s.machineState.gasAvailable.subNat (memoryExpansionCost s .CREATE2)).toNat <
        GasConstants.Gcreate + GasConstants.Gkeccak256word * ((size.toNat + 31) / 32) +
          Ethereum.EVM.R size.toNat then .error .OutOfGass
    else if R.length + 1 + 1 + 1 + 1 - 4 + 1 > 1024 then .error .StackOverflow
    else if ¬s.executionEnv.perm = true then .error .StaticModeViolation
    else if size > ⟨49152⟩ then .error .OutOfGass
    else create2AfterAttempt charged offset size R (zeroCreate2Attempt fork charged initCode salt) at st
  rw [st] at hstep
  split at hstep
  · contradiction
  rename_i hmem
  split at hstep
  · contradiction
  split at hstep
  · contradiction
  split at hstep
  · contradiction
  split at hstep
  · contradiction
  obtain ⟨addr, mid, gas, z, out⟩ := zeroCreate2Attempt fork charged initCode salt
  unfold create2AfterAttempt at hstep
  dsimp only at hstep
  split at hstep
  · contradiction
  cases hstep
  refine ⟨rfl, ?_⟩
  simp only [charged, create2Charged, Sat256.subNat_toNat]
  omega

end Benchmarks.Midnight
