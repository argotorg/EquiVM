import Benchmarks.Midnight.Create2Attempt

variable {fork : Ethereum.Fork}

/-! Couple zero-value CREATE2 with source creation, including rejected creations. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def create2Charged (s : State) (size : UInt256) : State :=
  {s with
    machineState.gasAvailable := (s.machineState.gasAvailable.subNat
      (memoryExpansionCost s .CREATE2)).subNat
      (GasConstants.Gcreate + GasConstants.Gkeccak256word * ((size.toNat + 31) / 32) +
        Ethereum.EVM.R size.toNat)
    machineState.execLength := s.machineState.execLength + 1}

def create2AfterAttempt (s : State) (offset size : UInt256) (R : List UInt256)
    (result : AccountAddress × State × UInt256 × Bool × ByteArray) :
    Except ExecutionException (State × Option (HaltCause × ByteArray)) :=
  let (addr, mid, gas, z, out) := result
  let initCode := s.machineState.memory.readWithPadding offset.toNat size.toNat
  let balance := s.accountMap.get? s.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)
  let x := if z = false ∨ s.executionEnv.depth.val = 1024 ∨
      (⟨0⟩ : UInt256) > balance ∨ initCode.size > 49152 then ⟨0⟩ else UInt256.ofNat addr.val
  if s.machineState.gasAvailable.toNat + gas.toNat < L s.machineState.gasAvailable.toNat then
    .error .OutOfGass
  else .ok ({mid with
    machineState.stack := x :: R
    machineState.activeWords := UInt256.ofNat
      (MachineState.M s.machineState.activeWords.toNat offset.toNat size.toNat)
    machineState.returnData := if z then ByteArray.empty else out
    machineState.gasAvailable := s.machineState.gasAvailable.subNat
      (L s.machineState.gasAvailable.toNat - gas.toNat)
    machineState.pc := s.machineState.pc + ⟨1⟩
    executionEnv := s.executionEnv}, none)

-- LIBRARY CANDIDATE: creation coupling for an arbitrary constructor and initialization code.
theorem zeroValueCreate2Step {cfg : Config} {name : Ident} {args : List Value}
    {s evm : State} {offset size salt : UInt256} {R : List UInt256}
    (hs : SourceState s s.executionEnv s.accountMap evm)
    (hd : decode s.executionEnv.code s.machineState.pc = some (.CREATE2, .none))
    (hstk : s.machineState.stack = ⟨0⟩ :: offset :: size :: salt :: R)
    (hperm : s.executionEnv.perm = true)
    (hcode : cfg.creationCode name args =
      some (s.machineState.memory.readWithPadding offset.toNat size.toNat))
    (hov : R.length + 1 ≤ 1024) :
    Xstep fork (D_J s.executionEnv.code 0) s = .error .OutOfGass ∨
    ∃ (addr : AccountAddress) (evm' : State) (z : Bool) (s' : State),
      newViaEVM fork cfg evm name 0 args (some (Ethereum.UInt256.toByteArray salt))
        (addr, evm', z) ∧
      Xstep fork (D_J s.executionEnv.code 0) s = .ok (s', none) ∧
      s'.executionEnv = s.executionEnv ∧ s'.σ₀ = s.σ₀ ∧
      s'.machineState.pc = s.machineState.pc + ⟨1⟩ ∧
      s'.machineState.stack = (if z then UInt256.ofNat addr.val else ⟨0⟩) :: R ∧
      s'.machineState.memory = s.machineState.memory ∧
      SourceState s s.executionEnv s'.accountMap evm' := by
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
  have hnoOverflow : ¬ R.length + 1 + 1 + 1 + 1 - 4 + 1 > 1024 := by omega
  simp only [hnoOverflow, hperm, not_true_eq_false, if_false] at st
  split at st
  · exact Or.inl st
  split at st
  · exact Or.inl st
  split at st
  · exact Or.inl st
  obtain ⟨addr, mid, gas, z, out, evm', ha, hnew, hworld, hmem, hs', hallowed⟩ :=
    zeroCreate2Attempt_source (s := charged) salt ⟨hs.world, hs.env, hs.accounts⟩ hcode
  rw [ha] at st
  unfold create2AfterAttempt at st
  have hx : (if z = false ∨ charged.executionEnv.depth.val = 1024 ∨
      (⟨0⟩ : UInt256) > (charged.accountMap.get? charged.executionEnv.codeOwner |>.option ⟨0⟩
        (·.balance)) ∨ (charged.machineState.memory.readWithPadding
          offset.toNat size.toNat).size > 49152 then ⟨0⟩ else UInt256.ofNat addr.val) =
      (if z then UInt256.ofNat addr.val else ⟨0⟩) := by
    cases z with
    | false => simp only [true_or, if_true, Bool.false_eq_true, if_false]
    | true =>
      obtain ⟨hd', hz'⟩ := hallowed rfl
      have hdn : charged.executionEnv.depth.val ≠ 1024 := fun h ↦ hd' (Fin.ext h)
      have hgt : ¬ (⟨0⟩ : UInt256) > (charged.accountMap.get? charged.executionEnv.codeOwner
          |>.option ⟨0⟩ (·.balance)) := Fin.not_lt_zero _
      have hsz : ¬ (charged.machineState.memory.readWithPadding
          offset.toNat size.toNat).size > 49152 := Nat.not_lt.mpr hz'
      simp only [Bool.true_eq_false, hdn, hgt, hsz,
        or_self, if_false, if_true]
  dsimp only at st
  rw [hx] at st
  split at st
  · exact Or.inl st
  exact Or.inr ⟨addr, evm', z, _, hnew, st, rfl, hworld, rfl, rfl, hmem,
    ⟨hs'.world, hs'.env, hs'.accounts⟩⟩

end Benchmarks.Midnight
