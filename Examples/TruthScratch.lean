import Examples.TruthBase

set_option maxRecDepth 100000

namespace Act
namespace Examples
namespace Truth

def truthParamSuccessState36 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState35 s with
    machineState.gasAvailable :=
      (truthParamSuccessState35 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gjumpdest
    machineState.pc := (truthParamSuccessState35 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState35 s).machineState.execLength + 1 }

def truthParamSuccessState37 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState36 s with
    machineState.stack := (⟨0x40⟩ : Ethereum.UInt256) ::
      (truthParamSuccessState36 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamSuccessState36 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState36 s).machineState.pc +
      Ethereum.UInt256.ofNat 2
    machineState.execLength := (truthParamSuccessState36 s).machineState.execLength + 1 }

@[irreducible] def truthParamSuccessFreeMemPtr (s : EVM.State) : Ethereum.UInt256 :=
  if (⟨0x40⟩ : Ethereum.UInt256).toNat ≥ (truthParamSuccessState37 s).machineState.memory.size ∨
      (⟨0x40⟩ : Ethereum.UInt256) ≥
        (truthParamSuccessState37 s).machineState.activeWords * ⟨32⟩ then
    ⟨0⟩
  else
    Ethereum.UInt256.ofNat
      (Ethereum.fromByteArrayBigEndian
        ((truthParamSuccessState37 s).machineState.memory.readWithPadding
          (⟨0x40⟩ : Ethereum.UInt256).toNat 32))

def truthParamSuccessState38 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState37 s with
    machineState.stack := truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
      truthParamMismatchSelectorWord s :: []
    machineState.activeWords :=
      Ethereum.UInt256.ofNat
        (Ethereum.MachineState.M (truthParamSuccessState37 s).machineState.activeWords.toNat
          (⟨0x40⟩ : Ethereum.UInt256).toNat 32)
    machineState.gasAvailable :=
      ((truthParamSuccessState37 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost
          (truthParamSuccessState37 s) .MLOAD)) -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState37 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState37 s).machineState.execLength + 1 }

@[irreducible] def truthParamSuccessAbiEnd (s : EVM.State) : Ethereum.UInt256 :=
  truthParamSuccessFreeMemPtr s + (⟨0x20⟩ : Ethereum.UInt256)

def truthParamSuccessState39 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState38 s with
    machineState.stack := (⟨0x3b⟩ : Ethereum.UInt256) ::
      (truthParamSuccessState38 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamSuccessState38 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState38 s).machineState.pc +
      Ethereum.UInt256.ofNat 2
    machineState.execLength := (truthParamSuccessState38 s).machineState.execLength + 1 }

def truthParamSuccessState40 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState39 s with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: truthParamSuccessFreeMemPtr s ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState39 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState39 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState39 s).machineState.execLength + 1 }

def truthParamSuccessState41 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState40 s with
    machineState.stack := truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState40 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState40 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState40 s).machineState.execLength + 1 }

def truthParamSuccessState42 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState41 s with
    machineState.stack := (⟨0x64⟩ : Ethereum.UInt256) ::
      (truthParamSuccessState41 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamSuccessState41 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState41 s).machineState.pc +
      Ethereum.UInt256.ofNat 2
    machineState.execLength := (truthParamSuccessState41 s).machineState.execLength + 1 }

def truthParamSuccessState43 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState42 s with
    machineState.stack := truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState42 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gmid
    machineState.pc := (⟨0x64⟩ : Ethereum.UInt256)
    machineState.execLength := (truthParamSuccessState42 s).machineState.execLength + 1 }

theorem truthParamSuccessState36_code (s : EVM.State) :
    (truthParamSuccessState36 s).executionEnv.code = s.executionEnv.code := by
  simp [truthParamSuccessState36, truthParamSuccessState35_code]

theorem truthParamSuccessState37_code (s : EVM.State) :
    (truthParamSuccessState37 s).executionEnv.code = s.executionEnv.code := by
  simp [truthParamSuccessState37, truthParamSuccessState36_code]

theorem truthParamSuccessState38_code (s : EVM.State) :
    (truthParamSuccessState38 s).executionEnv.code = s.executionEnv.code := by
  simp [truthParamSuccessState38, truthParamSuccessState37_code]

theorem truthParamSuccessState39_code (s : EVM.State) :
    (truthParamSuccessState39 s).executionEnv.code = s.executionEnv.code := by
  simp [truthParamSuccessState39, truthParamSuccessState38_code]

theorem truthParamSuccessState40_code (s : EVM.State) :
    (truthParamSuccessState40 s).executionEnv.code = s.executionEnv.code := by
  simp [truthParamSuccessState40, truthParamSuccessState39_code]

theorem truthParamSuccessState41_code (s : EVM.State) :
    (truthParamSuccessState41 s).executionEnv.code = s.executionEnv.code := by
  simp [truthParamSuccessState41, truthParamSuccessState40_code]

theorem truthParamSuccessState42_code (s : EVM.State) :
    (truthParamSuccessState42 s).executionEnv.code = s.executionEnv.code := by
  simp [truthParamSuccessState42, truthParamSuccessState41_code]

theorem truthParamSuccessState43_code (s : EVM.State) :
    (truthParamSuccessState43 s).executionEnv.code = s.executionEnv.code := by
  simp [truthParamSuccessState43, truthParamSuccessState42_code]

theorem truth_fresh_success_xstep_pc48
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamSuccessState35
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamSuccessState35
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gjumpdest then .error .OutOfGass
      else .ok
        (truthParamSuccessState36
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamSuccessState35 s).executionEnv.code ⟨0⟩ := by
    rw [truthParamSuccessState35_code]
    simp [s, truthFreshState]
  rw [hvalid]
  rw [Ethereum.EVM.step_jumpdest (truthParamSuccessState35 s)]
  · have hoverflow :
        ¬ ((truthParamSuccessState35 s).machineState.stack.length - 0 + 0 > 1024) := by
      simp [truthParamSuccessState35, truthParamSuccessState34]
    rw [if_neg hoverflow]
    simp [s, truthParamSuccessState36, truthParamSuccessState35]
  · rw [truthParamSuccessState35_code]
    simp [s, truthFreshState, h_code]
    exact truth_decode_pc48

theorem truth_fresh_success_xstep_pc49
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamSuccessState36
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamSuccessState36
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok
        (truthParamSuccessState37
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamSuccessState36 s).executionEnv.code ⟨0⟩ := by
    rw [truthParamSuccessState36_code]
    simp [s, truthFreshState]
  rw [hvalid]
  rw [Ethereum.EVM.step_push1 (truthParamSuccessState36 s) (⟨0x40⟩ : Ethereum.UInt256)]
  · have hoverflow :
        ¬ ((truthParamSuccessState36 s).machineState.stack.length - 0 + 1 > 1024) := by
      simp [truthParamSuccessState36, truthParamSuccessState35, truthParamSuccessState34]
    rw [if_neg hoverflow]
    simp [s, truthParamSuccessState37, truthParamSuccessState36]
  · rw [truthParamSuccessState36_code]
    simp [s, truthFreshState, h_code]
    exact truth_decode_pc49

theorem truth_fresh_success_xstep_pc51
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamSuccessState37
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamSuccessState37
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            Ethereum.EVM.memoryExpansionCost
              (truthParamSuccessState37
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MLOAD
      then .error .OutOfGass
      else
        if ((truthParamSuccessState37
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
              Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost
                (truthParamSuccessState37
                  (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MLOAD)).toNat <
              GasConstants.Gverylow then .error .OutOfGass
        else .ok
          (truthParamSuccessState38
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamSuccessState37 s).executionEnv.code ⟨0⟩ := by
    rw [truthParamSuccessState37_code]
    simp [s, truthFreshState]
  rw [hvalid]
  rw [Ethereum.EVM.step_mload (truthParamSuccessState37 s)]
  · have hstack :
        (truthParamSuccessState37 s).machineState.stack =
          (⟨0x40⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
            truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState37, truthParamSuccessState36, truthParamSuccessState35,
        truthParamSuccessState34]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte]
    simp [s, truthParamSuccessState38, truthParamSuccessFreeMemPtr, truthParamSuccessState37]
  · rw [truthParamSuccessState37_code]
    simp [s, truthFreshState, h_code]
    exact truth_decode_pc51

/-
WIP: these later return-wrapper steps currently make the kernel expand very
large nested state equalities. Keep the checked prefix importable while working
on a narrower proof shape in a second scratch layer.

theorem truth_fresh_success_xstep_pc52
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamSuccessState38
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamSuccessState38
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok
        (truthParamSuccessState39
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamSuccessState38 s).executionEnv.code ⟨0⟩ := by
    rw [truthParamSuccessState38_code]
    simp [s, truthFreshState]
  rw [hvalid]
  rw [Ethereum.EVM.step_push1 (truthParamSuccessState38 s) (⟨0x3b⟩ : Ethereum.UInt256)]
  · have hoverflow :
        ¬ ((truthParamSuccessState38 s).machineState.stack.length - 0 + 1 > 1024) := by
      simp [truthParamSuccessState38]
    rw [if_neg hoverflow]
    rfl
  · rw [truthParamSuccessState38_code]
    simp [s, truthFreshState, h_code]
    exact truth_decode_pc52

theorem truth_fresh_success_xstep_pc54
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamSuccessState39
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamSuccessState39
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok
        (truthParamSuccessState40
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamSuccessState39 s).executionEnv.code ⟨0⟩ := by
    rw [truthParamSuccessState39_code]
    simp [s, truthFreshState]
  rw [hvalid]
  rw [Ethereum.EVM.step_swap2 (truthParamSuccessState39 s)]
  · have hstack :
        (truthParamSuccessState39 s).machineState.stack =
          (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamSuccessFreeMemPtr s ::
            (⟨1⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState39, truthParamSuccessState38]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte]
    rfl
  · rw [truthParamSuccessState39_code]
    simp [s, truthFreshState, h_code]
    exact truth_decode_pc54

theorem truth_fresh_success_xstep_pc55
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamSuccessState40
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamSuccessState40
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok
        (truthParamSuccessState41
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamSuccessState40 s).executionEnv.code ⟨0⟩ := by
    rw [truthParamSuccessState40_code]
    simp [s, truthFreshState]
  rw [hvalid]
  rw [Ethereum.EVM.step_swap1 (truthParamSuccessState40 s)]
  · have hstack :
        (truthParamSuccessState40 s).machineState.stack =
          (⟨1⟩ : Ethereum.UInt256) :: truthParamSuccessFreeMemPtr s ::
            (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState40]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte]
    rfl
  · rw [truthParamSuccessState40_code]
    simp [s, truthFreshState, h_code]
    exact truth_decode_pc55

theorem truth_fresh_success_xstep_pc56
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamSuccessState41
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamSuccessState41
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok
        (truthParamSuccessState42
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamSuccessState41 s).executionEnv.code ⟨0⟩ := by
    rw [truthParamSuccessState41_code]
    simp [s, truthFreshState]
  rw [hvalid]
  rw [Ethereum.EVM.step_push1 (truthParamSuccessState41 s) (⟨0x64⟩ : Ethereum.UInt256)]
  · have hoverflow :
        ¬ ((truthParamSuccessState41 s).machineState.stack.length - 0 + 1 > 1024) := by
      simp [truthParamSuccessState41]
    rw [if_neg hoverflow]
    rfl
  · rw [truthParamSuccessState41_code]
    simp [s, truthFreshState, h_code]
    exact truth_decode_pc56

set_option maxHeartbeats 2000000 in
theorem truth_fresh_success_xstep_pc58
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamSuccessState42
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamSuccessState42
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gmid then .error .OutOfGass
      else .ok
        (truthParamSuccessState43
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamSuccessState42 s).executionEnv.code ⟨0⟩ := by
    rw [truthParamSuccessState42_code]
    simp [s, truthFreshState]
  rw [hvalid]
  rw [Ethereum.EVM.step_jump (truthParamSuccessState42 s)]
  · simp only [truthParamSuccessState42, truthParamSuccessState41]
    have hcontains :
        (Ethereum.EVM.D_J (truthParamSuccessState40 s).executionEnv.code ⟨0⟩).contains
          (⟨0x64⟩ : Ethereum.UInt256) = true := by
      rw [truthParamSuccessState40_code]
      simp [s, truthFreshState, h_code]
      exact truth_valid_jumpdest_64
    rw [hcontains]
    simp [s, truthParamSuccessState43, truthParamSuccessState42, truthParamSuccessState41,
      truthParamSuccessState40]
	  · rw [truthParamSuccessState42_code]
	    simp [s, truthFreshState, h_code]
	    exact truth_decode_pc58
-/

end Truth
end Examples
end Act
