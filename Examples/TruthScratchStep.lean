import Examples.TruthScratch

set_option maxRecDepth 100000

namespace Act
namespace Examples
namespace Truth

theorem truth_success_xstep_pc48_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState35 s).executionEnv.code
        (truthParamSuccessState35 s).machineState.pc = some (.JUMPDEST, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState35 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState35 s) =
      if (truthParamSuccessState35 s).machineState.gasAvailable.toNat <
            GasConstants.Gjumpdest then .error .OutOfGass
      else .ok (truthParamSuccessState36 s, .none) := by
  rw [Ethereum.EVM.step_jumpdest (truthParamSuccessState35 s)]
  · have hoverflow :
        ¬ ((truthParamSuccessState35 s).machineState.stack.length - 0 + 0 > 1024) := by
      simp [truthParamSuccessState35, truthParamSuccessState34]
    rw [if_neg hoverflow]
    simp [truthParamSuccessState36, truthParamSuccessState35]
  · exact hdecode

theorem truth_success_xstep_pc49_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState36 s).executionEnv.code
        (truthParamSuccessState36 s).machineState.pc =
          some (.PUSH1, .some ((⟨0x40⟩ : Ethereum.UInt256), 1))) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState36 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState36 s) =
      if (truthParamSuccessState36 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState37 s, .none) := by
  rw [Ethereum.EVM.step_push1 (truthParamSuccessState36 s) (⟨0x40⟩ : Ethereum.UInt256)]
  · have hoverflow :
        ¬ ((truthParamSuccessState36 s).machineState.stack.length - 0 + 1 > 1024) := by
      simp [truthParamSuccessState36, truthParamSuccessState35, truthParamSuccessState34]
    rw [if_neg hoverflow]
    simp [truthParamSuccessState37, truthParamSuccessState36]
  · exact hdecode

theorem truth_success_xstep_pc51_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState37 s).executionEnv.code
        (truthParamSuccessState37 s).machineState.pc = some (.MLOAD, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState37 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState37 s) =
      if (truthParamSuccessState37 s).machineState.gasAvailable.toNat <
            Ethereum.EVM.memoryExpansionCost (truthParamSuccessState37 s) .MLOAD
      then .error .OutOfGass
      else
        if ((truthParamSuccessState37 s).machineState.gasAvailable -
              Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost
                (truthParamSuccessState37 s) .MLOAD)).toNat <
              GasConstants.Gverylow then .error .OutOfGass
        else .ok (truthParamSuccessState38 s, .none) := by
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
    simp [truthParamSuccessState38, truthParamSuccessFreeMemPtr, truthParamSuccessState37]
  · exact hdecode

theorem truth_success_xstep_pc52_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState38 s).executionEnv.code
        (truthParamSuccessState38 s).machineState.pc =
          some (.PUSH1, .some ((⟨0x3b⟩ : Ethereum.UInt256), 1))) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState38 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState38 s) =
      if (truthParamSuccessState38 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState39 s, .none) := by
  rw [Ethereum.EVM.step_push1 (truthParamSuccessState38 s) (⟨0x3b⟩ : Ethereum.UInt256)]
  · have hoverflow :
        ¬ ((truthParamSuccessState38 s).machineState.stack.length - 0 + 1 > 1024) := by
      simp [truthParamSuccessState38]
    rw [if_neg hoverflow]
    rfl
  · exact hdecode

/-
This fresh-state wrapper is logically just `truth_success_xstep_pc52_core`
specialized to `truthFreshState`, but the expanded theorem type currently
triggers kernel deep recursion. Keep the compact core theorem as the checked
artifact while developing the rest of the path.

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
  apply truth_success_xstep_pc52_core
  rw [truthParamSuccessState38_code]
  simp [s, truthFreshState, h_code]
  exact truth_decode_pc52
-/

theorem truth_success_xstep_pc54_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState39 s).executionEnv.code
        (truthParamSuccessState39 s).machineState.pc = some (.SWAP2, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState39 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState39 s) =
      if (truthParamSuccessState39 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState40 s, .none) := by
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
  · exact hdecode

theorem truth_success_xstep_pc55_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState40 s).executionEnv.code
        (truthParamSuccessState40 s).machineState.pc = some (.SWAP1, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState40 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState40 s) =
      if (truthParamSuccessState40 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState41 s, .none) := by
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
  · exact hdecode

theorem truth_success_xstep_pc56_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState41 s).executionEnv.code
        (truthParamSuccessState41 s).machineState.pc =
          some (.PUSH1, .some ((⟨0x64⟩ : Ethereum.UInt256), 1))) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState41 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState41 s) =
      if (truthParamSuccessState41 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState42 s, .none) := by
  rw [Ethereum.EVM.step_push1 (truthParamSuccessState41 s) (⟨0x64⟩ : Ethereum.UInt256)]
  · have hoverflow :
        ¬ ((truthParamSuccessState41 s).machineState.stack.length - 0 + 1 > 1024) := by
      simp [truthParamSuccessState41]
    rw [if_neg hoverflow]
    rfl
  · exact hdecode

theorem truth_success_xstep_pc58_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState42 s).executionEnv.code
        (truthParamSuccessState42 s).machineState.pc = some (.JUMP, .none))
    (hcontains :
      (Ethereum.EVM.D_J (truthParamSuccessState42 s).executionEnv.code ⟨0⟩).contains
        (⟨0x64⟩ : Ethereum.UInt256) = true) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState42 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState42 s) =
      if (truthParamSuccessState42 s).machineState.gasAvailable.toNat <
            GasConstants.Gmid then .error .OutOfGass
      else .ok (truthParamSuccessState43 s, .none) := by
  rw [Ethereum.EVM.step_jump (truthParamSuccessState42 s)]
  · have hstack :
        (truthParamSuccessState42 s).machineState.stack =
          (⟨0x64⟩ : Ethereum.UInt256) :: truthParamSuccessFreeMemPtr s ::
            (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) ::
              truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState42, truthParamSuccessState41]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte, Bool.not_eq_true]
    rw [hcontains]
    rfl
  · exact hdecode

theorem truth_success_X_pc48_to_pc58_of_xsteps
    (s : EVM.State)
    (f : Nat)
    (validJumps : Array Ethereum.UInt256)
    (xres : Except Ethereum.EVM.ExecutionException (Ethereum.ExecutionResult EVM.State))
    (h48 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState35 s) =
        .ok (truthParamSuccessState36 s, .none))
    (h49 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState36 s) =
        .ok (truthParamSuccessState37 s, .none))
    (h51 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState37 s) =
        .ok (truthParamSuccessState38 s, .none))
    (h52 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState38 s) =
        .ok (truthParamSuccessState39 s, .none))
    (h54 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState39 s) =
        .ok (truthParamSuccessState40 s, .none))
    (h55 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState40 s) =
        .ok (truthParamSuccessState41 s, .none))
    (h56 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState41 s) =
        .ok (truthParamSuccessState42 s, .none))
    (h58 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState42 s) =
        .ok (truthParamSuccessState43 s, .none))
    (htail :
      Ethereum.EVM.X f validJumps (truthParamSuccessState43 s) = xres) :
    Ethereum.EVM.X (f + 8) validJumps (truthParamSuccessState35 s) = xres := by
  have hf :
      f + 8 = ((((((((f + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) := by
    omega
  rw [hf]
  truth_continue_step h48
  truth_continue_step h49
  truth_continue_step h51
  truth_continue_step h52
  truth_continue_step h54
  truth_continue_step h55
  truth_continue_step h56
  truth_continue_step h58
  exact htail

theorem truth_success_X_pc48_to_pc58_of_gas_guards
    (s : EVM.State)
    (f : Nat)
    (xres : Except Ethereum.EVM.ExecutionException (Ethereum.ExecutionResult EVM.State))
    (h_code : s.executionEnv.code = truthRuntimeBytecode)
    (hgas48 :
      ¬ (truthParamSuccessState35 s).machineState.gasAvailable.toNat <
          GasConstants.Gjumpdest)
    (hgas49 :
      ¬ (truthParamSuccessState36 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas51_mem :
      ¬ (truthParamSuccessState37 s).machineState.gasAvailable.toNat <
          Ethereum.EVM.memoryExpansionCost (truthParamSuccessState37 s) .MLOAD)
    (hgas51_op :
      ¬ ((truthParamSuccessState37 s).machineState.gasAvailable -
            Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost
              (truthParamSuccessState37 s) .MLOAD)).toNat <
          GasConstants.Gverylow)
    (hgas52 :
      ¬ (truthParamSuccessState38 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas54 :
      ¬ (truthParamSuccessState39 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas55 :
      ¬ (truthParamSuccessState40 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas56 :
      ¬ (truthParamSuccessState41 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas58 :
      ¬ (truthParamSuccessState42 s).machineState.gasAvailable.toNat <
          GasConstants.Gmid)
    (htail :
      Ethereum.EVM.X f (Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩)
        (truthParamSuccessState43 s) = xres) :
    Ethereum.EVM.X (f + 8) (Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩)
        (truthParamSuccessState35 s) = xres := by
  apply truth_success_X_pc48_to_pc58_of_xsteps
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState35 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState35_code]]
    rw [truth_success_xstep_pc48_core]
    · rw [if_neg hgas48]
    · rw [truthParamSuccessState35_code, h_code]
      exact truth_decode_pc48
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState36 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState36_code]]
    rw [truth_success_xstep_pc49_core]
    · rw [if_neg hgas49]
    · rw [truthParamSuccessState36_code, h_code]
      exact truth_decode_pc49
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState37 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState37_code]]
    rw [truth_success_xstep_pc51_core]
    · rw [if_neg hgas51_mem, if_neg hgas51_op]
    · rw [truthParamSuccessState37_code, h_code]
      exact truth_decode_pc51
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState38 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState38_code]]
    rw [truth_success_xstep_pc52_core]
    · rw [if_neg hgas52]
    · rw [truthParamSuccessState38_code, h_code]
      exact truth_decode_pc52
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState39 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState39_code]]
    rw [truth_success_xstep_pc54_core]
    · rw [if_neg hgas54]
    · rw [truthParamSuccessState39_code, h_code]
      exact truth_decode_pc54
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState40 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState40_code]]
    rw [truth_success_xstep_pc55_core]
    · rw [if_neg hgas55]
    · rw [truthParamSuccessState40_code, h_code]
      exact truth_decode_pc55
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState41 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState41_code]]
    rw [truth_success_xstep_pc56_core]
    · rw [if_neg hgas56]
    · rw [truthParamSuccessState41_code, h_code]
      exact truth_decode_pc56
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState42 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState42_code]]
    rw [truth_success_xstep_pc58_core]
    · rw [if_neg hgas58]
    · rw [truthParamSuccessState42_code, h_code]
      exact truth_decode_pc58
    · rw [truthParamSuccessState42_code, h_code]
      exact truth_valid_jumpdest_64
  · exact htail

end Truth
end Examples
end Act
