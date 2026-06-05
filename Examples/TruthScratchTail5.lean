import Examples.TruthScratchTail4

set_option maxRecDepth 100000

namespace Act
namespace Examples
namespace Truth

def truthParamSuccessState80 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState79 s with
    machineState.gasAvailable :=
      (truthParamSuccessState79 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gjumpdest
    machineState.pc := (truthParamSuccessState79 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState79 s).machineState.execLength + 1 }

def truthParamSuccessState81 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState80 s with
    machineState.stack := (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamSuccessFreeMemPtr s ::
      (⟨1⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
      truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState80 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState80 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState80 s).machineState.execLength + 1 }

def truthParamSuccessState82 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState81 s with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: truthParamSuccessFreeMemPtr s ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
      truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState81 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState81 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState81 s).machineState.execLength + 1 }

def truthParamSuccessState83 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState82 s with
    machineState.stack := truthParamSuccessFreeMemPtr s :: (⟨0x3b⟩ : Ethereum.UInt256) ::
      truthParamSuccessAbiEnd s :: truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState82 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := (truthParamSuccessState82 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState82 s).machineState.execLength + 1 }

def truthParamSuccessState84 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState83 s with
    machineState.stack := (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
      truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState83 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := (truthParamSuccessState83 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState83 s).machineState.execLength + 1 }

def truthParamSuccessState85 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState84 s with
    machineState.stack := truthParamSuccessAbiEnd s :: truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState84 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gmid
    machineState.pc := (⟨0x3b⟩ : Ethereum.UInt256)
    machineState.execLength := (truthParamSuccessState84 s).machineState.execLength + 1 }

theorem truthParamSuccessState80_code (s : EVM.State) :
    (truthParamSuccessState80 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState80, truthParamSuccessState79_code]

theorem truthParamSuccessState81_code (s : EVM.State) :
    (truthParamSuccessState81 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState81, truthParamSuccessState80_code]

theorem truthParamSuccessState82_code (s : EVM.State) :
    (truthParamSuccessState82 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState82, truthParamSuccessState81_code]

theorem truthParamSuccessState83_code (s : EVM.State) :
    (truthParamSuccessState83 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState83, truthParamSuccessState82_code]

theorem truthParamSuccessState84_code (s : EVM.State) :
    (truthParamSuccessState84 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState84, truthParamSuccessState83_code]

theorem truthParamSuccessState85_code (s : EVM.State) :
    (truthParamSuccessState85 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState85, truthParamSuccessState84_code]

theorem truth_success_tail_xstep_pc117_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState79 s).executionEnv.code
        (truthParamSuccessState79 s).machineState.pc = some (.JUMPDEST, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState79 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState79 s) =
      if (truthParamSuccessState79 s).machineState.gasAvailable.toNat <
            GasConstants.Gjumpdest then .error .OutOfGass
      else .ok (truthParamSuccessState80 s, .none) := by
  rw [Ethereum.EVM.step_jumpdest (truthParamSuccessState79 s)]
  · have hoverflow :
        ¬ ((truthParamSuccessState79 s).machineState.stack.length - 0 + 0 > 1024) := by
      simp [truthParamSuccessState79]
    rw [if_neg hoverflow]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc118_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState80 s).executionEnv.code
        (truthParamSuccessState80 s).machineState.pc = some (.SWAP3, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState80 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState80 s) =
      if (truthParamSuccessState80 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState81 s, .none) := by
  rw [Ethereum.EVM.step_swap3 (truthParamSuccessState80 s)]
  · have hstack :
        (truthParamSuccessState80 s).machineState.stack =
          truthParamSuccessAbiEnd s :: truthParamSuccessFreeMemPtr s ::
            (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) ::
            truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState80, truthParamSuccessState79]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc119_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState81 s).executionEnv.code
        (truthParamSuccessState81 s).machineState.pc = some (.SWAP2, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState81 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState81 s) =
      if (truthParamSuccessState81 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState82 s, .none) := by
  rw [Ethereum.EVM.step_swap2 (truthParamSuccessState81 s)]
  · have hstack :
        (truthParamSuccessState81 s).machineState.stack =
          (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamSuccessFreeMemPtr s ::
            (⟨1⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
            truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState81]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc120_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState82 s).executionEnv.code
        (truthParamSuccessState82 s).machineState.pc = some (.POP, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState82 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState82 s) =
      if (truthParamSuccessState82 s).machineState.gasAvailable.toNat <
            GasConstants.Gbase then .error .OutOfGass
      else .ok (truthParamSuccessState83 s, .none) := by
  rw [Ethereum.EVM.step_pop (truthParamSuccessState82 s)]
  · have hstack :
        (truthParamSuccessState82 s).machineState.stack =
          (⟨1⟩ : Ethereum.UInt256) :: truthParamSuccessFreeMemPtr s ::
            (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
            truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState82]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc121_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState83 s).executionEnv.code
        (truthParamSuccessState83 s).machineState.pc = some (.POP, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState83 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState83 s) =
      if (truthParamSuccessState83 s).machineState.gasAvailable.toNat <
            GasConstants.Gbase then .error .OutOfGass
      else .ok (truthParamSuccessState84 s, .none) := by
  rw [Ethereum.EVM.step_pop (truthParamSuccessState83 s)]
  · have hstack :
        (truthParamSuccessState83 s).machineState.stack =
          truthParamSuccessFreeMemPtr s :: (⟨0x3b⟩ : Ethereum.UInt256) ::
            truthParamSuccessAbiEnd s :: truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState83]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc122_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState84 s).executionEnv.code
        (truthParamSuccessState84 s).machineState.pc = some (.JUMP, .none))
    (hcontains :
      (Ethereum.EVM.D_J (truthParamSuccessState84 s).executionEnv.code ⟨0⟩).contains
        (⟨0x3b⟩ : Ethereum.UInt256) = true) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState84 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState84 s) =
      if (truthParamSuccessState84 s).machineState.gasAvailable.toNat <
            GasConstants.Gmid then .error .OutOfGass
      else .ok (truthParamSuccessState85 s, .none) := by
  rw [Ethereum.EVM.step_jump (truthParamSuccessState84 s)]
  · have hstack :
        (truthParamSuccessState84 s).machineState.stack =
          (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
            truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState84, truthParamSuccessState83]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte, Bool.not_eq_true]
    rw [hcontains]
    rfl
  · exact hdecode

theorem truth_success_tail_X_pc117_to_pc122_of_xsteps
    (s : EVM.State)
    (f : Nat)
    (validJumps : Array Ethereum.UInt256)
    (xres : Except Ethereum.EVM.ExecutionException (Ethereum.ExecutionResult EVM.State))
    (h117 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState79 s) =
        .ok (truthParamSuccessState80 s, .none))
    (h118 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState80 s) =
        .ok (truthParamSuccessState81 s, .none))
    (h119 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState81 s) =
        .ok (truthParamSuccessState82 s, .none))
    (h120 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState82 s) =
        .ok (truthParamSuccessState83 s, .none))
    (h121 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState83 s) =
        .ok (truthParamSuccessState84 s, .none))
    (h122 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState84 s) =
        .ok (truthParamSuccessState85 s, .none))
    (htail :
      Ethereum.EVM.X f validJumps (truthParamSuccessState85 s) = xres) :
    Ethereum.EVM.X (f + 6) validJumps (truthParamSuccessState79 s) = xres := by
  have hf :
      f + 6 = ((((((f + 1) + 1) + 1) + 1) + 1) + 1) := by
    omega
  rw [hf]
  truth_continue_step h117
  truth_continue_step h118
  truth_continue_step h119
  truth_continue_step h120
  truth_continue_step h121
  truth_continue_step h122
  exact htail

theorem truth_success_tail_X_pc117_to_pc122_of_gas_guards
    (s : EVM.State)
    (f : Nat)
    (xres : Except Ethereum.EVM.ExecutionException (Ethereum.ExecutionResult EVM.State))
    (h_code : s.executionEnv.code = truthRuntimeBytecode)
    (hgas117 :
      ¬ (truthParamSuccessState79 s).machineState.gasAvailable.toNat <
          GasConstants.Gjumpdest)
    (hgas118 :
      ¬ (truthParamSuccessState80 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas119 :
      ¬ (truthParamSuccessState81 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas120 :
      ¬ (truthParamSuccessState82 s).machineState.gasAvailable.toNat <
          GasConstants.Gbase)
    (hgas121 :
      ¬ (truthParamSuccessState83 s).machineState.gasAvailable.toNat <
          GasConstants.Gbase)
    (hgas122 :
      ¬ (truthParamSuccessState84 s).machineState.gasAvailable.toNat <
          GasConstants.Gmid)
    (htail :
      Ethereum.EVM.X f (Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩)
        (truthParamSuccessState85 s) = xres) :
    Ethereum.EVM.X (f + 6) (Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩)
        (truthParamSuccessState79 s) = xres := by
  apply truth_success_tail_X_pc117_to_pc122_of_xsteps
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState79 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState79_code]]
    rw [truth_success_tail_xstep_pc117_core]
    · rw [if_neg hgas117]
    · rw [truthParamSuccessState79_code, h_code]
      exact truth_decode_pc117
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState80 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState80_code]]
    rw [truth_success_tail_xstep_pc118_core]
    · rw [if_neg hgas118]
    · rw [truthParamSuccessState80_code, h_code]
      exact truth_decode_pc118
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState81 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState81_code]]
    rw [truth_success_tail_xstep_pc119_core]
    · rw [if_neg hgas119]
    · rw [truthParamSuccessState81_code, h_code]
      exact truth_decode_pc119
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState82 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState82_code]]
    rw [truth_success_tail_xstep_pc120_core]
    · rw [if_neg hgas120]
    · rw [truthParamSuccessState82_code, h_code]
      exact truth_decode_pc120
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState83 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState83_code]]
    rw [truth_success_tail_xstep_pc121_core]
    · rw [if_neg hgas121]
    · rw [truthParamSuccessState83_code, h_code]
      exact truth_decode_pc121
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState84 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState84_code]]
    rw [truth_success_tail_xstep_pc122_core]
    · rw [if_neg hgas122]
    · rw [truthParamSuccessState84_code, h_code]
      exact truth_decode_pc122
    · rw [truthParamSuccessState84_code, h_code]
      exact truth_valid_jumpdest_3b
  · exact htail

end Truth
end Examples
end Act
