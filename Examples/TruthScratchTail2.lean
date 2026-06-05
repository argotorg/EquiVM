import Examples.TruthScratchTail

set_option maxRecDepth 100000

namespace Act
namespace Examples
namespace Truth

def truthParamSuccessState58 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState57 s with
    machineState.gasAvailable :=
      (truthParamSuccessState57 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gjumpdest
    machineState.pc := (truthParamSuccessState57 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState57 s).machineState.execLength + 1 }

def truthParamSuccessState59 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState58 s with
    machineState.stack := (⟨0x5e⟩ : Ethereum.UInt256) ::
      (truthParamSuccessState58 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamSuccessState58 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc :=
      (truthParamSuccessState58 s).machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := (truthParamSuccessState58 s).machineState.execLength + 1 }

def truthParamSuccessState60 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState59 s with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: (⟨0x5e⟩ : Ethereum.UInt256) ::
      (⟨1⟩ : Ethereum.UInt256) :: truthParamSuccessFreeMemPtr s ::
      (⟨0x75⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
      truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState59 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState59 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState59 s).machineState.execLength + 1 }

def truthParamSuccessState61 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState60 s with
    machineState.stack := (⟨0x4c⟩ : Ethereum.UInt256) ::
      (truthParamSuccessState60 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamSuccessState60 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc :=
      (truthParamSuccessState60 s).machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := (truthParamSuccessState60 s).machineState.execLength + 1 }

def truthParamSuccessState62 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState61 s with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: (⟨0x5e⟩ : Ethereum.UInt256) ::
      (⟨1⟩ : Ethereum.UInt256) :: truthParamSuccessFreeMemPtr s ::
      (⟨0x75⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
      truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState61 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gmid
    machineState.pc := (⟨0x4c⟩ : Ethereum.UInt256)
    machineState.execLength := (truthParamSuccessState61 s).machineState.execLength + 1 }

theorem truthParamSuccessState58_code (s : EVM.State) :
    (truthParamSuccessState58 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState58, truthParamSuccessState57_code]

theorem truthParamSuccessState59_code (s : EVM.State) :
    (truthParamSuccessState59 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState59, truthParamSuccessState58_code]

theorem truthParamSuccessState60_code (s : EVM.State) :
    (truthParamSuccessState60 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState60, truthParamSuccessState59_code]

theorem truthParamSuccessState61_code (s : EVM.State) :
    (truthParamSuccessState61 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState61, truthParamSuccessState60_code]

theorem truthParamSuccessState62_code (s : EVM.State) :
    (truthParamSuccessState62 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState62, truthParamSuccessState61_code]

theorem truth_success_tail_xstep_pc87_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState57 s).executionEnv.code
        (truthParamSuccessState57 s).machineState.pc = some (.JUMPDEST, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState57 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState57 s) =
      if (truthParamSuccessState57 s).machineState.gasAvailable.toNat <
            GasConstants.Gjumpdest then .error .OutOfGass
      else .ok (truthParamSuccessState58 s, .none) := by
  rw [Ethereum.EVM.step_jumpdest (truthParamSuccessState57 s)]
  · have hoverflow :
        ¬ ((truthParamSuccessState57 s).machineState.stack.length - 0 + 0 > 1024) := by
      simp [truthParamSuccessState57]
    rw [if_neg hoverflow]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc88_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState58 s).executionEnv.code
        (truthParamSuccessState58 s).machineState.pc =
          some (.PUSH1, .some ((⟨0x5e⟩ : Ethereum.UInt256), 1))) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState58 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState58 s) =
      if (truthParamSuccessState58 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState59 s, .none) := by
  rw [Ethereum.EVM.step_push1 (truthParamSuccessState58 s) (⟨0x5e⟩ : Ethereum.UInt256)]
  · have hoverflow :
        ¬ ((truthParamSuccessState58 s).machineState.stack.length - 0 + 1 > 1024) := by
      simp [truthParamSuccessState58, truthParamSuccessState57]
    rw [if_neg hoverflow]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc90_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState59 s).executionEnv.code
        (truthParamSuccessState59 s).machineState.pc = some (.DUP2, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState59 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState59 s) =
      if (truthParamSuccessState59 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState60 s, .none) := by
  rw [Ethereum.EVM.step_dup2 (truthParamSuccessState59 s)]
  · have hstack :
        (truthParamSuccessState59 s).machineState.stack =
          (⟨0x5e⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
            truthParamSuccessFreeMemPtr s :: (⟨0x75⟩ : Ethereum.UInt256) ::
            truthParamSuccessAbiEnd s :: truthParamSuccessFreeMemPtr s ::
            (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) ::
            truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState59, truthParamSuccessState58, truthParamSuccessState57]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc91_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState60 s).executionEnv.code
        (truthParamSuccessState60 s).machineState.pc =
          some (.PUSH1, .some ((⟨0x4c⟩ : Ethereum.UInt256), 1))) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState60 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState60 s) =
      if (truthParamSuccessState60 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState61 s, .none) := by
  rw [Ethereum.EVM.step_push1 (truthParamSuccessState60 s) (⟨0x4c⟩ : Ethereum.UInt256)]
  · have hoverflow :
        ¬ ((truthParamSuccessState60 s).machineState.stack.length - 0 + 1 > 1024) := by
      simp [truthParamSuccessState60]
    rw [if_neg hoverflow]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc93_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState61 s).executionEnv.code
        (truthParamSuccessState61 s).machineState.pc = some (.JUMP, .none))
    (hcontains :
      (Ethereum.EVM.D_J (truthParamSuccessState61 s).executionEnv.code ⟨0⟩).contains
        (⟨0x4c⟩ : Ethereum.UInt256) = true) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState61 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState61 s) =
      if (truthParamSuccessState61 s).machineState.gasAvailable.toNat <
            GasConstants.Gmid then .error .OutOfGass
      else .ok (truthParamSuccessState62 s, .none) := by
  rw [Ethereum.EVM.step_jump (truthParamSuccessState61 s)]
  · have hstack :
        (truthParamSuccessState61 s).machineState.stack =
          (⟨0x4c⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
            (⟨0x5e⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
            truthParamSuccessFreeMemPtr s :: (⟨0x75⟩ : Ethereum.UInt256) ::
            truthParamSuccessAbiEnd s :: truthParamSuccessFreeMemPtr s ::
            (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) ::
            truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState61, truthParamSuccessState60]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte, Bool.not_eq_true]
    rw [hcontains]
    rfl
  · exact hdecode

theorem truth_success_tail_X_pc87_to_pc93_of_xsteps
    (s : EVM.State)
    (f : Nat)
    (validJumps : Array Ethereum.UInt256)
    (xres : Except Ethereum.EVM.ExecutionException (Ethereum.ExecutionResult EVM.State))
    (h87 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState57 s) =
        .ok (truthParamSuccessState58 s, .none))
    (h88 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState58 s) =
        .ok (truthParamSuccessState59 s, .none))
    (h90 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState59 s) =
        .ok (truthParamSuccessState60 s, .none))
    (h91 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState60 s) =
        .ok (truthParamSuccessState61 s, .none))
    (h93 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState61 s) =
        .ok (truthParamSuccessState62 s, .none))
    (htail :
      Ethereum.EVM.X f validJumps (truthParamSuccessState62 s) = xres) :
    Ethereum.EVM.X (f + 5) validJumps (truthParamSuccessState57 s) = xres := by
  have hf :
      f + 5 = (((((f + 1) + 1) + 1) + 1) + 1) := by
    omega
  rw [hf]
  truth_continue_step h87
  truth_continue_step h88
  truth_continue_step h90
  truth_continue_step h91
  truth_continue_step h93
  exact htail

theorem truth_success_tail_X_pc87_to_pc93_of_gas_guards
    (s : EVM.State)
    (f : Nat)
    (xres : Except Ethereum.EVM.ExecutionException (Ethereum.ExecutionResult EVM.State))
    (h_code : s.executionEnv.code = truthRuntimeBytecode)
    (hgas87 :
      ¬ (truthParamSuccessState57 s).machineState.gasAvailable.toNat <
          GasConstants.Gjumpdest)
    (hgas88 :
      ¬ (truthParamSuccessState58 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas90 :
      ¬ (truthParamSuccessState59 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas91 :
      ¬ (truthParamSuccessState60 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas93 :
      ¬ (truthParamSuccessState61 s).machineState.gasAvailable.toNat <
          GasConstants.Gmid)
    (htail :
      Ethereum.EVM.X f (Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩)
        (truthParamSuccessState62 s) = xres) :
    Ethereum.EVM.X (f + 5) (Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩)
        (truthParamSuccessState57 s) = xres := by
  apply truth_success_tail_X_pc87_to_pc93_of_xsteps
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState57 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState57_code]]
    rw [truth_success_tail_xstep_pc87_core]
    · rw [if_neg hgas87]
    · rw [truthParamSuccessState57_code, h_code]
      exact truth_decode_pc87
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState58 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState58_code]]
    rw [truth_success_tail_xstep_pc88_core]
    · rw [if_neg hgas88]
    · rw [truthParamSuccessState58_code, h_code]
      exact truth_decode_pc88
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState59 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState59_code]]
    rw [truth_success_tail_xstep_pc90_core]
    · rw [if_neg hgas90]
    · rw [truthParamSuccessState59_code, h_code]
      exact truth_decode_pc90
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState60 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState60_code]]
    rw [truth_success_tail_xstep_pc91_core]
    · rw [if_neg hgas91]
    · rw [truthParamSuccessState60_code, h_code]
      exact truth_decode_pc91
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState61 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState61_code]]
    rw [truth_success_tail_xstep_pc93_core]
    · rw [if_neg hgas93]
    · rw [truthParamSuccessState61_code, h_code]
      exact truth_decode_pc93
    · rw [truthParamSuccessState61_code, h_code]
      exact truth_valid_jumpdest_4c
  · exact htail

end Truth
end Examples
end Act
