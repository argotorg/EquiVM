import Examples.TruthScratchTail3

set_option maxRecDepth 100000

namespace Act
namespace Examples
namespace Truth

def truthParamSuccessState74 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState73 s with
    machineState.gasAvailable :=
      (truthParamSuccessState73 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gjumpdest
    machineState.pc := (truthParamSuccessState73 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState73 s).machineState.execLength + 1 }

def truthParamSuccessState75 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState74 s with
    machineState.stack := truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨1⟩ : Ethereum.UInt256) :: truthParamSuccessFreeMemPtr s ::
      (⟨0x75⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
      truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState74 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState74 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState74 s).machineState.execLength + 1 }

def truthParamSuccessEncodedMemory (s : EVM.State) : ByteArray :=
  (⟨1⟩ : Ethereum.UInt256).toByteArray.write 0
    (truthParamSuccessState75 s).machineState.memory (truthParamSuccessFreeMemPtr s).toNat 32

def truthParamSuccessState76 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState75 s with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: truthParamSuccessFreeMemPtr s ::
      (⟨0x75⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
      truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: []
    machineState.memory := truthParamSuccessEncodedMemory s
    machineState.activeWords :=
      Ethereum.UInt256.ofNat
        (Ethereum.MachineState.M (truthParamSuccessState75 s).machineState.activeWords.toNat
          (truthParamSuccessFreeMemPtr s).toNat 32)
    machineState.gasAvailable :=
      ((truthParamSuccessState75 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost (truthParamSuccessState75 s) .MSTORE)) -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState75 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState75 s).machineState.execLength + 1 }

def truthParamSuccessState77 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState76 s with
    machineState.stack := truthParamSuccessFreeMemPtr s :: (⟨0x75⟩ : Ethereum.UInt256) ::
      truthParamSuccessAbiEnd s :: truthParamSuccessFreeMemPtr s ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) ::
      truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState76 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := (truthParamSuccessState76 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState76 s).machineState.execLength + 1 }

def truthParamSuccessState78 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState77 s with
    machineState.stack := (⟨0x75⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
      truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState77 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := (truthParamSuccessState77 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState77 s).machineState.execLength + 1 }

def truthParamSuccessState79 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState78 s with
    machineState.stack := truthParamSuccessAbiEnd s :: truthParamSuccessFreeMemPtr s ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) ::
      truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState78 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gmid
    machineState.pc := (⟨0x75⟩ : Ethereum.UInt256)
    machineState.execLength := (truthParamSuccessState78 s).machineState.execLength + 1 }

theorem truthParamSuccessState74_code (s : EVM.State) :
    (truthParamSuccessState74 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState74, truthParamSuccessState73_code]

theorem truthParamSuccessState75_code (s : EVM.State) :
    (truthParamSuccessState75 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState75, truthParamSuccessState74_code]

theorem truthParamSuccessState76_code (s : EVM.State) :
    (truthParamSuccessState76 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState76, truthParamSuccessState75_code]

theorem truthParamSuccessState77_code (s : EVM.State) :
    (truthParamSuccessState77 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState77, truthParamSuccessState76_code]

theorem truthParamSuccessState78_code (s : EVM.State) :
    (truthParamSuccessState78 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState78, truthParamSuccessState77_code]

theorem truthParamSuccessState79_code (s : EVM.State) :
    (truthParamSuccessState79 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState79, truthParamSuccessState78_code]

theorem truth_success_tail_xstep_pc94_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState73 s).executionEnv.code
        (truthParamSuccessState73 s).machineState.pc = some (.JUMPDEST, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState73 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState73 s) =
      if (truthParamSuccessState73 s).machineState.gasAvailable.toNat <
            GasConstants.Gjumpdest then .error .OutOfGass
      else .ok (truthParamSuccessState74 s, .none) := by
  rw [Ethereum.EVM.step_jumpdest (truthParamSuccessState73 s)]
  · have hoverflow :
        ¬ ((truthParamSuccessState73 s).machineState.stack.length - 0 + 0 > 1024) := by
      simp [truthParamSuccessState73]
    rw [if_neg hoverflow]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc95_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState74 s).executionEnv.code
        (truthParamSuccessState74 s).machineState.pc = some (.DUP3, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState74 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState74 s) =
      if (truthParamSuccessState74 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState75 s, .none) := by
  rw [Ethereum.EVM.step_dup3 (truthParamSuccessState74 s)]
  · have hstack :
        (truthParamSuccessState74 s).machineState.stack =
          (⟨1⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
            truthParamSuccessFreeMemPtr s :: (⟨0x75⟩ : Ethereum.UInt256) ::
            truthParamSuccessAbiEnd s :: truthParamSuccessFreeMemPtr s ::
            (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) ::
            truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState74, truthParamSuccessState73]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc96_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState75 s).executionEnv.code
        (truthParamSuccessState75 s).machineState.pc = some (.MSTORE, .none))
    (hmem :
      ¬ (truthParamSuccessState75 s).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost (truthParamSuccessState75 s) .MSTORE)
    (hgas :
      ¬ ((truthParamSuccessState75 s).machineState.gasAvailable -
          Ethereum.UInt256.ofNat
            (Ethereum.EVM.memoryExpansionCost (truthParamSuccessState75 s) .MSTORE)).toNat <
        GasConstants.Gverylow) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState75 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState75 s) =
      .ok (truthParamSuccessState76 s, .none) := by
  rw [Ethereum.EVM.step_mstore (truthParamSuccessState75 s) hdecode]
  have hstack :
      (truthParamSuccessState75 s).machineState.stack =
        truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
          (⟨1⟩ : Ethereum.UInt256) :: truthParamSuccessFreeMemPtr s ::
          (⟨0x75⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
          truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
          (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: [] := by
    simp [truthParamSuccessState75]
  rw [hstack]
  change
    (if (truthParamSuccessState75 s).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost (truthParamSuccessState75 s) .MSTORE then _ else _) = _
  rw [if_neg hmem]
  change
    (if ((truthParamSuccessState75 s).machineState.gasAvailable -
          Ethereum.UInt256.ofNat
            (Ethereum.EVM.memoryExpansionCost (truthParamSuccessState75 s) .MSTORE)).toNat <
        GasConstants.Gverylow then _ else _) = _
  rw [if_neg hgas]
  simp only [truthParamSuccessState75, truthParamSuccessState76, truthParamSuccessEncodedMemory,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  have hoverflow : ¬ 8 > 1024 := by native_decide
  rw [if_neg hoverflow]

theorem truth_success_tail_xstep_pc97_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState76 s).executionEnv.code
        (truthParamSuccessState76 s).machineState.pc = some (.POP, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState76 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState76 s) =
      if (truthParamSuccessState76 s).machineState.gasAvailable.toNat <
            GasConstants.Gbase then .error .OutOfGass
      else .ok (truthParamSuccessState77 s, .none) := by
  rw [Ethereum.EVM.step_pop (truthParamSuccessState76 s)]
  · have hstack :
        (truthParamSuccessState76 s).machineState.stack =
          (⟨1⟩ : Ethereum.UInt256) :: truthParamSuccessFreeMemPtr s ::
            (⟨0x75⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
            truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
            (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState76]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc98_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState77 s).executionEnv.code
        (truthParamSuccessState77 s).machineState.pc = some (.POP, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState77 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState77 s) =
      if (truthParamSuccessState77 s).machineState.gasAvailable.toNat <
            GasConstants.Gbase then .error .OutOfGass
      else .ok (truthParamSuccessState78 s, .none) := by
  rw [Ethereum.EVM.step_pop (truthParamSuccessState77 s)]
  · have hstack :
        (truthParamSuccessState77 s).machineState.stack =
          truthParamSuccessFreeMemPtr s :: (⟨0x75⟩ : Ethereum.UInt256) ::
            truthParamSuccessAbiEnd s :: truthParamSuccessFreeMemPtr s ::
            (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) ::
            truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState77]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc99_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState78 s).executionEnv.code
        (truthParamSuccessState78 s).machineState.pc = some (.JUMP, .none))
    (hcontains :
      (Ethereum.EVM.D_J (truthParamSuccessState78 s).executionEnv.code ⟨0⟩).contains
        (⟨0x75⟩ : Ethereum.UInt256) = true) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState78 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState78 s) =
      if (truthParamSuccessState78 s).machineState.gasAvailable.toNat <
            GasConstants.Gmid then .error .OutOfGass
      else .ok (truthParamSuccessState79 s, .none) := by
  rw [Ethereum.EVM.step_jump (truthParamSuccessState78 s)]
  · have hstack :
        (truthParamSuccessState78 s).machineState.stack =
          (⟨0x75⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
            truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
            (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState78, truthParamSuccessState77]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte, Bool.not_eq_true]
    rw [hcontains]
    rfl
  · exact hdecode

theorem truth_success_tail_X_pc94_to_pc99_of_xsteps
    (s : EVM.State)
    (f : Nat)
    (validJumps : Array Ethereum.UInt256)
    (xres : Except Ethereum.EVM.ExecutionException (Ethereum.ExecutionResult EVM.State))
    (h94 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState73 s) =
        .ok (truthParamSuccessState74 s, .none))
    (h95 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState74 s) =
        .ok (truthParamSuccessState75 s, .none))
    (h96 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState75 s) =
        .ok (truthParamSuccessState76 s, .none))
    (h97 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState76 s) =
        .ok (truthParamSuccessState77 s, .none))
    (h98 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState77 s) =
        .ok (truthParamSuccessState78 s, .none))
    (h99 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState78 s) =
        .ok (truthParamSuccessState79 s, .none))
    (htail :
      Ethereum.EVM.X f validJumps (truthParamSuccessState79 s) = xres) :
    Ethereum.EVM.X (f + 6) validJumps (truthParamSuccessState73 s) = xres := by
  have hf :
      f + 6 = ((((((f + 1) + 1) + 1) + 1) + 1) + 1) := by
    omega
  rw [hf]
  truth_continue_step h94
  truth_continue_step h95
  truth_continue_step h96
  truth_continue_step h97
  truth_continue_step h98
  truth_continue_step h99
  exact htail

theorem truth_success_tail_X_pc94_to_pc99_of_gas_guards
    (s : EVM.State)
    (f : Nat)
    (xres : Except Ethereum.EVM.ExecutionException (Ethereum.ExecutionResult EVM.State))
    (h_code : s.executionEnv.code = truthRuntimeBytecode)
    (hgas94 :
      ¬ (truthParamSuccessState73 s).machineState.gasAvailable.toNat <
          GasConstants.Gjumpdest)
    (hgas95 :
      ¬ (truthParamSuccessState74 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hmem96 :
      ¬ (truthParamSuccessState75 s).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost (truthParamSuccessState75 s) .MSTORE)
    (hgas96 :
      ¬ ((truthParamSuccessState75 s).machineState.gasAvailable -
          Ethereum.UInt256.ofNat
            (Ethereum.EVM.memoryExpansionCost (truthParamSuccessState75 s) .MSTORE)).toNat <
        GasConstants.Gverylow)
    (hgas97 :
      ¬ (truthParamSuccessState76 s).machineState.gasAvailable.toNat <
          GasConstants.Gbase)
    (hgas98 :
      ¬ (truthParamSuccessState77 s).machineState.gasAvailable.toNat <
          GasConstants.Gbase)
    (hgas99 :
      ¬ (truthParamSuccessState78 s).machineState.gasAvailable.toNat <
          GasConstants.Gmid)
    (htail :
      Ethereum.EVM.X f (Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩)
        (truthParamSuccessState79 s) = xres) :
    Ethereum.EVM.X (f + 6) (Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩)
        (truthParamSuccessState73 s) = xres := by
  apply truth_success_tail_X_pc94_to_pc99_of_xsteps
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState73 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState73_code]]
    rw [truth_success_tail_xstep_pc94_core]
    · rw [if_neg hgas94]
    · rw [truthParamSuccessState73_code, h_code]
      exact truth_decode_pc94
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState74 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState74_code]]
    rw [truth_success_tail_xstep_pc95_core]
    · rw [if_neg hgas95]
    · rw [truthParamSuccessState74_code, h_code]
      exact truth_decode_pc95
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState75 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState75_code]]
    rw [truth_success_tail_xstep_pc96_core]
    · rw [truthParamSuccessState75_code, h_code]
      exact truth_decode_pc96
    · exact hmem96
    · exact hgas96
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState76 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState76_code]]
    rw [truth_success_tail_xstep_pc97_core]
    · rw [if_neg hgas97]
    · rw [truthParamSuccessState76_code, h_code]
      exact truth_decode_pc97
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState77 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState77_code]]
    rw [truth_success_tail_xstep_pc98_core]
    · rw [if_neg hgas98]
    · rw [truthParamSuccessState77_code, h_code]
      exact truth_decode_pc98
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState78 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState78_code]]
    rw [truth_success_tail_xstep_pc99_core]
    · rw [if_neg hgas99]
    · rw [truthParamSuccessState78_code, h_code]
      exact truth_decode_pc99
    · rw [truthParamSuccessState78_code, h_code]
      exact truth_valid_jumpdest_75
  · exact htail

end Truth
end Examples
end Act
