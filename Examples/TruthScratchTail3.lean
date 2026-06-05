import Examples.TruthScratchTail2

set_option maxRecDepth 100000

namespace Act
namespace Examples
namespace Truth

def truthParamSuccessState63 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState62 s with
    machineState.gasAvailable :=
      (truthParamSuccessState62 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gjumpdest
    machineState.pc := (truthParamSuccessState62 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState62 s).machineState.execLength + 1 }

def truthParamSuccessState64 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState63 s with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) ::
      (truthParamSuccessState63 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamSuccessState63 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := (truthParamSuccessState63 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState63 s).machineState.execLength + 1 }

def truthParamSuccessState65 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState64 s with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨0x5e⟩ : Ethereum.UInt256) ::
      (⟨1⟩ : Ethereum.UInt256) :: truthParamSuccessFreeMemPtr s ::
      (⟨0x75⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
      truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState64 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState64 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState64 s).machineState.execLength + 1 }

def truthParamSuccessState66 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState65 s with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨0x5e⟩ : Ethereum.UInt256) ::
      (⟨1⟩ : Ethereum.UInt256) :: truthParamSuccessFreeMemPtr s ::
      (⟨0x75⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
      truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState65 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState65 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState65 s).machineState.execLength + 1 }

def truthParamSuccessState67 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState66 s with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨0x5e⟩ : Ethereum.UInt256) ::
      (⟨1⟩ : Ethereum.UInt256) :: truthParamSuccessFreeMemPtr s ::
      (⟨0x75⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
      truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState66 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState66 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState66 s).machineState.execLength + 1 }

def truthParamSuccessState68 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState67 s with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨0x5e⟩ : Ethereum.UInt256) ::
      (⟨1⟩ : Ethereum.UInt256) :: truthParamSuccessFreeMemPtr s ::
      (⟨0x75⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
      truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState67 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState67 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState67 s).machineState.execLength + 1 }

def truthParamSuccessState69 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState68 s with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x5e⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
      truthParamSuccessFreeMemPtr s :: (⟨0x75⟩ : Ethereum.UInt256) ::
      truthParamSuccessAbiEnd s :: truthParamSuccessFreeMemPtr s ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) ::
      truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState68 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := (truthParamSuccessState68 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState68 s).machineState.execLength + 1 }

def truthParamSuccessState70 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState69 s with
    machineState.stack := (⟨0x5e⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
      truthParamSuccessFreeMemPtr s :: (⟨0x75⟩ : Ethereum.UInt256) ::
      truthParamSuccessAbiEnd s :: truthParamSuccessFreeMemPtr s ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) ::
      truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState69 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState69 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState69 s).machineState.execLength + 1 }

def truthParamSuccessState71 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState70 s with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: (⟨0x5e⟩ : Ethereum.UInt256) ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
      truthParamSuccessFreeMemPtr s :: (⟨0x75⟩ : Ethereum.UInt256) ::
      truthParamSuccessAbiEnd s :: truthParamSuccessFreeMemPtr s ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) ::
      truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState70 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState70 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState70 s).machineState.execLength + 1 }

def truthParamSuccessState72 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState71 s with
    machineState.stack := (⟨0x5e⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨1⟩ : Ethereum.UInt256) :: truthParamSuccessFreeMemPtr s ::
      (⟨0x75⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
      truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState71 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := (truthParamSuccessState71 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState71 s).machineState.execLength + 1 }

def truthParamSuccessState73 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState72 s with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
      truthParamSuccessFreeMemPtr s :: (⟨0x75⟩ : Ethereum.UInt256) ::
      truthParamSuccessAbiEnd s :: truthParamSuccessFreeMemPtr s ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) ::
      truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState72 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gmid
    machineState.pc := (⟨0x5e⟩ : Ethereum.UInt256)
    machineState.execLength := (truthParamSuccessState72 s).machineState.execLength + 1 }

theorem truthParamSuccessState63_code (s : EVM.State) :
    (truthParamSuccessState63 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState63, truthParamSuccessState62_code]

theorem truthParamSuccessState64_code (s : EVM.State) :
    (truthParamSuccessState64 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState64, truthParamSuccessState63_code]

theorem truthParamSuccessState65_code (s : EVM.State) :
    (truthParamSuccessState65 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState65, truthParamSuccessState64_code]

theorem truthParamSuccessState66_code (s : EVM.State) :
    (truthParamSuccessState66 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState66, truthParamSuccessState65_code]

theorem truthParamSuccessState67_code (s : EVM.State) :
    (truthParamSuccessState67 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState67, truthParamSuccessState66_code]

theorem truthParamSuccessState68_code (s : EVM.State) :
    (truthParamSuccessState68 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState68, truthParamSuccessState67_code]

theorem truthParamSuccessState69_code (s : EVM.State) :
    (truthParamSuccessState69 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState69, truthParamSuccessState68_code]

theorem truthParamSuccessState70_code (s : EVM.State) :
    (truthParamSuccessState70 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState70, truthParamSuccessState69_code]

theorem truthParamSuccessState71_code (s : EVM.State) :
    (truthParamSuccessState71 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState71, truthParamSuccessState70_code]

theorem truthParamSuccessState72_code (s : EVM.State) :
    (truthParamSuccessState72 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState72, truthParamSuccessState71_code]

theorem truthParamSuccessState73_code (s : EVM.State) :
    (truthParamSuccessState73 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState73, truthParamSuccessState72_code]

theorem truth_success_tail_xstep_pc76_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState62 s).executionEnv.code
        (truthParamSuccessState62 s).machineState.pc = some (.JUMPDEST, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState62 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState62 s) =
      if (truthParamSuccessState62 s).machineState.gasAvailable.toNat <
            GasConstants.Gjumpdest then .error .OutOfGass
      else .ok (truthParamSuccessState63 s, .none) := by
  rw [Ethereum.EVM.step_jumpdest (truthParamSuccessState62 s)]
  · have hoverflow :
        ¬ ((truthParamSuccessState62 s).machineState.stack.length - 0 + 0 > 1024) := by
      simp [truthParamSuccessState62]
    rw [if_neg hoverflow]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc77_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState63 s).executionEnv.code
        (truthParamSuccessState63 s).machineState.pc = some (.PUSH0, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState63 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState63 s) =
      if (truthParamSuccessState63 s).machineState.gasAvailable.toNat <
            GasConstants.Gbase then .error .OutOfGass
      else .ok (truthParamSuccessState64 s, .none) := by
  rw [Ethereum.EVM.step_push0 (truthParamSuccessState63 s)]
  · have hoverflow :
        ¬ ((truthParamSuccessState63 s).machineState.stack.length - 0 + 1 > 1024) := by
      simp [truthParamSuccessState63, truthParamSuccessState62]
    rw [if_neg hoverflow]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc78_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState64 s).executionEnv.code
        (truthParamSuccessState64 s).machineState.pc = some (.DUP2, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState64 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState64 s) =
      if (truthParamSuccessState64 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState65 s, .none) := by
  rw [Ethereum.EVM.step_dup2 (truthParamSuccessState64 s)]
  · have hstack :
        (truthParamSuccessState64 s).machineState.stack =
          (⟨0⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
            (⟨0x5e⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
            truthParamSuccessFreeMemPtr s :: (⟨0x75⟩ : Ethereum.UInt256) ::
            truthParamSuccessAbiEnd s :: truthParamSuccessFreeMemPtr s ::
            (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) ::
            truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState64, truthParamSuccessState63, truthParamSuccessState62]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc79_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState65 s).executionEnv.code
        (truthParamSuccessState65 s).machineState.pc = some (.ISZERO, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState65 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState65 s) =
      if (truthParamSuccessState65 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState66 s, .none) := by
  rw [Ethereum.EVM.step_iszero (truthParamSuccessState65 s)]
  · have hstack :
        (truthParamSuccessState65 s).machineState.stack =
          (⟨1⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) ::
            (⟨1⟩ : Ethereum.UInt256) :: (⟨0x5e⟩ : Ethereum.UInt256) ::
            (⟨1⟩ : Ethereum.UInt256) :: truthParamSuccessFreeMemPtr s ::
            (⟨0x75⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
            truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
            (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState65]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc80_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState66 s).executionEnv.code
        (truthParamSuccessState66 s).machineState.pc = some (.ISZERO, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState66 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState66 s) =
      if (truthParamSuccessState66 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState67 s, .none) := by
  rw [Ethereum.EVM.step_iszero (truthParamSuccessState66 s)]
  · have hstack :
        (truthParamSuccessState66 s).machineState.stack =
          (⟨0⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) ::
            (⟨1⟩ : Ethereum.UInt256) :: (⟨0x5e⟩ : Ethereum.UInt256) ::
            (⟨1⟩ : Ethereum.UInt256) :: truthParamSuccessFreeMemPtr s ::
            (⟨0x75⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
            truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
            (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState66]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc81_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState67 s).executionEnv.code
        (truthParamSuccessState67 s).machineState.pc = some (.SWAP1, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState67 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState67 s) =
      if (truthParamSuccessState67 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState68 s, .none) := by
  rw [Ethereum.EVM.step_swap1 (truthParamSuccessState67 s)]
  · have hstack :
        (truthParamSuccessState67 s).machineState.stack =
          (⟨1⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) ::
            (⟨1⟩ : Ethereum.UInt256) :: (⟨0x5e⟩ : Ethereum.UInt256) ::
            (⟨1⟩ : Ethereum.UInt256) :: truthParamSuccessFreeMemPtr s ::
            (⟨0x75⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
            truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
            (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState67]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc82_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState68 s).executionEnv.code
        (truthParamSuccessState68 s).machineState.pc = some (.POP, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState68 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState68 s) =
      if (truthParamSuccessState68 s).machineState.gasAvailable.toNat <
            GasConstants.Gbase then .error .OutOfGass
      else .ok (truthParamSuccessState69 s, .none) := by
  rw [Ethereum.EVM.step_pop (truthParamSuccessState68 s)]
  · have hstack :
        (truthParamSuccessState68 s).machineState.stack =
          (⟨0⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
            (⟨1⟩ : Ethereum.UInt256) :: (⟨0x5e⟩ : Ethereum.UInt256) ::
            (⟨1⟩ : Ethereum.UInt256) :: truthParamSuccessFreeMemPtr s ::
            (⟨0x75⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
            truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
            (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState68]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc83_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState69 s).executionEnv.code
        (truthParamSuccessState69 s).machineState.pc = some (.SWAP2, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState69 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState69 s) =
      if (truthParamSuccessState69 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState70 s, .none) := by
  rw [Ethereum.EVM.step_swap2 (truthParamSuccessState69 s)]
  · have hstack :
        (truthParamSuccessState69 s).machineState.stack =
          (⟨1⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
            (⟨0x5e⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
            truthParamSuccessFreeMemPtr s :: (⟨0x75⟩ : Ethereum.UInt256) ::
            truthParamSuccessAbiEnd s :: truthParamSuccessFreeMemPtr s ::
            (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) ::
            truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState69]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc84_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState70 s).executionEnv.code
        (truthParamSuccessState70 s).machineState.pc = some (.SWAP1, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState70 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState70 s) =
      if (truthParamSuccessState70 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState71 s, .none) := by
  rw [Ethereum.EVM.step_swap1 (truthParamSuccessState70 s)]
  · have hstack :
        (truthParamSuccessState70 s).machineState.stack =
          (⟨0x5e⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
            (⟨1⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
            truthParamSuccessFreeMemPtr s :: (⟨0x75⟩ : Ethereum.UInt256) ::
            truthParamSuccessAbiEnd s :: truthParamSuccessFreeMemPtr s ::
            (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) ::
            truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState70]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc85_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState71 s).executionEnv.code
        (truthParamSuccessState71 s).machineState.pc = some (.POP, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState71 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState71 s) =
      if (truthParamSuccessState71 s).machineState.gasAvailable.toNat <
            GasConstants.Gbase then .error .OutOfGass
      else .ok (truthParamSuccessState72 s, .none) := by
  rw [Ethereum.EVM.step_pop (truthParamSuccessState71 s)]
  · have hstack :
        (truthParamSuccessState71 s).machineState.stack =
          (⟨1⟩ : Ethereum.UInt256) :: (⟨0x5e⟩ : Ethereum.UInt256) ::
            (⟨1⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
            truthParamSuccessFreeMemPtr s :: (⟨0x75⟩ : Ethereum.UInt256) ::
            truthParamSuccessAbiEnd s :: truthParamSuccessFreeMemPtr s ::
            (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) ::
            truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState71]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc86_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState72 s).executionEnv.code
        (truthParamSuccessState72 s).machineState.pc = some (.JUMP, .none))
    (hcontains :
      (Ethereum.EVM.D_J (truthParamSuccessState72 s).executionEnv.code ⟨0⟩).contains
        (⟨0x5e⟩ : Ethereum.UInt256) = true) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState72 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState72 s) =
      if (truthParamSuccessState72 s).machineState.gasAvailable.toNat <
            GasConstants.Gmid then .error .OutOfGass
      else .ok (truthParamSuccessState73 s, .none) := by
  rw [Ethereum.EVM.step_jump (truthParamSuccessState72 s)]
  · have hstack :
        (truthParamSuccessState72 s).machineState.stack =
          (⟨0x5e⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
            (⟨1⟩ : Ethereum.UInt256) :: truthParamSuccessFreeMemPtr s ::
            (⟨0x75⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
            truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
            (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState72, truthParamSuccessState71]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte, Bool.not_eq_true]
    rw [hcontains]
    rfl
  · exact hdecode

theorem truth_success_tail_X_pc76_to_pc86_of_xsteps
    (s : EVM.State)
    (f : Nat)
    (validJumps : Array Ethereum.UInt256)
    (xres : Except Ethereum.EVM.ExecutionException (Ethereum.ExecutionResult EVM.State))
    (h76 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState62 s) =
        .ok (truthParamSuccessState63 s, .none))
    (h77 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState63 s) =
        .ok (truthParamSuccessState64 s, .none))
    (h78 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState64 s) =
        .ok (truthParamSuccessState65 s, .none))
    (h79 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState65 s) =
        .ok (truthParamSuccessState66 s, .none))
    (h80 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState66 s) =
        .ok (truthParamSuccessState67 s, .none))
    (h81 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState67 s) =
        .ok (truthParamSuccessState68 s, .none))
    (h82 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState68 s) =
        .ok (truthParamSuccessState69 s, .none))
    (h83 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState69 s) =
        .ok (truthParamSuccessState70 s, .none))
    (h84 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState70 s) =
        .ok (truthParamSuccessState71 s, .none))
    (h85 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState71 s) =
        .ok (truthParamSuccessState72 s, .none))
    (h86 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState72 s) =
        .ok (truthParamSuccessState73 s, .none))
    (htail :
      Ethereum.EVM.X f validJumps (truthParamSuccessState73 s) = xres) :
    Ethereum.EVM.X (f + 11) validJumps (truthParamSuccessState62 s) = xres := by
  have hf :
      f + 11 = (((((((((((f + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) := by
    omega
  rw [hf]
  truth_continue_step h76
  truth_continue_step h77
  truth_continue_step h78
  truth_continue_step h79
  truth_continue_step h80
  truth_continue_step h81
  truth_continue_step h82
  truth_continue_step h83
  truth_continue_step h84
  truth_continue_step h85
  truth_continue_step h86
  exact htail

theorem truth_success_tail_X_pc76_to_pc86_of_gas_guards
    (s : EVM.State)
    (f : Nat)
    (xres : Except Ethereum.EVM.ExecutionException (Ethereum.ExecutionResult EVM.State))
    (h_code : s.executionEnv.code = truthRuntimeBytecode)
    (hgas76 :
      ¬ (truthParamSuccessState62 s).machineState.gasAvailable.toNat <
          GasConstants.Gjumpdest)
    (hgas77 :
      ¬ (truthParamSuccessState63 s).machineState.gasAvailable.toNat <
          GasConstants.Gbase)
    (hgas78 :
      ¬ (truthParamSuccessState64 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas79 :
      ¬ (truthParamSuccessState65 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas80 :
      ¬ (truthParamSuccessState66 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas81 :
      ¬ (truthParamSuccessState67 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas82 :
      ¬ (truthParamSuccessState68 s).machineState.gasAvailable.toNat <
          GasConstants.Gbase)
    (hgas83 :
      ¬ (truthParamSuccessState69 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas84 :
      ¬ (truthParamSuccessState70 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas85 :
      ¬ (truthParamSuccessState71 s).machineState.gasAvailable.toNat <
          GasConstants.Gbase)
    (hgas86 :
      ¬ (truthParamSuccessState72 s).machineState.gasAvailable.toNat <
          GasConstants.Gmid)
    (htail :
      Ethereum.EVM.X f (Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩)
        (truthParamSuccessState73 s) = xres) :
    Ethereum.EVM.X (f + 11) (Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩)
        (truthParamSuccessState62 s) = xres := by
  apply truth_success_tail_X_pc76_to_pc86_of_xsteps
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState62 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState62_code]]
    rw [truth_success_tail_xstep_pc76_core]
    · rw [if_neg hgas76]
    · rw [truthParamSuccessState62_code, h_code]
      exact truth_decode_pc76
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState63 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState63_code]]
    rw [truth_success_tail_xstep_pc77_core]
    · rw [if_neg hgas77]
    · rw [truthParamSuccessState63_code, h_code]
      exact truth_decode_pc77
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState64 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState64_code]]
    rw [truth_success_tail_xstep_pc78_core]
    · rw [if_neg hgas78]
    · rw [truthParamSuccessState64_code, h_code]
      exact truth_decode_pc78
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState65 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState65_code]]
    rw [truth_success_tail_xstep_pc79_core]
    · rw [if_neg hgas79]
    · rw [truthParamSuccessState65_code, h_code]
      exact truth_decode_pc79
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState66 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState66_code]]
    rw [truth_success_tail_xstep_pc80_core]
    · rw [if_neg hgas80]
    · rw [truthParamSuccessState66_code, h_code]
      exact truth_decode_pc80
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState67 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState67_code]]
    rw [truth_success_tail_xstep_pc81_core]
    · rw [if_neg hgas81]
    · rw [truthParamSuccessState67_code, h_code]
      exact truth_decode_pc81
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState68 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState68_code]]
    rw [truth_success_tail_xstep_pc82_core]
    · rw [if_neg hgas82]
    · rw [truthParamSuccessState68_code, h_code]
      exact truth_decode_pc82
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState69 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState69_code]]
    rw [truth_success_tail_xstep_pc83_core]
    · rw [if_neg hgas83]
    · rw [truthParamSuccessState69_code, h_code]
      exact truth_decode_pc83
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState70 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState70_code]]
    rw [truth_success_tail_xstep_pc84_core]
    · rw [if_neg hgas84]
    · rw [truthParamSuccessState70_code, h_code]
      exact truth_decode_pc84
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState71 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState71_code]]
    rw [truth_success_tail_xstep_pc85_core]
    · rw [if_neg hgas85]
    · rw [truthParamSuccessState71_code, h_code]
      exact truth_decode_pc85
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState72 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState72_code]]
    rw [truth_success_tail_xstep_pc86_core]
    · rw [if_neg hgas86]
    · rw [truthParamSuccessState72_code, h_code]
      exact truth_decode_pc86
    · rw [truthParamSuccessState72_code, h_code]
      exact truth_valid_jumpdest_5e
  · exact htail

end Truth
end Examples
end Act
