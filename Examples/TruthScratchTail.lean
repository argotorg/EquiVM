import Examples.TruthScratchStep

set_option maxRecDepth 100000

namespace Act
namespace Examples
namespace Truth

def truthParamSuccessState44 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState43 s with
    machineState.gasAvailable :=
      (truthParamSuccessState43 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gjumpdest
    machineState.pc := (truthParamSuccessState43 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState43 s).machineState.execLength + 1 }

def truthParamSuccessState45 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState44 s with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) ::
      (truthParamSuccessState44 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamSuccessState44 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := (truthParamSuccessState44 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState44 s).machineState.execLength + 1 }

def truthParamSuccessState46 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState45 s with
    machineState.stack := (⟨0x20⟩ : Ethereum.UInt256) ::
      (truthParamSuccessState45 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamSuccessState45 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc :=
      (truthParamSuccessState45 s).machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := (truthParamSuccessState45 s).machineState.execLength + 1 }

def truthParamSuccessState47 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState46 s with
    machineState.stack := truthParamSuccessFreeMemPtr s :: (⟨0x20⟩ : Ethereum.UInt256) ::
      (⟨0⟩ : Ethereum.UInt256) :: truthParamSuccessFreeMemPtr s ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) ::
      truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState46 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState46 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState46 s).machineState.execLength + 1 }

def truthParamSuccessState48 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState47 s with
    machineState.stack := truthParamSuccessAbiEnd s :: (⟨0⟩ : Ethereum.UInt256) ::
      truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState47 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState47 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState47 s).machineState.execLength + 1 }

def truthParamSuccessState49 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState48 s with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
      truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState48 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState48 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState48 s).machineState.execLength + 1 }

def truthParamSuccessState50 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState49 s with
    machineState.stack := truthParamSuccessAbiEnd s :: truthParamSuccessFreeMemPtr s ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) ::
      truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState49 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := (truthParamSuccessState49 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState49 s).machineState.execLength + 1 }

def truthParamSuccessState51 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState50 s with
    machineState.stack := (⟨0x75⟩ : Ethereum.UInt256) ::
      (truthParamSuccessState50 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamSuccessState50 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc :=
      (truthParamSuccessState50 s).machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := (truthParamSuccessState50 s).machineState.execLength + 1 }

def truthParamSuccessState52 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState51 s with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) ::
      (truthParamSuccessState51 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamSuccessState51 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := (truthParamSuccessState51 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState51 s).machineState.execLength + 1 }

def truthParamSuccessState53 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState52 s with
    machineState.stack := truthParamSuccessFreeMemPtr s :: (⟨0⟩ : Ethereum.UInt256) ::
      (⟨0x75⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
      truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState52 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState52 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState52 s).machineState.execLength + 1 }

def truthParamSuccessState54 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState53 s with
    machineState.stack := truthParamSuccessFreeMemPtr s :: (⟨0x75⟩ : Ethereum.UInt256) ::
      truthParamSuccessAbiEnd s :: truthParamSuccessFreeMemPtr s ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) ::
      truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState53 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState53 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState53 s).machineState.execLength + 1 }

def truthParamSuccessState55 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState54 s with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: truthParamSuccessFreeMemPtr s ::
      (⟨0x75⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
      truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState54 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState54 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState54 s).machineState.execLength + 1 }

def truthParamSuccessState56 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState55 s with
    machineState.stack := (⟨0x57⟩ : Ethereum.UInt256) ::
      (truthParamSuccessState55 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamSuccessState55 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc :=
      (truthParamSuccessState55 s).machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := (truthParamSuccessState55 s).machineState.execLength + 1 }

def truthParamSuccessState57 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState56 s with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: truthParamSuccessFreeMemPtr s ::
      (⟨0x75⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
      truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState56 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gmid
    machineState.pc := (⟨0x57⟩ : Ethereum.UInt256)
    machineState.execLength := (truthParamSuccessState56 s).machineState.execLength + 1 }

theorem truthParamSuccessState44_code (s : EVM.State) :
    (truthParamSuccessState44 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState44, truthParamSuccessState43_code]

theorem truthParamSuccessState45_code (s : EVM.State) :
    (truthParamSuccessState45 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState45, truthParamSuccessState44_code]

theorem truthParamSuccessState46_code (s : EVM.State) :
    (truthParamSuccessState46 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState46, truthParamSuccessState45_code]

theorem truthParamSuccessState47_code (s : EVM.State) :
    (truthParamSuccessState47 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState47, truthParamSuccessState46_code]

theorem truthParamSuccessState48_code (s : EVM.State) :
    (truthParamSuccessState48 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState48, truthParamSuccessState47_code]

theorem truthParamSuccessState49_code (s : EVM.State) :
    (truthParamSuccessState49 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState49, truthParamSuccessState48_code]

theorem truthParamSuccessState50_code (s : EVM.State) :
    (truthParamSuccessState50 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState50, truthParamSuccessState49_code]

theorem truthParamSuccessState51_code (s : EVM.State) :
    (truthParamSuccessState51 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState51, truthParamSuccessState50_code]

theorem truthParamSuccessState52_code (s : EVM.State) :
    (truthParamSuccessState52 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState52, truthParamSuccessState51_code]

theorem truthParamSuccessState53_code (s : EVM.State) :
    (truthParamSuccessState53 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState53, truthParamSuccessState52_code]

theorem truthParamSuccessState54_code (s : EVM.State) :
    (truthParamSuccessState54 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState54, truthParamSuccessState53_code]

theorem truthParamSuccessState55_code (s : EVM.State) :
    (truthParamSuccessState55 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState55, truthParamSuccessState54_code]

theorem truthParamSuccessState56_code (s : EVM.State) :
    (truthParamSuccessState56 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState56, truthParamSuccessState55_code]

theorem truthParamSuccessState57_code (s : EVM.State) :
    (truthParamSuccessState57 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState57, truthParamSuccessState56_code]

theorem truth_success_tail_xstep_pc100_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState43 s).executionEnv.code
        (truthParamSuccessState43 s).machineState.pc = some (.JUMPDEST, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState43 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState43 s) =
      if (truthParamSuccessState43 s).machineState.gasAvailable.toNat <
            GasConstants.Gjumpdest then .error .OutOfGass
      else .ok (truthParamSuccessState44 s, .none) := by
  rw [Ethereum.EVM.step_jumpdest (truthParamSuccessState43 s)]
  · have hoverflow :
        ¬ ((truthParamSuccessState43 s).machineState.stack.length - 0 + 0 > 1024) := by
      simp [truthParamSuccessState43, truthParamSuccessState42, truthParamSuccessState41]
    rw [if_neg hoverflow]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc101_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState44 s).executionEnv.code
        (truthParamSuccessState44 s).machineState.pc = some (.PUSH0, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState44 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState44 s) =
      if (truthParamSuccessState44 s).machineState.gasAvailable.toNat <
            GasConstants.Gbase then .error .OutOfGass
      else .ok (truthParamSuccessState45 s, .none) := by
  rw [Ethereum.EVM.step_push0 (truthParamSuccessState44 s)]
  · have hoverflow :
        ¬ ((truthParamSuccessState44 s).machineState.stack.length - 0 + 1 > 1024) := by
      simp [truthParamSuccessState44, truthParamSuccessState43]
    rw [if_neg hoverflow]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc102_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState45 s).executionEnv.code
        (truthParamSuccessState45 s).machineState.pc =
          some (.PUSH1, .some ((⟨0x20⟩ : Ethereum.UInt256), 1))) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState45 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState45 s) =
      if (truthParamSuccessState45 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState46 s, .none) := by
  rw [Ethereum.EVM.step_push1 (truthParamSuccessState45 s) (⟨0x20⟩ : Ethereum.UInt256)]
  · have hoverflow :
        ¬ ((truthParamSuccessState45 s).machineState.stack.length - 0 + 1 > 1024) := by
      simp [truthParamSuccessState45, truthParamSuccessState44, truthParamSuccessState43]
    rw [if_neg hoverflow]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc104_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState46 s).executionEnv.code
        (truthParamSuccessState46 s).machineState.pc = some (.DUP3, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState46 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState46 s) =
      if (truthParamSuccessState46 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState47 s, .none) := by
  rw [Ethereum.EVM.step_dup3 (truthParamSuccessState46 s)]
  · have hstack :
        (truthParamSuccessState46 s).machineState.stack =
          (⟨0x20⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) ::
            truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
            (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState46, truthParamSuccessState45, truthParamSuccessState44,
        truthParamSuccessState43]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc105_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState47 s).executionEnv.code
        (truthParamSuccessState47 s).machineState.pc = some (.ADD, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState47 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState47 s) =
      if (truthParamSuccessState47 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState48 s, .none) := by
  rw [Ethereum.EVM.step_add (truthParamSuccessState47 s)]
  · have hstack :
        (truthParamSuccessState47 s).machineState.stack =
          truthParamSuccessFreeMemPtr s :: (⟨0x20⟩ : Ethereum.UInt256) ::
            (⟨0⟩ : Ethereum.UInt256) :: truthParamSuccessFreeMemPtr s ::
            (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) ::
            truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState47]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte]
    simp [truthParamSuccessState48, truthParamSuccessAbiEnd]
  · exact hdecode

theorem truth_success_tail_xstep_pc106_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState48 s).executionEnv.code
        (truthParamSuccessState48 s).machineState.pc = some (.SWAP1, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState48 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState48 s) =
      if (truthParamSuccessState48 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState49 s, .none) := by
  rw [Ethereum.EVM.step_swap1 (truthParamSuccessState48 s)]
  · have hstack :
        (truthParamSuccessState48 s).machineState.stack =
          truthParamSuccessAbiEnd s :: (⟨0⟩ : Ethereum.UInt256) ::
            truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
            (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState48]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc107_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState49 s).executionEnv.code
        (truthParamSuccessState49 s).machineState.pc = some (.POP, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState49 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState49 s) =
      if (truthParamSuccessState49 s).machineState.gasAvailable.toNat <
            GasConstants.Gbase then .error .OutOfGass
      else .ok (truthParamSuccessState50 s, .none) := by
  rw [Ethereum.EVM.step_pop (truthParamSuccessState49 s)]
  · have hstack :
        (truthParamSuccessState49 s).machineState.stack =
          (⟨0⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
            truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
            (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState49]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc108_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState50 s).executionEnv.code
        (truthParamSuccessState50 s).machineState.pc =
          some (.PUSH1, .some ((⟨0x75⟩ : Ethereum.UInt256), 1))) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState50 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState50 s) =
      if (truthParamSuccessState50 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState51 s, .none) := by
  rw [Ethereum.EVM.step_push1 (truthParamSuccessState50 s) (⟨0x75⟩ : Ethereum.UInt256)]
  · have hoverflow :
        ¬ ((truthParamSuccessState50 s).machineState.stack.length - 0 + 1 > 1024) := by
      simp [truthParamSuccessState50]
    rw [if_neg hoverflow]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc110_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState51 s).executionEnv.code
        (truthParamSuccessState51 s).machineState.pc = some (.PUSH0, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState51 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState51 s) =
      if (truthParamSuccessState51 s).machineState.gasAvailable.toNat <
            GasConstants.Gbase then .error .OutOfGass
      else .ok (truthParamSuccessState52 s, .none) := by
  rw [Ethereum.EVM.step_push0 (truthParamSuccessState51 s)]
  · have hoverflow :
        ¬ ((truthParamSuccessState51 s).machineState.stack.length - 0 + 1 > 1024) := by
      simp [truthParamSuccessState51, truthParamSuccessState50]
    rw [if_neg hoverflow]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc111_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState52 s).executionEnv.code
        (truthParamSuccessState52 s).machineState.pc = some (.DUP4, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState52 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState52 s) =
      if (truthParamSuccessState52 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState53 s, .none) := by
  rw [Ethereum.EVM.step_dup4 (truthParamSuccessState52 s)]
  · have hstack :
        (truthParamSuccessState52 s).machineState.stack =
          (⟨0⟩ : Ethereum.UInt256) :: (⟨0x75⟩ : Ethereum.UInt256) ::
            truthParamSuccessAbiEnd s :: truthParamSuccessFreeMemPtr s ::
            (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) ::
            truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState52, truthParamSuccessState51, truthParamSuccessState50]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc112_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState53 s).executionEnv.code
        (truthParamSuccessState53 s).machineState.pc = some (.ADD, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState53 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState53 s) =
      if (truthParamSuccessState53 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState54 s, .none) := by
  rw [Ethereum.EVM.step_add (truthParamSuccessState53 s)]
  · have hstack :
        (truthParamSuccessState53 s).machineState.stack =
          truthParamSuccessFreeMemPtr s :: (⟨0⟩ : Ethereum.UInt256) ::
            (⟨0x75⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
            truthParamSuccessFreeMemPtr s :: (⟨1⟩ : Ethereum.UInt256) ::
            (⟨0x3b⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState53]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte]
    simp [truthParamSuccessState54, truth_uint256_add_zero]
  · exact hdecode

theorem truth_success_tail_xstep_pc113_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState54 s).executionEnv.code
        (truthParamSuccessState54 s).machineState.pc = some (.DUP5, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState54 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState54 s) =
      if (truthParamSuccessState54 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState55 s, .none) := by
  rw [Ethereum.EVM.step_dup5 (truthParamSuccessState54 s)]
  · have hstack :
        (truthParamSuccessState54 s).machineState.stack =
          truthParamSuccessFreeMemPtr s :: (⟨0x75⟩ : Ethereum.UInt256) ::
            truthParamSuccessAbiEnd s :: truthParamSuccessFreeMemPtr s ::
            (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) ::
            truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState54]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc114_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState55 s).executionEnv.code
        (truthParamSuccessState55 s).machineState.pc =
          some (.PUSH1, .some ((⟨0x57⟩ : Ethereum.UInt256), 1))) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState55 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState55 s) =
      if (truthParamSuccessState55 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState56 s, .none) := by
  rw [Ethereum.EVM.step_push1 (truthParamSuccessState55 s) (⟨0x57⟩ : Ethereum.UInt256)]
  · have hoverflow :
        ¬ ((truthParamSuccessState55 s).machineState.stack.length - 0 + 1 > 1024) := by
      simp [truthParamSuccessState55]
    rw [if_neg hoverflow]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc116_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState56 s).executionEnv.code
        (truthParamSuccessState56 s).machineState.pc = some (.JUMP, .none))
    (hcontains :
      (Ethereum.EVM.D_J (truthParamSuccessState56 s).executionEnv.code ⟨0⟩).contains
        (⟨0x57⟩ : Ethereum.UInt256) = true) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState56 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState56 s) =
      if (truthParamSuccessState56 s).machineState.gasAvailable.toNat <
            GasConstants.Gmid then .error .OutOfGass
      else .ok (truthParamSuccessState57 s, .none) := by
  rw [Ethereum.EVM.step_jump (truthParamSuccessState56 s)]
  · have hstack :
        (truthParamSuccessState56 s).machineState.stack =
          (⟨0x57⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
            truthParamSuccessFreeMemPtr s :: (⟨0x75⟩ : Ethereum.UInt256) ::
            truthParamSuccessAbiEnd s :: truthParamSuccessFreeMemPtr s ::
            (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) ::
            truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState56, truthParamSuccessState55]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte, Bool.not_eq_true]
    rw [hcontains]
    rfl
  · exact hdecode

theorem truth_success_tail_X_pc108_to_pc116_of_xsteps
    (s : EVM.State)
    (f : Nat)
    (validJumps : Array Ethereum.UInt256)
    (xres : Except Ethereum.EVM.ExecutionException (Ethereum.ExecutionResult EVM.State))
    (h108 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState50 s) =
        .ok (truthParamSuccessState51 s, .none))
    (h110 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState51 s) =
        .ok (truthParamSuccessState52 s, .none))
    (h111 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState52 s) =
        .ok (truthParamSuccessState53 s, .none))
    (h112 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState53 s) =
        .ok (truthParamSuccessState54 s, .none))
    (h113 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState54 s) =
        .ok (truthParamSuccessState55 s, .none))
    (h114 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState55 s) =
        .ok (truthParamSuccessState56 s, .none))
    (h116 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState56 s) =
        .ok (truthParamSuccessState57 s, .none))
    (htail :
      Ethereum.EVM.X f validJumps (truthParamSuccessState57 s) = xres) :
    Ethereum.EVM.X (f + 7) validJumps (truthParamSuccessState50 s) = xres := by
  have hf :
      f + 7 = (((((((f + 1) + 1) + 1) + 1) + 1) + 1) + 1) := by
    omega
  rw [hf]
  truth_continue_step h108
  truth_continue_step h110
  truth_continue_step h111
  truth_continue_step h112
  truth_continue_step h113
  truth_continue_step h114
  truth_continue_step h116
  exact htail

theorem truth_success_tail_X_pc108_to_pc116_of_gas_guards
    (s : EVM.State)
    (f : Nat)
    (xres : Except Ethereum.EVM.ExecutionException (Ethereum.ExecutionResult EVM.State))
    (h_code : s.executionEnv.code = truthRuntimeBytecode)
    (hgas108 :
      ¬ (truthParamSuccessState50 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas110 :
      ¬ (truthParamSuccessState51 s).machineState.gasAvailable.toNat <
          GasConstants.Gbase)
    (hgas111 :
      ¬ (truthParamSuccessState52 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas112 :
      ¬ (truthParamSuccessState53 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas113 :
      ¬ (truthParamSuccessState54 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas114 :
      ¬ (truthParamSuccessState55 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas116 :
      ¬ (truthParamSuccessState56 s).machineState.gasAvailable.toNat <
          GasConstants.Gmid)
    (htail :
      Ethereum.EVM.X f (Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩)
        (truthParamSuccessState57 s) = xres) :
    Ethereum.EVM.X (f + 7) (Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩)
        (truthParamSuccessState50 s) = xres := by
  apply truth_success_tail_X_pc108_to_pc116_of_xsteps
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState50 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState50_code]]
    rw [truth_success_tail_xstep_pc108_core]
    · rw [if_neg hgas108]
    · rw [truthParamSuccessState50_code, h_code]
      exact truth_decode_pc108
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState51 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState51_code]]
    rw [truth_success_tail_xstep_pc110_core]
    · rw [if_neg hgas110]
    · rw [truthParamSuccessState51_code, h_code]
      exact truth_decode_pc110
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState52 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState52_code]]
    rw [truth_success_tail_xstep_pc111_core]
    · rw [if_neg hgas111]
    · rw [truthParamSuccessState52_code, h_code]
      exact truth_decode_pc111
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState53 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState53_code]]
    rw [truth_success_tail_xstep_pc112_core]
    · rw [if_neg hgas112]
    · rw [truthParamSuccessState53_code, h_code]
      exact truth_decode_pc112
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState54 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState54_code]]
    rw [truth_success_tail_xstep_pc113_core]
    · rw [if_neg hgas113]
    · rw [truthParamSuccessState54_code, h_code]
      exact truth_decode_pc113
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState55 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState55_code]]
    rw [truth_success_tail_xstep_pc114_core]
    · rw [if_neg hgas114]
    · rw [truthParamSuccessState55_code, h_code]
      exact truth_decode_pc114
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState56 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState56_code]]
    rw [truth_success_tail_xstep_pc116_core]
    · rw [if_neg hgas116]
    · rw [truthParamSuccessState56_code, h_code]
      exact truth_decode_pc116
    · rw [truthParamSuccessState56_code, h_code]
      exact truth_valid_jumpdest_57
  · exact htail

theorem truth_success_tail_X_pc100_to_pc107_of_xsteps
    (s : EVM.State)
    (f : Nat)
    (validJumps : Array Ethereum.UInt256)
    (xres : Except Ethereum.EVM.ExecutionException (Ethereum.ExecutionResult EVM.State))
    (h100 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState43 s) =
        .ok (truthParamSuccessState44 s, .none))
    (h101 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState44 s) =
        .ok (truthParamSuccessState45 s, .none))
    (h102 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState45 s) =
        .ok (truthParamSuccessState46 s, .none))
    (h104 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState46 s) =
        .ok (truthParamSuccessState47 s, .none))
    (h105 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState47 s) =
        .ok (truthParamSuccessState48 s, .none))
    (h106 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState48 s) =
        .ok (truthParamSuccessState49 s, .none))
    (h107 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState49 s) =
        .ok (truthParamSuccessState50 s, .none))
    (htail :
      Ethereum.EVM.X f validJumps (truthParamSuccessState50 s) = xres) :
    Ethereum.EVM.X (f + 7) validJumps (truthParamSuccessState43 s) = xres := by
  have hf :
      f + 7 = (((((((f + 1) + 1) + 1) + 1) + 1) + 1) + 1) := by
    omega
  rw [hf]
  truth_continue_step h100
  truth_continue_step h101
  truth_continue_step h102
  truth_continue_step h104
  truth_continue_step h105
  truth_continue_step h106
  truth_continue_step h107
  exact htail

theorem truth_success_tail_X_pc100_to_pc107_of_gas_guards
    (s : EVM.State)
    (f : Nat)
    (xres : Except Ethereum.EVM.ExecutionException (Ethereum.ExecutionResult EVM.State))
    (h_code : s.executionEnv.code = truthRuntimeBytecode)
    (hgas100 :
      ¬ (truthParamSuccessState43 s).machineState.gasAvailable.toNat <
          GasConstants.Gjumpdest)
    (hgas101 :
      ¬ (truthParamSuccessState44 s).machineState.gasAvailable.toNat <
          GasConstants.Gbase)
    (hgas102 :
      ¬ (truthParamSuccessState45 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas104 :
      ¬ (truthParamSuccessState46 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas105 :
      ¬ (truthParamSuccessState47 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas106 :
      ¬ (truthParamSuccessState48 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas107 :
      ¬ (truthParamSuccessState49 s).machineState.gasAvailable.toNat <
          GasConstants.Gbase)
    (htail :
      Ethereum.EVM.X f (Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩)
        (truthParamSuccessState50 s) = xres) :
    Ethereum.EVM.X (f + 7) (Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩)
        (truthParamSuccessState43 s) = xres := by
  apply truth_success_tail_X_pc100_to_pc107_of_xsteps
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState43 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState43_code]]
    rw [truth_success_tail_xstep_pc100_core]
    · rw [if_neg hgas100]
    · rw [truthParamSuccessState43_code, h_code]
      exact truth_decode_pc100
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState44 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState44_code]]
    rw [truth_success_tail_xstep_pc101_core]
    · rw [if_neg hgas101]
    · rw [truthParamSuccessState44_code, h_code]
      exact truth_decode_pc101
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState45 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState45_code]]
    rw [truth_success_tail_xstep_pc102_core]
    · rw [if_neg hgas102]
    · rw [truthParamSuccessState45_code, h_code]
      exact truth_decode_pc102
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState46 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState46_code]]
    rw [truth_success_tail_xstep_pc104_core]
    · rw [if_neg hgas104]
    · rw [truthParamSuccessState46_code, h_code]
      exact truth_decode_pc104
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState47 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState47_code]]
    rw [truth_success_tail_xstep_pc105_core]
    · rw [if_neg hgas105]
    · rw [truthParamSuccessState47_code, h_code]
      exact truth_decode_pc105
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState48 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState48_code]]
    rw [truth_success_tail_xstep_pc106_core]
    · rw [if_neg hgas106]
    · rw [truthParamSuccessState48_code, h_code]
      exact truth_decode_pc106
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState49 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState49_code]]
    rw [truth_success_tail_xstep_pc107_core]
    · rw [if_neg hgas107]
    · rw [truthParamSuccessState49_code, h_code]
      exact truth_decode_pc107
  · exact htail

end Truth
end Examples
end Act
