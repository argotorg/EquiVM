import Examples.TruthScratchTail5

set_option maxRecDepth 100000

namespace Act
namespace Examples
namespace Truth

def truthParamSuccessState86 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState85 s with
    machineState.gasAvailable :=
      (truthParamSuccessState85 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gjumpdest
    machineState.pc := (truthParamSuccessState85 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState85 s).machineState.execLength + 1 }

def truthParamSuccessState87 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState86 s with
    machineState.stack := (⟨0x40⟩ : Ethereum.UInt256) ::
      (truthParamSuccessState86 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamSuccessState86 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState86 s).machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := (truthParamSuccessState86 s).machineState.execLength + 1 }

def truthParamSuccessFinalFreeMemPtr (s : EVM.State) : Ethereum.UInt256 :=
  if (⟨0x40⟩ : Ethereum.UInt256).toNat ≥ (truthParamSuccessState87 s).machineState.memory.size ∨
      (⟨0x40⟩ : Ethereum.UInt256) ≥
        (truthParamSuccessState87 s).machineState.activeWords * ⟨32⟩ then
    ⟨0⟩
  else
    Ethereum.UInt256.ofNat
      (Ethereum.fromByteArrayBigEndian
        ((truthParamSuccessState87 s).machineState.memory.readWithPadding
          (⟨0x40⟩ : Ethereum.UInt256).toNat 32))

def truthParamSuccessState88 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState87 s with
    machineState.stack := truthParamSuccessFinalFreeMemPtr s :: truthParamSuccessAbiEnd s ::
      truthParamMismatchSelectorWord s :: []
    machineState.activeWords :=
      Ethereum.UInt256.ofNat
        (Ethereum.MachineState.M (truthParamSuccessState87 s).machineState.activeWords.toNat
          (⟨0x40⟩ : Ethereum.UInt256).toNat 32)
    machineState.gasAvailable :=
      ((truthParamSuccessState87 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost (truthParamSuccessState87 s) .MLOAD)) -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState87 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState87 s).machineState.execLength + 1 }

def truthParamSuccessReturnLength (s : EVM.State) : Ethereum.UInt256 :=
  Ethereum.UInt256.sub (truthParamSuccessAbiEnd s) (truthParamSuccessFinalFreeMemPtr s)

def truthParamSuccessState89 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState88 s with
    machineState.stack := truthParamSuccessFinalFreeMemPtr s ::
      truthParamSuccessFinalFreeMemPtr s :: truthParamSuccessAbiEnd s ::
      truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState88 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState88 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState88 s).machineState.execLength + 1 }

def truthParamSuccessState90 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState89 s with
    machineState.stack := truthParamSuccessAbiEnd s :: truthParamSuccessFinalFreeMemPtr s ::
      truthParamSuccessFinalFreeMemPtr s :: truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState89 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState89 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState89 s).machineState.execLength + 1 }

def truthParamSuccessState91 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState90 s with
    machineState.stack := truthParamSuccessReturnLength s :: truthParamSuccessFinalFreeMemPtr s ::
      truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState90 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState90 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState90 s).machineState.execLength + 1 }

def truthParamSuccessState92 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState91 s with
    machineState.stack := truthParamSuccessFinalFreeMemPtr s ::
      truthParamSuccessReturnLength s :: truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState91 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState91 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState91 s).machineState.execLength + 1 }

def truthParamSuccessFinalReturnData (s : EVM.State) : ByteArray :=
  (truthParamSuccessState92 s).machineState.memory.readWithPadding
    (truthParamSuccessFinalFreeMemPtr s).toNat (truthParamSuccessReturnLength s).toNat

def truthParamSuccessState93 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState92 s with
    machineState.stack := [truthParamMismatchSelectorWord s]
    machineState.H_return := truthParamSuccessFinalReturnData s
    machineState.activeWords :=
      Ethereum.UInt256.ofNat
        (Ethereum.MachineState.M (truthParamSuccessState92 s).machineState.activeWords.toNat
          (truthParamSuccessFinalFreeMemPtr s).toNat (truthParamSuccessReturnLength s).toNat)
    machineState.gasAvailable :=
      ((truthParamSuccessState92 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost (truthParamSuccessState92 s) .RETURN)) -
        Ethereum.UInt256.ofNat GasConstants.Gzero
    machineState.pc := (truthParamSuccessState92 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState92 s).machineState.execLength + 1 }

theorem truthParamSuccessState86_code (s : EVM.State) :
    (truthParamSuccessState86 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState86, truthParamSuccessState85_code]

theorem truthParamSuccessState87_code (s : EVM.State) :
    (truthParamSuccessState87 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState87, truthParamSuccessState86_code]

theorem truthParamSuccessState88_code (s : EVM.State) :
    (truthParamSuccessState88 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState88, truthParamSuccessState87_code]

theorem truthParamSuccessState89_code (s : EVM.State) :
    (truthParamSuccessState89 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState89, truthParamSuccessState88_code]

theorem truthParamSuccessState90_code (s : EVM.State) :
    (truthParamSuccessState90 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState90, truthParamSuccessState89_code]

theorem truthParamSuccessState91_code (s : EVM.State) :
    (truthParamSuccessState91 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState91, truthParamSuccessState90_code]

theorem truthParamSuccessState92_code (s : EVM.State) :
    (truthParamSuccessState92 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState92, truthParamSuccessState91_code]

theorem truthParamSuccessState93_code (s : EVM.State) :
    (truthParamSuccessState93 s).executionEnv.code = s.executionEnv.code := by
  rw [truthParamSuccessState93, truthParamSuccessState92_code]

theorem truth_success_tail_xstep_pc59_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState85 s).executionEnv.code
        (truthParamSuccessState85 s).machineState.pc = some (.JUMPDEST, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState85 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState85 s) =
      if (truthParamSuccessState85 s).machineState.gasAvailable.toNat <
            GasConstants.Gjumpdest then .error .OutOfGass
      else .ok (truthParamSuccessState86 s, .none) := by
  rw [Ethereum.EVM.step_jumpdest (truthParamSuccessState85 s)]
  · have hoverflow :
        ¬ ((truthParamSuccessState85 s).machineState.stack.length - 0 + 0 > 1024) := by
      simp [truthParamSuccessState85]
    rw [if_neg hoverflow]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc60_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState86 s).executionEnv.code
        (truthParamSuccessState86 s).machineState.pc =
          some (.PUSH1, some ((⟨0x40⟩ : Ethereum.UInt256), 1))) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState86 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState86 s) =
      if (truthParamSuccessState86 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState87 s, .none) := by
  rw [Ethereum.EVM.step_push1 (truthParamSuccessState86 s) (⟨0x40⟩ : Ethereum.UInt256)]
  · have hlen : (truthParamSuccessState85 s).machineState.stack.length - 0 + 1 = 3 := by
      simp [truthParamSuccessState85]
    simp only [truthParamSuccessState86, truthParamSuccessState87, hlen, Nat.reduceGT,
      ↓reduceIte]
  · exact hdecode

theorem truth_success_tail_xstep_pc62_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState87 s).executionEnv.code
        (truthParamSuccessState87 s).machineState.pc = some (.MLOAD, .none))
    (hmem :
      ¬ (truthParamSuccessState87 s).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost (truthParamSuccessState87 s) .MLOAD)
    (hgas :
      ¬ ((truthParamSuccessState87 s).machineState.gasAvailable -
          Ethereum.UInt256.ofNat
            (Ethereum.EVM.memoryExpansionCost (truthParamSuccessState87 s) .MLOAD)).toNat <
        GasConstants.Gverylow) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState87 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState87 s) =
      .ok (truthParamSuccessState88 s, .none) := by
  rw [Ethereum.EVM.step_mload (truthParamSuccessState87 s) hdecode]
  have hstack :
      (truthParamSuccessState87 s).machineState.stack =
        (⟨0x40⟩ : Ethereum.UInt256) :: truthParamSuccessAbiEnd s ::
          truthParamMismatchSelectorWord s :: [] := by
    simp [truthParamSuccessState87, truthParamSuccessState86, truthParamSuccessState85]
  rw [hstack]
  change
    (if (truthParamSuccessState87 s).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost (truthParamSuccessState87 s) .MLOAD then _ else _) = _
  rw [if_neg hmem]
  change
    (if ((truthParamSuccessState87 s).machineState.gasAvailable -
          Ethereum.UInt256.ofNat
            (Ethereum.EVM.memoryExpansionCost (truthParamSuccessState87 s) .MLOAD)).toNat <
        GasConstants.Gverylow then _ else _) = _
  rw [if_neg hgas]
  simp only [truthParamSuccessState87, truthParamSuccessState88,
    truthParamSuccessFinalFreeMemPtr, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub]
  have hoverflow : ¬ 3 > 1024 := by native_decide
  rw [if_neg hoverflow]

theorem truth_success_tail_xstep_pc63_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState88 s).executionEnv.code
        (truthParamSuccessState88 s).machineState.pc = some (.DUP1, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState88 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState88 s) =
      if (truthParamSuccessState88 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState89 s, .none) := by
  rw [Ethereum.EVM.step_dup1 (truthParamSuccessState88 s)]
  · have hstack :
        (truthParamSuccessState88 s).machineState.stack =
          truthParamSuccessFinalFreeMemPtr s :: truthParamSuccessAbiEnd s ::
            truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState88]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc64_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState89 s).executionEnv.code
        (truthParamSuccessState89 s).machineState.pc = some (.SWAP2, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState89 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState89 s) =
      if (truthParamSuccessState89 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState90 s, .none) := by
  rw [Ethereum.EVM.step_swap2 (truthParamSuccessState89 s)]
  · have hstack :
        (truthParamSuccessState89 s).machineState.stack =
          truthParamSuccessFinalFreeMemPtr s :: truthParamSuccessFinalFreeMemPtr s ::
            truthParamSuccessAbiEnd s :: truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState89]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc65_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState90 s).executionEnv.code
        (truthParamSuccessState90 s).machineState.pc = some (.SUB, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState90 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState90 s) =
      if (truthParamSuccessState90 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState91 s, .none) := by
  rw [Ethereum.EVM.step_sub (truthParamSuccessState90 s)]
  · have hstack :
        (truthParamSuccessState90 s).machineState.stack =
          truthParamSuccessAbiEnd s :: truthParamSuccessFinalFreeMemPtr s ::
            truthParamSuccessFinalFreeMemPtr s :: truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState90, truthParamSuccessState89]
    rw [hstack]
    simp only [truthParamSuccessState91, truthParamSuccessReturnLength, List.length_cons,
      List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT, ↓reduceIte]
  · exact hdecode

theorem truth_success_tail_xstep_pc66_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState91 s).executionEnv.code
        (truthParamSuccessState91 s).machineState.pc = some (.SWAP1, .none)) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState91 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState91 s) =
      if (truthParamSuccessState91 s).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok (truthParamSuccessState92 s, .none) := by
  rw [Ethereum.EVM.step_swap1 (truthParamSuccessState91 s)]
  · have hstack :
        (truthParamSuccessState91 s).machineState.stack =
          truthParamSuccessReturnLength s :: truthParamSuccessFinalFreeMemPtr s ::
            truthParamMismatchSelectorWord s :: [] := by
      simp [truthParamSuccessState91]
    rw [hstack]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGT,
      ↓reduceIte]
    rfl
  · exact hdecode

theorem truth_success_tail_xstep_pc67_core
    (s : EVM.State)
    (hdecode :
      Ethereum.EVM.decode (truthParamSuccessState92 s).executionEnv.code
        (truthParamSuccessState92 s).machineState.pc = some (.RETURN, .none))
    (hmem :
      ¬ (truthParamSuccessState92 s).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost (truthParamSuccessState92 s) .RETURN) :
    Ethereum.EVM.Xstep
        (Ethereum.EVM.D_J (truthParamSuccessState92 s).executionEnv.code ⟨0⟩)
        (truthParamSuccessState92 s) =
      .ok (truthParamSuccessState93 s, some (true, truthParamSuccessFinalReturnData s)) := by
  rw [Ethereum.EVM.step_return (truthParamSuccessState92 s) hdecode]
  have hstack :
      (truthParamSuccessState92 s).machineState.stack =
        truthParamSuccessFinalFreeMemPtr s :: truthParamSuccessReturnLength s ::
          truthParamMismatchSelectorWord s :: [] := by
    simp [truthParamSuccessState92]
  rw [hstack]
  change
    (if (truthParamSuccessState92 s).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost (truthParamSuccessState92 s) .RETURN then _ else _) = _
  rw [if_neg hmem]
  simp only [truthParamSuccessState92, truthParamSuccessState93,
    truthParamSuccessFinalReturnData, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub]
  have hoverflow : ¬ 1 > 1024 := by native_decide
  rw [if_neg hoverflow]

theorem truth_success_tail_X_pc59_to_pc67_of_xsteps
    (s : EVM.State)
    (f : Nat)
    (validJumps : Array Ethereum.UInt256)
    (h59 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState85 s) =
        .ok (truthParamSuccessState86 s, .none))
    (h60 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState86 s) =
        .ok (truthParamSuccessState87 s, .none))
    (h62 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState87 s) =
        .ok (truthParamSuccessState88 s, .none))
    (h63 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState88 s) =
        .ok (truthParamSuccessState89 s, .none))
    (h64 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState89 s) =
        .ok (truthParamSuccessState90 s, .none))
    (h65 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState90 s) =
        .ok (truthParamSuccessState91 s, .none))
    (h66 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState91 s) =
        .ok (truthParamSuccessState92 s, .none))
    (h67 :
      Ethereum.EVM.Xstep validJumps (truthParamSuccessState92 s) =
        .ok (truthParamSuccessState93 s, some (true, truthParamSuccessFinalReturnData s))) :
    Ethereum.EVM.X (f + 8) validJumps (truthParamSuccessState85 s) =
      .ok (.success (truthParamSuccessState93 s) (truthParamSuccessFinalReturnData s)) := by
  have hf :
      f + 8 = ((((((((f + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) := by
    omega
  rw [hf]
  truth_continue_step h59
  truth_continue_step h60
  truth_continue_step h62
  truth_continue_step h63
  truth_continue_step h64
  truth_continue_step h65
  truth_continue_step h66
  apply Ethereum.EVM.Xstep_X_X_halt_success
  exact h67

theorem truth_success_tail_X_pc59_to_pc67_of_gas_guards
    (s : EVM.State)
    (f : Nat)
    (h_code : s.executionEnv.code = truthRuntimeBytecode)
    (hgas59 :
      ¬ (truthParamSuccessState85 s).machineState.gasAvailable.toNat <
          GasConstants.Gjumpdest)
    (hgas60 :
      ¬ (truthParamSuccessState86 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hmem62 :
      ¬ (truthParamSuccessState87 s).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost (truthParamSuccessState87 s) .MLOAD)
    (hgas62 :
      ¬ ((truthParamSuccessState87 s).machineState.gasAvailable -
          Ethereum.UInt256.ofNat
            (Ethereum.EVM.memoryExpansionCost (truthParamSuccessState87 s) .MLOAD)).toNat <
        GasConstants.Gverylow)
    (hgas63 :
      ¬ (truthParamSuccessState88 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas64 :
      ¬ (truthParamSuccessState89 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas65 :
      ¬ (truthParamSuccessState90 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas66 :
      ¬ (truthParamSuccessState91 s).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hmem67 :
      ¬ (truthParamSuccessState92 s).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost (truthParamSuccessState92 s) .RETURN) :
    Ethereum.EVM.X (f + 8) (Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩)
        (truthParamSuccessState85 s) =
      .ok (.success (truthParamSuccessState93 s) (truthParamSuccessFinalReturnData s)) := by
  apply truth_success_tail_X_pc59_to_pc67_of_xsteps
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState85 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState85_code]]
    rw [truth_success_tail_xstep_pc59_core]
    · rw [if_neg hgas59]
    · rw [truthParamSuccessState85_code, h_code]
      exact truth_decode_pc59
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState86 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState86_code]]
    rw [truth_success_tail_xstep_pc60_core]
    · rw [if_neg hgas60]
    · rw [truthParamSuccessState86_code, h_code]
      exact truth_decode_pc60
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState87 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState87_code]]
    rw [truth_success_tail_xstep_pc62_core]
    · rw [truthParamSuccessState87_code, h_code]
      exact truth_decode_pc62
    · exact hmem62
    · exact hgas62
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState88 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState88_code]]
    rw [truth_success_tail_xstep_pc63_core]
    · rw [if_neg hgas63]
    · rw [truthParamSuccessState88_code, h_code]
      exact truth_decode_pc63
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState89 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState89_code]]
    rw [truth_success_tail_xstep_pc64_core]
    · rw [if_neg hgas64]
    · rw [truthParamSuccessState89_code, h_code]
      exact truth_decode_pc64
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState90 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState90_code]]
    rw [truth_success_tail_xstep_pc65_core]
    · rw [if_neg hgas65]
    · rw [truthParamSuccessState90_code, h_code]
      exact truth_decode_pc65
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState91 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState91_code]]
    rw [truth_success_tail_xstep_pc66_core]
    · rw [if_neg hgas66]
    · rw [truthParamSuccessState91_code, h_code]
      exact truth_decode_pc66
  · rw [show
        Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩ =
          Ethereum.EVM.D_J (truthParamSuccessState92 s).executionEnv.code ⟨0⟩ by
        rw [truthParamSuccessState92_code]]
    rw [truth_success_tail_xstep_pc67_core]
    · rw [truthParamSuccessState92_code, h_code]
      exact truth_decode_pc67
    · exact hmem67

end Truth
end Examples
end Act
