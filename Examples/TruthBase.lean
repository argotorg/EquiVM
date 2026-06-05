import Act.Dispatch
import ABI.Decode
import ABI.Encode
import Act.Equiv
import Ethereum.Theory.OpcodeLemmas
import Ethereum.Theory.ProgressLemmas
import Mathlib.Algebra.Group.Fin.Basic

namespace Act
namespace Examples
namespace Truth

open ABI

def truthRuntimeBytecode : ByteArray :=
  ⟨#[
    0x60, 0x80, 0x60, 0x40, 0x52, 0x34, 0x80, 0x15, 0x60, 0x0e, 0x57, 0x5f,
    0x5f, 0xfd, 0x5b, 0x50, 0x60, 0x04, 0x36, 0x10, 0x60, 0x26, 0x57, 0x5f,
    0x35, 0x60, 0xe0, 0x1c, 0x80, 0x63, 0x9e, 0x9f, 0x51, 0xd2, 0x14, 0x60,
    0x2a, 0x57, 0x5b, 0x5f, 0x5f, 0xfd, 0x5b, 0x60, 0x30, 0x60, 0x44, 0x56,
    0x5b, 0x60, 0x40, 0x51, 0x60, 0x3b, 0x91, 0x90, 0x60, 0x64, 0x56, 0x5b,
    0x60, 0x40, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3, 0x5b, 0x5f, 0x60, 0x01,
    0x90, 0x50, 0x90, 0x56, 0x5b, 0x5f, 0x81, 0x15, 0x15, 0x90, 0x50, 0x91,
    0x90, 0x50, 0x56, 0x5b, 0x60, 0x5e, 0x81, 0x60, 0x4c, 0x56, 0x5b, 0x82,
    0x52, 0x50, 0x50, 0x56, 0x5b, 0x5f, 0x60, 0x20, 0x82, 0x01, 0x90, 0x50,
    0x60, 0x75, 0x5f, 0x83, 0x01, 0x84, 0x60, 0x57, 0x56, 0x5b, 0x92, 0x91,
    0x50, 0x50, 0x56
  ]⟩

def truthSelector : ByteArray :=
  ⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩

def truthCallData : ByteArray :=
  truthSelector

def truthShortCallData : ByteArray :=
  ⟨#[]⟩

def truthMismatchCallData : ByteArray :=
  ⟨#[0xde, 0xad, 0xbe, 0xef]⟩

def truthReturnData : ByteArray :=
  ByteArray.mk (EVM.UInt256.toBytes (⟨1⟩ : Ethereum.UInt256)).toArray

def truthTransition : TransitionDecl :=
  { name := "truth"
    params := []
    returnType := some (.elem .bool)
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0))
        ,
        .return (.boolLit true) ] }

def truthContract : ContractDecl :=
  { name := "Truth"
    storage := []
    ctor := { params := [], body := [] }
    transitions := [truthTransition] }

def emptyStorageLayout : StorageLayout :=
  { layout := fun _ => none }

def truthConfig : Config :=
  { storage := emptyStorageLayout
    externalABI := defaultExternalCallABI }

def truthExecutionEnv : Ethereum.ExecutionEnv :=
  { (default : Ethereum.ExecutionEnv) with
      code := truthRuntimeBytecode
      calldata := truthCallData
      weiValue := (⟨0⟩ : Ethereum.UInt256)
      depth := 0 }

def truthInitialState : EVM.State :=
  { (default : EVM.State) with
      executionEnv := truthExecutionEnv
      machineState.gasAvailable := (⟨100000⟩ : Ethereum.UInt256) }

def truthShortExecutionEnv : Ethereum.ExecutionEnv :=
  { truthExecutionEnv with
      calldata := truthShortCallData }

def truthShortInitialState : EVM.State :=
  { truthInitialState with
      executionEnv := truthShortExecutionEnv }

def truthMismatchExecutionEnv : Ethereum.ExecutionEnv :=
  { truthExecutionEnv with
      calldata := truthMismatchCallData }

def truthMismatchInitialState : EVM.State :=
  { truthInitialState with
      executionEnv := truthMismatchExecutionEnv }

def truthFreshState
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) : EVM.State :=
  { (default : EVM.State) with
      accountMap := σ
      σ₀ := σ₀
      executionEnv := I
      substate := A
      createdAccounts := createdAccounts
      machineState.gasAvailable := g
      blocks := blocks
      genesisBlockHeader := genesisBlockHeader }

theorem truth_Xi_eq_X_fresh
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      (do
        let result ← Ethereum.EVM.X (g.toNat + 1) (Ethereum.EVM.D_J I.code ⟨0⟩)
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
        match result with
        | Ethereum.ExecutionResult.success evmState' o =>
            .ok (Ethereum.ExecutionResult.success
              (evmState'.createdAccounts, evmState'.accountMap,
                evmState'.machineState.gasAvailable, evmState'.substate) o)
        | Ethereum.ExecutionResult.revert g' o =>
            .ok (Ethereum.ExecutionResult.revert g' o)) := by
  unfold Ethereum.EVM.Ξ truthFreshState
  rfl


theorem truth_Xi_revert_of_X_fresh_revert
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g g' : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (o : ByteArray)
    (hX :
      Ethereum.EVM.X (g.toNat + 1) (Ethereum.EVM.D_J I.code ⟨0⟩)
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
        .ok (.revert g' o)) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert g' o) := by
  rw [truth_Xi_eq_X_fresh]
  rw [hX]
  simp [bind, Except.bind]

theorem truth_Xi_success_of_X_fresh_success
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (s' : EVM.State)
    (o : ByteArray)
    (h_createdAccounts : s'.createdAccounts = createdAccounts)
    (h_accountMap : s'.accountMap = σ)
    (h_substate : s'.substate = A)
    (hX :
      Ethereum.EVM.X (g.toNat + 1) (Ethereum.EVM.D_J I.code ⟨0⟩)
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
        .ok (.success s' o)) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.success (createdAccounts, σ, s'.machineState.gasAvailable, A) o) := by
  rw [truth_Xi_eq_X_fresh]
  rw [hX]
  simp [bind, Except.bind, h_createdAccounts, h_accountMap, h_substate]

theorem truth_Xi_outOfGas_of_X_fresh_outOfGas
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (hX :
      Ethereum.EVM.X (g.toNat + 1) (Ethereum.EVM.D_J I.code ⟨0⟩)
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
        .error .OutOfGass) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass := by
  rw [truth_Xi_eq_X_fresh]
  rw [hX]
  simp [bind, Except.bind]

theorem truth_Xi_outOfGas_of_fresh_Xstep_outOfGas
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (hstep :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
        .error .OutOfGass) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass := by
  apply truth_Xi_outOfGas_of_X_fresh_outOfGas
  unfold Ethereum.EVM.X
  simp [hstep, bind, Except.bind]

def truthValidJumps : Array Ethereum.UInt256 :=
  Ethereum.EVM.D_J truthRuntimeBytecode ⟨0⟩

def truthParamState1 (s : EVM.State) : EVM.State :=
  { s with
    machineState.stack := (⟨0x80⟩ : Ethereum.UInt256) :: s.machineState.stack
    machineState.gasAvailable :=
      s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := s.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := s.machineState.execLength + 1 }

def truthParamState2 (s : EVM.State) : EVM.State :=
  { truthParamState1 s with
    machineState.stack := (⟨0x40⟩ : Ethereum.UInt256) :: (truthParamState1 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamState1 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamState1 s).machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := (truthParamState1 s).machineState.execLength + 1 }

def truthParamState3 (s : EVM.State) : EVM.State :=
  { truthParamState2 s with
    machineState.stack := []
    machineState.memory :=
      (⟨0x80⟩ : Ethereum.UInt256).toByteArray.write 0
        (truthParamState2 s).machineState.memory 0x40 32
    machineState.activeWords :=
      Ethereum.UInt256.ofNat
        (Ethereum.MachineState.M (truthParamState2 s).machineState.activeWords.toNat 0x40 32)
    machineState.gasAvailable :=
      ((truthParamState2 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost (truthParamState2 s) .MSTORE)) -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamState2 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamState2 s).machineState.execLength + 1 }

def truthParamState4 (s : EVM.State) : EVM.State :=
  { truthParamState3 s with
    machineState.stack := (truthParamState3 s).executionEnv.weiValue ::
      (truthParamState3 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamState3 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := (truthParamState3 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamState3 s).machineState.execLength + 1 }

def truthParamState5 (s : EVM.State) : EVM.State :=
  { truthParamState4 s with
    machineState.stack := (truthParamState4 s).executionEnv.weiValue ::
      (truthParamState4 s).executionEnv.weiValue :: []
    machineState.gasAvailable :=
      (truthParamState4 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamState4 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamState4 s).machineState.execLength + 1 }

def truthParamState6 (s : EVM.State) : EVM.State :=
  { truthParamState5 s with
    machineState.stack := Ethereum.UInt256.isZero (truthParamState5 s).executionEnv.weiValue ::
      (truthParamState5 s).executionEnv.weiValue :: []
    machineState.gasAvailable :=
      (truthParamState5 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamState5 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamState5 s).machineState.execLength + 1 }

def truthParamState7 (s : EVM.State) : EVM.State :=
  { truthParamState6 s with
    machineState.stack := (⟨0x0e⟩ : Ethereum.UInt256) :: (truthParamState6 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamState6 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamState6 s).machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := (truthParamState6 s).machineState.execLength + 1 }

def truthParamNonpayableState8 (s : EVM.State) : EVM.State :=
  { truthParamState7 s with
    machineState.stack := [(truthParamState7 s).executionEnv.weiValue]
    machineState.gasAvailable :=
      (truthParamState7 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Ghigh
    machineState.pc := (truthParamState7 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamState7 s).machineState.execLength + 1 }

def truthParamNonpayableState9 (s : EVM.State) : EVM.State :=
  { truthParamNonpayableState8 s with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) ::
      (truthParamNonpayableState8 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamNonpayableState8 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := (truthParamNonpayableState8 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamNonpayableState8 s).machineState.execLength + 1 }

def truthParamNonpayableState10 (s : EVM.State) : EVM.State :=
  { truthParamNonpayableState9 s with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) ::
      (truthParamNonpayableState9 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamNonpayableState9 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := (truthParamNonpayableState9 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamNonpayableState9 s).machineState.execLength + 1 }

def truthParamNonpayableReturnData (s : EVM.State) : ByteArray :=
  (truthParamNonpayableState10 s).machineState.memory.readWithPadding 0 0

def truthParamNonpayableState11 (s : EVM.State) : EVM.State :=
  { truthParamNonpayableState10 s with
    machineState.stack := [(truthParamNonpayableState10 s).executionEnv.weiValue]
    machineState.H_return := truthParamNonpayableReturnData s
    machineState.activeWords :=
      Ethereum.UInt256.ofNat
        (Ethereum.MachineState.M (truthParamNonpayableState10 s).machineState.activeWords.toNat 0 0)
    machineState.gasAvailable :=
      ((truthParamNonpayableState10 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost
          (truthParamNonpayableState10 s) .REVERT)) -
        Ethereum.UInt256.ofNat GasConstants.Gzero
    machineState.pc := (truthParamNonpayableState10 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamNonpayableState10 s).machineState.execLength + 1 }

def truthParamPayableState8 (s : EVM.State) : EVM.State :=
  { truthParamState7 s with
    machineState.stack := [(truthParamState7 s).executionEnv.weiValue]
    machineState.gasAvailable :=
      (truthParamState7 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Ghigh
    machineState.pc := (⟨0x0e⟩ : Ethereum.UInt256)
    machineState.execLength := (truthParamState7 s).machineState.execLength + 1 }

def truthParamPayableState9 (s : EVM.State) : EVM.State :=
  { truthParamPayableState8 s with
    machineState.gasAvailable :=
      (truthParamPayableState8 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gjumpdest
    machineState.pc := (truthParamPayableState8 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamPayableState8 s).machineState.execLength + 1 }

def truthParamPayableState10 (s : EVM.State) : EVM.State :=
  { truthParamPayableState9 s with
    machineState.stack := []
    machineState.gasAvailable :=
      (truthParamPayableState9 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := (truthParamPayableState9 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamPayableState9 s).machineState.execLength + 1 }

def truthParamPayableState11 (s : EVM.State) : EVM.State :=
  { truthParamPayableState10 s with
    machineState.stack := (⟨0x04⟩ : Ethereum.UInt256) ::
      (truthParamPayableState10 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamPayableState10 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamPayableState10 s).machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := (truthParamPayableState10 s).machineState.execLength + 1 }

def truthParamPayableState12 (s : EVM.State) : EVM.State :=
  { truthParamPayableState11 s with
    machineState.stack :=
      Ethereum.UInt256.ofNat (truthParamPayableState11 s).executionEnv.calldata.size ::
      (truthParamPayableState11 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamPayableState11 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := (truthParamPayableState11 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamPayableState11 s).machineState.execLength + 1 }

def truthParamPayableState13 (s : EVM.State) : EVM.State :=
  { truthParamPayableState12 s with
    machineState.stack :=
      Ethereum.UInt256.lt
        (Ethereum.UInt256.ofNat (truthParamPayableState12 s).executionEnv.calldata.size)
        (⟨0x04⟩ : Ethereum.UInt256) :: []
    machineState.gasAvailable :=
      (truthParamPayableState12 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamPayableState12 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamPayableState12 s).machineState.execLength + 1 }

def truthParamPayableState14 (s : EVM.State) : EVM.State :=
  { truthParamPayableState13 s with
    machineState.stack := (⟨0x26⟩ : Ethereum.UInt256) ::
      (truthParamPayableState13 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamPayableState13 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamPayableState13 s).machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := (truthParamPayableState13 s).machineState.execLength + 1 }

def truthParamShortState15 (s : EVM.State) : EVM.State :=
  { truthParamPayableState14 s with
    machineState.stack := []
    machineState.gasAvailable :=
      (truthParamPayableState14 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Ghigh
    machineState.pc := (⟨0x26⟩ : Ethereum.UInt256)
    machineState.execLength := (truthParamPayableState14 s).machineState.execLength + 1 }

def truthParamShortState16 (s : EVM.State) : EVM.State :=
  { truthParamShortState15 s with
    machineState.gasAvailable :=
      (truthParamShortState15 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gjumpdest
    machineState.pc := (truthParamShortState15 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamShortState15 s).machineState.execLength + 1 }

def truthParamShortState17 (s : EVM.State) : EVM.State :=
  { truthParamShortState16 s with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) ::
      (truthParamShortState16 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamShortState16 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := (truthParamShortState16 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamShortState16 s).machineState.execLength + 1 }

def truthParamShortState18 (s : EVM.State) : EVM.State :=
  { truthParamShortState17 s with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) ::
      (truthParamShortState17 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamShortState17 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := (truthParamShortState17 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamShortState17 s).machineState.execLength + 1 }

def truthParamShortReturnData (s : EVM.State) : ByteArray :=
  (truthParamShortState18 s).machineState.memory.readWithPadding 0 0

def truthParamShortState19 (s : EVM.State) : EVM.State :=
  { truthParamShortState18 s with
    machineState.stack := []
    machineState.H_return := truthParamShortReturnData s
    machineState.activeWords :=
      Ethereum.UInt256.ofNat
        (Ethereum.MachineState.M (truthParamShortState18 s).machineState.activeWords.toNat 0 0)
    machineState.gasAvailable :=
      ((truthParamShortState18 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost
          (truthParamShortState18 s) .REVERT)) -
        Ethereum.UInt256.ofNat GasConstants.Gzero
    machineState.pc := (truthParamShortState18 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamShortState18 s).machineState.execLength + 1 }

theorem truth_fresh_xstep_pc0
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
      if g.toNat < GasConstants.Gverylow then .error .OutOfGass
      else .ok
        (truthParamState1
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).executionEnv.code
          ⟨0⟩ := by
    simp [truthFreshState]
  rw [hvalid]
  rw [Ethereum.EVM.step_push1
    (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
    (⟨0x80⟩ : Ethereum.UInt256)]
  · have hoverflow :
        ¬ (1024 <
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).machineState.stack.length -
            0 + 1) := by
      simp [truthFreshState]
      native_decide
    rw [if_neg hoverflow]
    simp [truthFreshState, truthParamState1]
  · simp [truthFreshState, h_code]
    native_decide

theorem truth_fresh_xstep_pc2
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState1
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamState1
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok
        (truthParamState2
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J
          (truthParamState1
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).executionEnv.code
          ⟨0⟩ := by
    simp [truthFreshState, truthParamState1]
  rw [hvalid]
  rw [Ethereum.EVM.step_push1
    (truthParamState1
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))
    (⟨0x40⟩ : Ethereum.UInt256)]
  · have hoverflow :
        ¬ (1024 <
          (truthParamState1
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.stack.length -
            0 + 1) := by
      simp [truthFreshState, truthParamState1]
      native_decide
    rw [if_neg hoverflow]
    simp [truthFreshState, truthParamState1, truthParamState2]
  · simp [truthFreshState, truthParamState1, h_code]
    native_decide

theorem truth_fresh_xstep_pc4
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState2
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamState2
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            Ethereum.EVM.memoryExpansionCost
              (truthParamState2
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE then
        .error .OutOfGass
      else if
          ((truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
              Ethereum.UInt256.ofNat
                (Ethereum.EVM.memoryExpansionCost
                  (truthParamState2
                    (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)).toNat <
            GasConstants.Gverylow then
        .error .OutOfGass
      else .ok
        (truthParamState3
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J
          (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).executionEnv.code
          ⟨0⟩ := by
    simp [truthFreshState, truthParamState1, truthParamState2]
  rw [hvalid]
  rw [Ethereum.EVM.step_mstore
    (truthParamState2
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))]
  · have hdefault_stack : (default : EVM.State).machineState.stack = [] := by
      native_decide
    have h64mod : 64 % Ethereum.UInt256.size = 64 := by
      native_decide
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      Ethereum.MachineState.M, Ethereum.UInt256.toNat, hdefault_stack, h64mod]
  · simp [truthFreshState, truthParamState1, truthParamState2, h_code]
    native_decide

theorem truth_fresh_xstep_pc5
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState3
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamState3
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gbase then .error .OutOfGass
      else .ok
        (truthParamState4
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J
          (truthParamState3
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).executionEnv.code
          ⟨0⟩ := by
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3]
  rw [hvalid]
  rw [Ethereum.EVM.step_callvalue
    (truthParamState3
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))]
  · have hoverflow :
        ¬ (1024 <
          (truthParamState3
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.stack.length -
            0 + 1) := by
      simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3]
    rw [if_neg hoverflow]
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3, h_code,
      Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_xstep_pc6
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState4
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamState4
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok
        (truthParamState5
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J
          (truthParamState4
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).executionEnv.code
          ⟨0⟩ := by
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4]
  rw [hvalid]
  rw [Ethereum.EVM.step_dup1
    (truthParamState4
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, h_code, Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_xstep_pc7
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState5
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamState5
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok
        (truthParamState6
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J
          (truthParamState5
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).executionEnv.code
          ⟨0⟩ := by
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5]
  rw [hvalid]
  rw [Ethereum.EVM.step_iszero
    (truthParamState5
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, h_code, Ethereum.MachineState.M,
      Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_xstep_pc8
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState6
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamState6
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok
        (truthParamState7
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J
          (truthParamState6
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).executionEnv.code
          ⟨0⟩ := by
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6]
  rw [hvalid]
  rw [Ethereum.EVM.step_push1
    (truthParamState6
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))
    (⟨0x0e⟩ : Ethereum.UInt256)]
  · have hoverflow :
        ¬ (1024 <
          (truthParamState6
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.stack.length -
            0 + 1) := by
      simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
        truthParamState4, truthParamState5, truthParamState6]
    rw [if_neg hoverflow]
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, h_code,
      Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

def truthShortState1 : EVM.State :=
  { truthShortInitialState with
    machineState.stack := (⟨0x80⟩ : Ethereum.UInt256) :: truthShortInitialState.machineState.stack
    machineState.gasAvailable :=
      truthShortInitialState.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthShortInitialState.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := truthShortInitialState.machineState.execLength + 1 }

def truthShortState2 : EVM.State :=
  { truthShortState1 with
    machineState.stack := (⟨0x40⟩ : Ethereum.UInt256) :: truthShortState1.machineState.stack
    machineState.gasAvailable :=
      truthShortState1.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthShortState1.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := truthShortState1.machineState.execLength + 1 }

def truthShortState3 : EVM.State :=
  { truthShortState2 with
    machineState.stack := []
    machineState.memory :=
      (⟨0x80⟩ : Ethereum.UInt256).toByteArray.write 0
        truthShortState2.machineState.memory 0x40 32
    machineState.activeWords :=
      Ethereum.UInt256.ofNat
        (Ethereum.MachineState.M truthShortState2.machineState.activeWords.toNat 0x40 32)
    machineState.gasAvailable :=
      (truthShortState2.machineState.gasAvailable -
        Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost truthShortState2 .MSTORE)) -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthShortState2.machineState.pc + ⟨1⟩
    machineState.execLength := truthShortState2.machineState.execLength + 1 }

def truthShortState4 : EVM.State :=
  { truthShortState3 with
    machineState.stack := truthShortState3.executionEnv.weiValue :: truthShortState3.machineState.stack
    machineState.gasAvailable :=
      truthShortState3.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := truthShortState3.machineState.pc + ⟨1⟩
    machineState.execLength := truthShortState3.machineState.execLength + 1 }

def truthShortState5 : EVM.State :=
  { truthShortState4 with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) :: []
    machineState.gasAvailable :=
      truthShortState4.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthShortState4.machineState.pc + ⟨1⟩
    machineState.execLength := truthShortState4.machineState.execLength + 1 }

def truthShortState6 : EVM.State :=
  { truthShortState5 with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) :: []
    machineState.gasAvailable :=
      truthShortState5.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthShortState5.machineState.pc + ⟨1⟩
    machineState.execLength := truthShortState5.machineState.execLength + 1 }

def truthShortState7 : EVM.State :=
  { truthShortState6 with
    machineState.stack := (⟨0x0e⟩ : Ethereum.UInt256) :: truthShortState6.machineState.stack
    machineState.gasAvailable :=
      truthShortState6.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthShortState6.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := truthShortState6.machineState.execLength + 1 }

def truthShortState8 : EVM.State :=
  { truthShortState7 with
    machineState.stack := [(⟨0⟩ : Ethereum.UInt256)]
    machineState.gasAvailable :=
      truthShortState7.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Ghigh
    machineState.pc := (⟨0x0e⟩ : Ethereum.UInt256)
    machineState.execLength := truthShortState7.machineState.execLength + 1 }

def truthShortState9 : EVM.State :=
  { truthShortState8 with
    machineState.gasAvailable :=
      truthShortState8.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gjumpdest
    machineState.pc := truthShortState8.machineState.pc + ⟨1⟩
    machineState.execLength := truthShortState8.machineState.execLength + 1 }

def truthShortState10 : EVM.State :=
  { truthShortState9 with
    machineState.stack := []
    machineState.gasAvailable :=
      truthShortState9.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := truthShortState9.machineState.pc + ⟨1⟩
    machineState.execLength := truthShortState9.machineState.execLength + 1 }

def truthShortState11 : EVM.State :=
  { truthShortState10 with
    machineState.stack := (⟨0x04⟩ : Ethereum.UInt256) :: truthShortState10.machineState.stack
    machineState.gasAvailable :=
      truthShortState10.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthShortState10.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := truthShortState10.machineState.execLength + 1 }

def truthShortState12 : EVM.State :=
  { truthShortState11 with
    machineState.stack := Ethereum.UInt256.ofNat truthShortState11.executionEnv.calldata.size ::
      truthShortState11.machineState.stack
    machineState.gasAvailable :=
      truthShortState11.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := truthShortState11.machineState.pc + ⟨1⟩
    machineState.execLength := truthShortState11.machineState.execLength + 1 }

def truthShortState13 : EVM.State :=
  { truthShortState12 with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: []
    machineState.gasAvailable :=
      truthShortState12.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthShortState12.machineState.pc + ⟨1⟩
    machineState.execLength := truthShortState12.machineState.execLength + 1 }

def truthShortState14 : EVM.State :=
  { truthShortState13 with
    machineState.stack := (⟨0x26⟩ : Ethereum.UInt256) :: truthShortState13.machineState.stack
    machineState.gasAvailable :=
      truthShortState13.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthShortState13.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := truthShortState13.machineState.execLength + 1 }

def truthShortState15 : EVM.State :=
  { truthShortState14 with
    machineState.stack := []
    machineState.gasAvailable :=
      truthShortState14.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Ghigh
    machineState.pc := (⟨0x26⟩ : Ethereum.UInt256)
    machineState.execLength := truthShortState14.machineState.execLength + 1 }

def truthShortState16 : EVM.State :=
  { truthShortState15 with
    machineState.gasAvailable :=
      truthShortState15.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gjumpdest
    machineState.pc := truthShortState15.machineState.pc + ⟨1⟩
    machineState.execLength := truthShortState15.machineState.execLength + 1 }

def truthShortState17 : EVM.State :=
  { truthShortState16 with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) :: truthShortState16.machineState.stack
    machineState.gasAvailable :=
      truthShortState16.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := truthShortState16.machineState.pc + ⟨1⟩
    machineState.execLength := truthShortState16.machineState.execLength + 1 }

def truthShortState18 : EVM.State :=
  { truthShortState17 with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) :: truthShortState17.machineState.stack
    machineState.gasAvailable :=
      truthShortState17.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := truthShortState17.machineState.pc + ⟨1⟩
    machineState.execLength := truthShortState17.machineState.execLength + 1 }

def truthShortReturnData : ByteArray :=
  truthShortState18.machineState.memory.readWithPadding 0 0

def truthShortState19 : EVM.State :=
  { truthShortState18 with
    machineState.stack := []
    machineState.H_return := truthShortReturnData
    machineState.activeWords :=
      Ethereum.UInt256.ofNat
        (Ethereum.MachineState.M truthShortState18.machineState.activeWords.toNat 0 0)
    machineState.gasAvailable :=
      (truthShortState18.machineState.gasAvailable -
        Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost truthShortState18 .REVERT)) -
        Ethereum.UInt256.ofNat GasConstants.Gzero
    machineState.pc := truthShortState18.machineState.pc + ⟨1⟩
    machineState.execLength := truthShortState18.machineState.execLength + 1 }

def truthState1 : EVM.State :=
  { truthInitialState with
    machineState.stack := (⟨0x80⟩ : Ethereum.UInt256) :: truthInitialState.machineState.stack
    machineState.gasAvailable :=
      truthInitialState.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthInitialState.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := truthInitialState.machineState.execLength + 1 }

def truthState2 : EVM.State :=
  { truthState1 with
    machineState.stack := (⟨0x40⟩ : Ethereum.UInt256) :: truthState1.machineState.stack
    machineState.gasAvailable :=
      truthState1.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState1.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := truthState1.machineState.execLength + 1 }

def truthState3 : EVM.State :=
  { truthState2 with
    machineState.stack := []
    machineState.memory :=
      (⟨0x80⟩ : Ethereum.UInt256).toByteArray.write 0
        truthState2.machineState.memory 0x40 32
    machineState.activeWords :=
      Ethereum.UInt256.ofNat
        (Ethereum.MachineState.M truthState2.machineState.activeWords.toNat 0x40 32)
    machineState.gasAvailable :=
      (truthState2.machineState.gasAvailable -
        Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost truthState2 .MSTORE)) -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState2.machineState.pc + ⟨1⟩
    machineState.execLength := truthState2.machineState.execLength + 1 }

def truthState4 : EVM.State :=
  { truthState3 with
    machineState.stack := truthState3.executionEnv.weiValue :: truthState3.machineState.stack
    machineState.gasAvailable :=
      truthState3.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := truthState3.machineState.pc + ⟨1⟩
    machineState.execLength := truthState3.machineState.execLength + 1 }

def truthState5 : EVM.State :=
  { truthState4 with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) :: []
    machineState.gasAvailable :=
      truthState4.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState4.machineState.pc + ⟨1⟩
    machineState.execLength := truthState4.machineState.execLength + 1 }

def truthState6 : EVM.State :=
  { truthState5 with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) :: []
    machineState.gasAvailable :=
      truthState5.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState5.machineState.pc + ⟨1⟩
    machineState.execLength := truthState5.machineState.execLength + 1 }

def truthState7 : EVM.State :=
  { truthState6 with
    machineState.stack := (⟨0x0e⟩ : Ethereum.UInt256) :: truthState6.machineState.stack
    machineState.gasAvailable :=
      truthState6.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState6.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := truthState6.machineState.execLength + 1 }

def truthState8 : EVM.State :=
  { truthState7 with
    machineState.stack := [(⟨0⟩ : Ethereum.UInt256)]
    machineState.gasAvailable :=
      truthState7.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Ghigh
    machineState.pc := (⟨0x0e⟩ : Ethereum.UInt256)
    machineState.execLength := truthState7.machineState.execLength + 1 }

def truthState9 : EVM.State :=
  { truthState8 with
    machineState.gasAvailable :=
      truthState8.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gjumpdest
    machineState.pc := truthState8.machineState.pc + ⟨1⟩
    machineState.execLength := truthState8.machineState.execLength + 1 }

def truthState10 : EVM.State :=
  { truthState9 with
    machineState.stack := []
    machineState.gasAvailable :=
      truthState9.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := truthState9.machineState.pc + ⟨1⟩
    machineState.execLength := truthState9.machineState.execLength + 1 }

def truthState11 : EVM.State :=
  { truthState10 with
    machineState.stack := (⟨0x04⟩ : Ethereum.UInt256) :: truthState10.machineState.stack
    machineState.gasAvailable :=
      truthState10.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState10.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := truthState10.machineState.execLength + 1 }

def truthState12 : EVM.State :=
  { truthState11 with
    machineState.stack := Ethereum.UInt256.ofNat truthState11.executionEnv.calldata.size ::
      truthState11.machineState.stack
    machineState.gasAvailable :=
      truthState11.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := truthState11.machineState.pc + ⟨1⟩
    machineState.execLength := truthState11.machineState.execLength + 1 }

def truthState13 : EVM.State :=
  { truthState12 with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) :: []
    machineState.gasAvailable :=
      truthState12.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState12.machineState.pc + ⟨1⟩
    machineState.execLength := truthState12.machineState.execLength + 1 }

def truthState14 : EVM.State :=
  { truthState13 with
    machineState.stack := (⟨0x26⟩ : Ethereum.UInt256) :: truthState13.machineState.stack
    machineState.gasAvailable :=
      truthState13.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState13.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := truthState13.machineState.execLength + 1 }

def truthState15 : EVM.State :=
  { truthState14 with
    machineState.stack := []
    machineState.gasAvailable :=
      truthState14.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Ghigh
    machineState.pc := truthState14.machineState.pc + ⟨1⟩
    machineState.execLength := truthState14.machineState.execLength + 1 }

def truthState16 : EVM.State :=
  { truthState15 with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) :: truthState15.machineState.stack
    machineState.gasAvailable :=
      truthState15.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := truthState15.machineState.pc + ⟨1⟩
    machineState.execLength := truthState15.machineState.execLength + 1 }

def truthCalldataWord : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray <| truthState16.executionEnv.calldata.readBytes 0 32

axiom truth_byteArray_zeroes_eq (n : USize) :
  ffi.ByteArray.zeroes n = ByteArray.mk (Array.mk (List.replicate n.toNat 0))

def truthState17 : EVM.State :=
  { truthState16 with
    machineState.stack := truthCalldataWord :: []
    machineState.gasAvailable :=
      truthState16.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState16.machineState.pc + ⟨1⟩
    machineState.execLength := truthState16.machineState.execLength + 1 }

def truthState18 : EVM.State :=
  { truthState17 with
    machineState.stack := (⟨0xe0⟩ : Ethereum.UInt256) :: truthState17.machineState.stack
    machineState.gasAvailable :=
      truthState17.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState17.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := truthState17.machineState.execLength + 1 }

def truthSelectorWord : Ethereum.UInt256 :=
  Ethereum.UInt256.shiftRight truthCalldataWord (⟨0xe0⟩ : Ethereum.UInt256)

def truthState19 : EVM.State :=
  { truthState18 with
    machineState.stack := truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState18.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState18.machineState.pc + ⟨1⟩
    machineState.execLength := truthState18.machineState.execLength + 1 }

def truthState20 : EVM.State :=
  { truthState19 with
    machineState.stack := truthSelectorWord :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState19.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState19.machineState.pc + ⟨1⟩
    machineState.execLength := truthState19.machineState.execLength + 1 }

def truthExpectedSelectorWord : Ethereum.UInt256 :=
  ⟨0x9e9f51d2⟩

theorem truth_selector_word_eq :
    truthSelectorWord = truthExpectedSelectorWord := by
  have hcalldata : truthState16.executionEnv.calldata = truthCallData := by
    simp [truthState16, truthState15, truthState14, truthState13, truthState12, truthState11,
      truthState10, truthState9, truthState8, truthState7, truthState6, truthState5,
      truthState4, truthState3, truthState2, truthState1, truthInitialState, truthExecutionEnv]
  unfold truthSelectorWord truthCalldataWord truthExpectedSelectorWord
  rw [hcalldata]
  simp [truthCallData, truthSelector, ByteArray.readBytes, truth_byteArray_zeroes_eq]
  native_decide

def truthState21 : EVM.State :=
  { truthState20 with
    machineState.stack := truthExpectedSelectorWord :: truthState20.machineState.stack
    machineState.gasAvailable :=
      truthState20.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState20.machineState.pc + Ethereum.UInt256.ofNat 5
    machineState.execLength := truthState20.machineState.execLength + 1 }

def truthSelectorEqWord : Ethereum.UInt256 :=
  Ethereum.UInt256.eq truthExpectedSelectorWord truthSelectorWord

def truthState22 : EVM.State :=
  { truthState21 with
    machineState.stack := truthSelectorEqWord :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState21.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState21.machineState.pc + ⟨1⟩
    machineState.execLength := truthState21.machineState.execLength + 1 }

def truthState23 : EVM.State :=
  { truthState22 with
    machineState.stack := (⟨0x2a⟩ : Ethereum.UInt256) :: truthState22.machineState.stack
    machineState.gasAvailable :=
      truthState22.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState22.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := truthState22.machineState.execLength + 1 }

def truthMismatchState1 : EVM.State :=
  { truthState1 with executionEnv := truthMismatchExecutionEnv }

def truthMismatchState2 : EVM.State :=
  { truthState2 with executionEnv := truthMismatchExecutionEnv }

def truthMismatchState3 : EVM.State :=
  { truthState3 with executionEnv := truthMismatchExecutionEnv }

def truthMismatchState4 : EVM.State :=
  { truthState4 with executionEnv := truthMismatchExecutionEnv }

def truthMismatchState5 : EVM.State :=
  { truthState5 with executionEnv := truthMismatchExecutionEnv }

def truthMismatchState6 : EVM.State :=
  { truthState6 with executionEnv := truthMismatchExecutionEnv }

def truthMismatchState7 : EVM.State :=
  { truthState7 with executionEnv := truthMismatchExecutionEnv }

def truthMismatchState8 : EVM.State :=
  { truthState8 with executionEnv := truthMismatchExecutionEnv }

def truthMismatchState9 : EVM.State :=
  { truthState9 with executionEnv := truthMismatchExecutionEnv }

def truthMismatchState10 : EVM.State :=
  { truthState10 with executionEnv := truthMismatchExecutionEnv }

def truthMismatchState11 : EVM.State :=
  { truthState11 with executionEnv := truthMismatchExecutionEnv }

def truthMismatchState12 : EVM.State :=
  { truthState12 with executionEnv := truthMismatchExecutionEnv }

def truthMismatchState13 : EVM.State :=
  { truthState13 with executionEnv := truthMismatchExecutionEnv }

def truthMismatchState14 : EVM.State :=
  { truthState14 with executionEnv := truthMismatchExecutionEnv }

def truthMismatchState15 : EVM.State :=
  { truthState15 with executionEnv := truthMismatchExecutionEnv }

def truthMismatchState16 : EVM.State :=
  { truthState16 with executionEnv := truthMismatchExecutionEnv }

def truthMismatchCalldataWord : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray <| truthMismatchState16.executionEnv.calldata.readBytes 0 32

def truthMismatchState17 : EVM.State :=
  { truthMismatchState16 with
    machineState.stack := truthMismatchCalldataWord :: []
    machineState.gasAvailable :=
      truthMismatchState16.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthMismatchState16.machineState.pc + ⟨1⟩
    machineState.execLength := truthMismatchState16.machineState.execLength + 1 }

def truthMismatchState18 : EVM.State :=
  { truthMismatchState17 with
    machineState.stack := (⟨0xe0⟩ : Ethereum.UInt256) :: truthMismatchState17.machineState.stack
    machineState.gasAvailable :=
      truthMismatchState17.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthMismatchState17.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := truthMismatchState17.machineState.execLength + 1 }

def truthMismatchSelectorWord : Ethereum.UInt256 :=
  Ethereum.UInt256.shiftRight truthMismatchCalldataWord (⟨0xe0⟩ : Ethereum.UInt256)

def truthMismatchState19 : EVM.State :=
  { truthMismatchState18 with
    machineState.stack := truthMismatchSelectorWord :: []
    machineState.gasAvailable :=
      truthMismatchState18.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthMismatchState18.machineState.pc + ⟨1⟩
    machineState.execLength := truthMismatchState18.machineState.execLength + 1 }

def truthMismatchState20 : EVM.State :=
  { truthMismatchState19 with
    machineState.stack := truthMismatchSelectorWord :: truthMismatchSelectorWord :: []
    machineState.gasAvailable :=
      truthMismatchState19.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthMismatchState19.machineState.pc + ⟨1⟩
    machineState.execLength := truthMismatchState19.machineState.execLength + 1 }

def truthMismatchState21 : EVM.State :=
  { truthMismatchState20 with
    machineState.stack := truthExpectedSelectorWord :: truthMismatchState20.machineState.stack
    machineState.gasAvailable :=
      truthMismatchState20.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthMismatchState20.machineState.pc + Ethereum.UInt256.ofNat 5
    machineState.execLength := truthMismatchState20.machineState.execLength + 1 }

def truthMismatchSelectorEqWord : Ethereum.UInt256 :=
  Ethereum.UInt256.eq truthExpectedSelectorWord truthMismatchSelectorWord

def truthMismatchState22 : EVM.State :=
  { truthMismatchState21 with
    machineState.stack := truthMismatchSelectorEqWord :: truthMismatchSelectorWord :: []
    machineState.gasAvailable :=
      truthMismatchState21.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthMismatchState21.machineState.pc + ⟨1⟩
    machineState.execLength := truthMismatchState21.machineState.execLength + 1 }

def truthMismatchState23 : EVM.State :=
  { truthMismatchState22 with
    machineState.stack := (⟨0x2a⟩ : Ethereum.UInt256) :: truthMismatchState22.machineState.stack
    machineState.gasAvailable :=
      truthMismatchState22.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthMismatchState22.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := truthMismatchState22.machineState.execLength + 1 }

def truthMismatchState24 : EVM.State :=
  { truthMismatchState23 with
    machineState.stack := [truthMismatchSelectorWord]
    machineState.gasAvailable :=
      truthMismatchState23.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Ghigh
    machineState.pc := truthMismatchState23.machineState.pc + ⟨1⟩
    machineState.execLength := truthMismatchState23.machineState.execLength + 1 }

def truthMismatchState25 : EVM.State :=
  { truthMismatchState24 with
    machineState.gasAvailable :=
      truthMismatchState24.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gjumpdest
    machineState.pc := truthMismatchState24.machineState.pc + ⟨1⟩
    machineState.execLength := truthMismatchState24.machineState.execLength + 1 }

def truthMismatchState26 : EVM.State :=
  { truthMismatchState25 with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) :: truthMismatchState25.machineState.stack
    machineState.gasAvailable :=
      truthMismatchState25.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := truthMismatchState25.machineState.pc + ⟨1⟩
    machineState.execLength := truthMismatchState25.machineState.execLength + 1 }

def truthMismatchState27 : EVM.State :=
  { truthMismatchState26 with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) :: truthMismatchState26.machineState.stack
    machineState.gasAvailable :=
      truthMismatchState26.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := truthMismatchState26.machineState.pc + ⟨1⟩
    machineState.execLength := truthMismatchState26.machineState.execLength + 1 }

def truthMismatchReturnData : ByteArray :=
  truthMismatchState27.machineState.memory.readWithPadding 0 0

def truthMismatchState28 : EVM.State :=
  { truthMismatchState27 with
    machineState.stack := [truthMismatchSelectorWord]
    machineState.H_return := truthMismatchReturnData
    machineState.activeWords :=
      Ethereum.UInt256.ofNat
        (Ethereum.MachineState.M truthMismatchState27.machineState.activeWords.toNat 0 0)
    machineState.gasAvailable :=
      (truthMismatchState27.machineState.gasAvailable -
        Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost truthMismatchState27 .REVERT)) -
        Ethereum.UInt256.ofNat GasConstants.Gzero
    machineState.pc := truthMismatchState27.machineState.pc + ⟨1⟩
    machineState.execLength := truthMismatchState27.machineState.execLength + 1 }

def truthParamMismatchState15 (s : EVM.State) : EVM.State :=
  { truthParamPayableState14 s with
    machineState.stack := []
    machineState.gasAvailable :=
      (truthParamPayableState14 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Ghigh
    machineState.pc := (truthParamPayableState14 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamPayableState14 s).machineState.execLength + 1 }

def truthParamMismatchState16 (s : EVM.State) : EVM.State :=
  { truthParamMismatchState15 s with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) ::
      (truthParamMismatchState15 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamMismatchState15 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := (truthParamMismatchState15 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamMismatchState15 s).machineState.execLength + 1 }

def truthParamMismatchCalldataWord (s : EVM.State) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray <|
    (truthParamMismatchState16 s).executionEnv.calldata.readBytes 0 32

def truthParamMismatchState17 (s : EVM.State) : EVM.State :=
  { truthParamMismatchState16 s with
    machineState.stack := truthParamMismatchCalldataWord s :: []
    machineState.gasAvailable :=
      (truthParamMismatchState16 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamMismatchState16 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamMismatchState16 s).machineState.execLength + 1 }

def truthParamMismatchState18 (s : EVM.State) : EVM.State :=
  { truthParamMismatchState17 s with
    machineState.stack := (⟨0xe0⟩ : Ethereum.UInt256) ::
      (truthParamMismatchState17 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamMismatchState17 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamMismatchState17 s).machineState.pc +
      Ethereum.UInt256.ofNat 2
    machineState.execLength := (truthParamMismatchState17 s).machineState.execLength + 1 }

def truthParamMismatchSelectorWord (s : EVM.State) : Ethereum.UInt256 :=
  Ethereum.UInt256.shiftRight (truthParamMismatchCalldataWord s) (⟨0xe0⟩ : Ethereum.UInt256)

def truthParamMismatchState19 (s : EVM.State) : EVM.State :=
  { truthParamMismatchState18 s with
    machineState.stack := truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamMismatchState18 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamMismatchState18 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamMismatchState18 s).machineState.execLength + 1 }

def truthParamMismatchState20 (s : EVM.State) : EVM.State :=
  { truthParamMismatchState19 s with
    machineState.stack := truthParamMismatchSelectorWord s ::
      truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamMismatchState19 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamMismatchState19 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamMismatchState19 s).machineState.execLength + 1 }

def truthParamMismatchState21 (s : EVM.State) : EVM.State :=
  { truthParamMismatchState20 s with
    machineState.stack := truthExpectedSelectorWord ::
      (truthParamMismatchState20 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamMismatchState20 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamMismatchState20 s).machineState.pc +
      Ethereum.UInt256.ofNat 5
    machineState.execLength := (truthParamMismatchState20 s).machineState.execLength + 1 }

def truthParamMismatchSelectorEqWord (s : EVM.State) : Ethereum.UInt256 :=
  Ethereum.UInt256.eq truthExpectedSelectorWord (truthParamMismatchSelectorWord s)

def truthParamMismatchState22 (s : EVM.State) : EVM.State :=
  { truthParamMismatchState21 s with
    machineState.stack := truthParamMismatchSelectorEqWord s ::
      truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamMismatchState21 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamMismatchState21 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamMismatchState21 s).machineState.execLength + 1 }

def truthParamMismatchState23 (s : EVM.State) : EVM.State :=
  { truthParamMismatchState22 s with
    machineState.stack := (⟨0x2a⟩ : Ethereum.UInt256) ::
      (truthParamMismatchState22 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamMismatchState22 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamMismatchState22 s).machineState.pc +
      Ethereum.UInt256.ofNat 2
    machineState.execLength := (truthParamMismatchState22 s).machineState.execLength + 1 }

def truthParamSuccessState24 (s : EVM.State) : EVM.State :=
  { truthParamMismatchState23 s with
    machineState.stack := [truthParamMismatchSelectorWord s]
    machineState.gasAvailable :=
      (truthParamMismatchState23 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Ghigh
    machineState.pc := (⟨0x2a⟩ : Ethereum.UInt256)
    machineState.execLength := (truthParamMismatchState23 s).machineState.execLength + 1 }

def truthParamSuccessState25 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState24 s with
    machineState.gasAvailable :=
      (truthParamSuccessState24 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gjumpdest
    machineState.pc := (truthParamSuccessState24 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState24 s).machineState.execLength + 1 }

def truthParamSuccessState26 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState25 s with
    machineState.stack := (⟨0x30⟩ : Ethereum.UInt256) ::
      (truthParamSuccessState25 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamSuccessState25 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState25 s).machineState.pc +
      Ethereum.UInt256.ofNat 2
    machineState.execLength := (truthParamSuccessState25 s).machineState.execLength + 1 }

def truthParamSuccessState27 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState26 s with
    machineState.stack := (⟨0x44⟩ : Ethereum.UInt256) ::
      (truthParamSuccessState26 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamSuccessState26 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState26 s).machineState.pc +
      Ethereum.UInt256.ofNat 2
    machineState.execLength := (truthParamSuccessState26 s).machineState.execLength + 1 }

def truthParamSuccessState28 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState27 s with
    machineState.stack := (⟨0x30⟩ : Ethereum.UInt256) ::
      truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState27 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gmid
    machineState.pc := (⟨0x44⟩ : Ethereum.UInt256)
    machineState.execLength := (truthParamSuccessState27 s).machineState.execLength + 1 }

def truthParamSuccessState29 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState28 s with
    machineState.gasAvailable :=
      (truthParamSuccessState28 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gjumpdest
    machineState.pc := (truthParamSuccessState28 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState28 s).machineState.execLength + 1 }

def truthParamSuccessState30 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState29 s with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) ::
      (truthParamSuccessState29 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamSuccessState29 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := (truthParamSuccessState29 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState29 s).machineState.execLength + 1 }

def truthParamSuccessState31 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState30 s with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) ::
      (truthParamSuccessState30 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamSuccessState30 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState30 s).machineState.pc +
      Ethereum.UInt256.ofNat 2
    machineState.execLength := (truthParamSuccessState30 s).machineState.execLength + 1 }

def truthParamSuccessState32 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState31 s with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x30⟩ : Ethereum.UInt256) :: truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState31 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState31 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState31 s).machineState.execLength + 1 }

def truthParamSuccessState33 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState32 s with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: (⟨0x30⟩ : Ethereum.UInt256) ::
      truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState32 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := (truthParamSuccessState32 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState32 s).machineState.execLength + 1 }

def truthParamSuccessState34 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState33 s with
    machineState.stack := (⟨0x30⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
      truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState33 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := (truthParamSuccessState33 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamSuccessState33 s).machineState.execLength + 1 }

def truthParamSuccessState35 (s : EVM.State) : EVM.State :=
  { truthParamSuccessState34 s with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) ::
      truthParamMismatchSelectorWord s :: []
    machineState.gasAvailable :=
      (truthParamSuccessState34 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gmid
    machineState.pc := (⟨0x30⟩ : Ethereum.UInt256)
    machineState.execLength := (truthParamSuccessState34 s).machineState.execLength + 1 }

theorem truthParamSuccessState24_code (s : EVM.State) :
    (truthParamSuccessState24 s).executionEnv.code = s.executionEnv.code := by
  simp [truthParamSuccessState24, truthParamMismatchState23, truthParamMismatchState22,
    truthParamMismatchState21, truthParamMismatchState20, truthParamMismatchState19,
    truthParamMismatchState18, truthParamMismatchState17, truthParamMismatchState16,
    truthParamMismatchState15, truthParamPayableState14, truthParamPayableState13,
    truthParamPayableState12, truthParamPayableState11, truthParamPayableState10,
    truthParamPayableState9, truthParamPayableState8, truthParamState7, truthParamState6,
    truthParamState5, truthParamState4, truthParamState3, truthParamState2,
    truthParamState1]

theorem truthParamSuccessState25_code (s : EVM.State) :
    (truthParamSuccessState25 s).executionEnv.code = s.executionEnv.code := by
  simp [truthParamSuccessState25, truthParamSuccessState24_code]

theorem truthParamSuccessState26_code (s : EVM.State) :
    (truthParamSuccessState26 s).executionEnv.code = s.executionEnv.code := by
  simp [truthParamSuccessState26, truthParamSuccessState25_code]

theorem truthParamSuccessState27_code (s : EVM.State) :
    (truthParamSuccessState27 s).executionEnv.code = s.executionEnv.code := by
  simp [truthParamSuccessState27, truthParamSuccessState26_code]

theorem truthParamSuccessState28_code (s : EVM.State) :
    (truthParamSuccessState28 s).executionEnv.code = s.executionEnv.code := by
  simp [truthParamSuccessState28, truthParamSuccessState27_code]

theorem truthParamSuccessState29_code (s : EVM.State) :
    (truthParamSuccessState29 s).executionEnv.code = s.executionEnv.code := by
  simp [truthParamSuccessState29, truthParamSuccessState28_code]

theorem truthParamSuccessState30_code (s : EVM.State) :
    (truthParamSuccessState30 s).executionEnv.code = s.executionEnv.code := by
  simp [truthParamSuccessState30, truthParamSuccessState29_code]

theorem truthParamSuccessState31_code (s : EVM.State) :
    (truthParamSuccessState31 s).executionEnv.code = s.executionEnv.code := by
  simp [truthParamSuccessState31, truthParamSuccessState30_code]

theorem truthParamSuccessState32_code (s : EVM.State) :
    (truthParamSuccessState32 s).executionEnv.code = s.executionEnv.code := by
  simp [truthParamSuccessState32, truthParamSuccessState31_code]

theorem truthParamSuccessState33_code (s : EVM.State) :
    (truthParamSuccessState33 s).executionEnv.code = s.executionEnv.code := by
  simp [truthParamSuccessState33, truthParamSuccessState32_code]

theorem truthParamSuccessState34_code (s : EVM.State) :
    (truthParamSuccessState34 s).executionEnv.code = s.executionEnv.code := by
  simp [truthParamSuccessState34, truthParamSuccessState33_code]

theorem truthParamSuccessState35_code (s : EVM.State) :
    (truthParamSuccessState35 s).executionEnv.code = s.executionEnv.code := by
  simp [truthParamSuccessState35, truthParamSuccessState34_code]

def truthParamMismatchState24 (s : EVM.State) : EVM.State :=
  { truthParamMismatchState23 s with
    machineState.stack := [truthParamMismatchSelectorWord s]
    machineState.gasAvailable :=
      (truthParamMismatchState23 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Ghigh
    machineState.pc := (truthParamMismatchState23 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamMismatchState23 s).machineState.execLength + 1 }

def truthParamMismatchState25 (s : EVM.State) : EVM.State :=
  { truthParamMismatchState24 s with
    machineState.gasAvailable :=
      (truthParamMismatchState24 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gjumpdest
    machineState.pc := (truthParamMismatchState24 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamMismatchState24 s).machineState.execLength + 1 }

def truthParamMismatchState26 (s : EVM.State) : EVM.State :=
  { truthParamMismatchState25 s with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) ::
      (truthParamMismatchState25 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamMismatchState25 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := (truthParamMismatchState25 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamMismatchState25 s).machineState.execLength + 1 }

def truthParamMismatchState27 (s : EVM.State) : EVM.State :=
  { truthParamMismatchState26 s with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) ::
      (truthParamMismatchState26 s).machineState.stack
    machineState.gasAvailable :=
      (truthParamMismatchState26 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := (truthParamMismatchState26 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamMismatchState26 s).machineState.execLength + 1 }

def truthParamMismatchReturnData (s : EVM.State) : ByteArray :=
  (truthParamMismatchState27 s).machineState.memory.readWithPadding 0 0

def truthParamMismatchState28 (s : EVM.State) : EVM.State :=
  { truthParamMismatchState27 s with
    machineState.stack := [truthParamMismatchSelectorWord s]
    machineState.H_return := truthParamMismatchReturnData s
    machineState.activeWords :=
      Ethereum.UInt256.ofNat
        (Ethereum.MachineState.M (truthParamMismatchState27 s).machineState.activeWords.toNat 0 0)
    machineState.gasAvailable :=
      ((truthParamMismatchState27 s).machineState.gasAvailable -
        Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost
          (truthParamMismatchState27 s) .REVERT)) -
        Ethereum.UInt256.ofNat GasConstants.Gzero
    machineState.pc := (truthParamMismatchState27 s).machineState.pc + ⟨1⟩
    machineState.execLength := (truthParamMismatchState27 s).machineState.execLength + 1 }

def truthState24 : EVM.State :=
  { truthState23 with
    machineState.stack := [truthSelectorWord]
    machineState.gasAvailable :=
      truthState23.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Ghigh
    machineState.pc := (⟨0x2a⟩ : Ethereum.UInt256)
    machineState.execLength := truthState23.machineState.execLength + 1 }

def truthState25 : EVM.State :=
  { truthState24 with
    machineState.gasAvailable :=
      truthState24.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gjumpdest
    machineState.pc := truthState24.machineState.pc + ⟨1⟩
    machineState.execLength := truthState24.machineState.execLength + 1 }

def truthState26 : EVM.State :=
  { truthState25 with
    machineState.stack := (⟨0x30⟩ : Ethereum.UInt256) :: truthState25.machineState.stack
    machineState.gasAvailable :=
      truthState25.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState25.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := truthState25.machineState.execLength + 1 }

def truthState27 : EVM.State :=
  { truthState26 with
    machineState.stack := (⟨0x44⟩ : Ethereum.UInt256) :: truthState26.machineState.stack
    machineState.gasAvailable :=
      truthState26.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState26.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := truthState26.machineState.execLength + 1 }

def truthState28 : EVM.State :=
  { truthState27 with
    machineState.stack := (⟨0x30⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState27.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gmid
    machineState.pc := (⟨0x44⟩ : Ethereum.UInt256)
    machineState.execLength := truthState27.machineState.execLength + 1 }

def truthState29 : EVM.State :=
  { truthState28 with
    machineState.gasAvailable :=
      truthState28.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gjumpdest
    machineState.pc := truthState28.machineState.pc + ⟨1⟩
    machineState.execLength := truthState28.machineState.execLength + 1 }

def truthState30 : EVM.State :=
  { truthState29 with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) :: truthState29.machineState.stack
    machineState.gasAvailable :=
      truthState29.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := truthState29.machineState.pc + ⟨1⟩
    machineState.execLength := truthState29.machineState.execLength + 1 }

def truthState31 : EVM.State :=
  { truthState30 with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: truthState30.machineState.stack
    machineState.gasAvailable :=
      truthState30.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState30.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := truthState30.machineState.execLength + 1 }

def truthState32 : EVM.State :=
  { truthState31 with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x30⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState31.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState31.machineState.pc + ⟨1⟩
    machineState.execLength := truthState31.machineState.execLength + 1 }

def truthState33 : EVM.State :=
  { truthState32 with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: (⟨0x30⟩ : Ethereum.UInt256) ::
      truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState32.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := truthState32.machineState.pc + ⟨1⟩
    machineState.execLength := truthState32.machineState.execLength + 1 }

def truthState34 : EVM.State :=
  { truthState33 with
    machineState.stack := (⟨0x30⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
      truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState33.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState33.machineState.pc + ⟨1⟩
    machineState.execLength := truthState33.machineState.execLength + 1 }

def truthState35 : EVM.State :=
  { truthState34 with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState34.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gmid
    machineState.pc := (⟨0x30⟩ : Ethereum.UInt256)
    machineState.execLength := truthState34.machineState.execLength + 1 }

def truthState36 : EVM.State :=
  { truthState35 with
    machineState.gasAvailable :=
      truthState35.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gjumpdest
    machineState.pc := truthState35.machineState.pc + ⟨1⟩
    machineState.execLength := truthState35.machineState.execLength + 1 }

def truthState37 : EVM.State :=
  { truthState36 with
    machineState.stack := (⟨0x40⟩ : Ethereum.UInt256) :: truthState36.machineState.stack
    machineState.gasAvailable :=
      truthState36.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState36.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := truthState36.machineState.execLength + 1 }

def truthFreeMemPtr : Ethereum.UInt256 :=
  if (⟨0x40⟩ : Ethereum.UInt256).toNat ≥ truthState37.machineState.memory.size ∨
      (⟨0x40⟩ : Ethereum.UInt256) ≥ truthState37.machineState.activeWords * ⟨32⟩ then
    ⟨0⟩
  else
    Ethereum.UInt256.ofNat
      (Ethereum.fromByteArrayBigEndian
        (truthState37.machineState.memory.readWithPadding
          (⟨0x40⟩ : Ethereum.UInt256).toNat 32))

def truthState38 : EVM.State :=
  { truthState37 with
    machineState.stack := truthFreeMemPtr :: (⟨1⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.activeWords :=
      Ethereum.UInt256.ofNat
        (Ethereum.MachineState.M truthState37.machineState.activeWords.toNat
          (⟨0x40⟩ : Ethereum.UInt256).toNat 32)
    machineState.gasAvailable :=
      (truthState37.machineState.gasAvailable -
        Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost truthState37 .MLOAD)) -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState37.machineState.pc + ⟨1⟩
    machineState.execLength := truthState37.machineState.execLength + 1 }

def truthAbiEnd : Ethereum.UInt256 :=
  truthFreeMemPtr + (⟨0x20⟩ : Ethereum.UInt256)

def truthState39 : EVM.State :=
  { truthState38 with
    machineState.stack := (⟨0x3b⟩ : Ethereum.UInt256) :: truthState38.machineState.stack
    machineState.gasAvailable :=
      truthState38.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState38.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := truthState38.machineState.execLength + 1 }

def truthState40 : EVM.State :=
  { truthState39 with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: truthFreeMemPtr ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState39.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState39.machineState.pc + ⟨1⟩
    machineState.execLength := truthState39.machineState.execLength + 1 }

def truthState41 : EVM.State :=
  { truthState40 with
    machineState.stack := truthFreeMemPtr :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState40.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState40.machineState.pc + ⟨1⟩
    machineState.execLength := truthState40.machineState.execLength + 1 }

def truthState42 : EVM.State :=
  { truthState41 with
    machineState.stack := (⟨0x64⟩ : Ethereum.UInt256) :: truthState41.machineState.stack
    machineState.gasAvailable :=
      truthState41.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState41.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := truthState41.machineState.execLength + 1 }

def truthState43 : EVM.State :=
  { truthState42 with
    machineState.stack := truthFreeMemPtr :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState42.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gmid
    machineState.pc := (⟨0x64⟩ : Ethereum.UInt256)
    machineState.execLength := truthState42.machineState.execLength + 1 }

def truthState44 : EVM.State :=
  { truthState43 with
    machineState.gasAvailable :=
      truthState43.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gjumpdest
    machineState.pc := truthState43.machineState.pc + ⟨1⟩
    machineState.execLength := truthState43.machineState.execLength + 1 }

def truthState45 : EVM.State :=
  { truthState44 with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) :: truthState44.machineState.stack
    machineState.gasAvailable :=
      truthState44.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := truthState44.machineState.pc + ⟨1⟩
    machineState.execLength := truthState44.machineState.execLength + 1 }

def truthState46 : EVM.State :=
  { truthState45 with
    machineState.stack := (⟨0x20⟩ : Ethereum.UInt256) :: truthState45.machineState.stack
    machineState.gasAvailable :=
      truthState45.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState45.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := truthState45.machineState.execLength + 1 }

def truthState47 : EVM.State :=
  { truthState46 with
    machineState.stack := truthFreeMemPtr :: (⟨0x20⟩ : Ethereum.UInt256) ::
      (⟨0⟩ : Ethereum.UInt256) :: truthFreeMemPtr :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState46.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState46.machineState.pc + ⟨1⟩
    machineState.execLength := truthState46.machineState.execLength + 1 }

def truthState48 : EVM.State :=
  { truthState47 with
    machineState.stack := truthAbiEnd :: (⟨0⟩ : Ethereum.UInt256) :: truthFreeMemPtr ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState47.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState47.machineState.pc + ⟨1⟩
    machineState.execLength := truthState47.machineState.execLength + 1 }

def truthState49 : EVM.State :=
  { truthState48 with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) :: truthAbiEnd :: truthFreeMemPtr ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState48.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState48.machineState.pc + ⟨1⟩
    machineState.execLength := truthState48.machineState.execLength + 1 }

def truthState50 : EVM.State :=
  { truthState49 with
    machineState.stack := truthAbiEnd :: truthFreeMemPtr :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState49.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := truthState49.machineState.pc + ⟨1⟩
    machineState.execLength := truthState49.machineState.execLength + 1 }

def truthState51 : EVM.State :=
  { truthState50 with
    machineState.stack := (⟨0x75⟩ : Ethereum.UInt256) :: truthState50.machineState.stack
    machineState.gasAvailable :=
      truthState50.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState50.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := truthState50.machineState.execLength + 1 }

def truthState52 : EVM.State :=
  { truthState51 with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) :: truthState51.machineState.stack
    machineState.gasAvailable :=
      truthState51.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := truthState51.machineState.pc + ⟨1⟩
    machineState.execLength := truthState51.machineState.execLength + 1 }

def truthState53 : EVM.State :=
  { truthState52 with
    machineState.stack := truthFreeMemPtr :: (⟨0⟩ : Ethereum.UInt256) ::
      (⟨0x75⟩ : Ethereum.UInt256) :: truthAbiEnd :: truthFreeMemPtr ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState52.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState52.machineState.pc + ⟨1⟩
    machineState.execLength := truthState52.machineState.execLength + 1 }

def truthState54 : EVM.State :=
  { truthState53 with
    machineState.stack := truthFreeMemPtr :: (⟨0x75⟩ : Ethereum.UInt256) :: truthAbiEnd ::
      truthFreeMemPtr :: (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) ::
      truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState53.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState53.machineState.pc + ⟨1⟩
    machineState.execLength := truthState53.machineState.execLength + 1 }

def truthState55 : EVM.State :=
  { truthState54 with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: truthFreeMemPtr ::
      (⟨0x75⟩ : Ethereum.UInt256) :: truthAbiEnd :: truthFreeMemPtr ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState54.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState54.machineState.pc + ⟨1⟩
    machineState.execLength := truthState54.machineState.execLength + 1 }

def truthState56 : EVM.State :=
  { truthState55 with
    machineState.stack := (⟨0x57⟩ : Ethereum.UInt256) :: truthState55.machineState.stack
    machineState.gasAvailable :=
      truthState55.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState55.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := truthState55.machineState.execLength + 1 }

def truthState57 : EVM.State :=
  { truthState56 with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: truthFreeMemPtr ::
      (⟨0x75⟩ : Ethereum.UInt256) :: truthAbiEnd :: truthFreeMemPtr ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState56.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gmid
    machineState.pc := (⟨0x57⟩ : Ethereum.UInt256)
    machineState.execLength := truthState56.machineState.execLength + 1 }

def truthState58 : EVM.State :=
  { truthState57 with
    machineState.gasAvailable :=
      truthState57.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gjumpdest
    machineState.pc := truthState57.machineState.pc + ⟨1⟩
    machineState.execLength := truthState57.machineState.execLength + 1 }

def truthState59 : EVM.State :=
  { truthState58 with
    machineState.stack := (⟨0x5e⟩ : Ethereum.UInt256) :: truthState58.machineState.stack
    machineState.gasAvailable :=
      truthState58.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState58.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := truthState58.machineState.execLength + 1 }

def truthState60 : EVM.State :=
  { truthState59 with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: (⟨0x5e⟩ : Ethereum.UInt256) ::
      (⟨1⟩ : Ethereum.UInt256) :: truthFreeMemPtr :: (⟨0x75⟩ : Ethereum.UInt256) ::
      truthAbiEnd :: truthFreeMemPtr :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState59.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState59.machineState.pc + ⟨1⟩
    machineState.execLength := truthState59.machineState.execLength + 1 }

def truthState61 : EVM.State :=
  { truthState60 with
    machineState.stack := (⟨0x4c⟩ : Ethereum.UInt256) :: truthState60.machineState.stack
    machineState.gasAvailable :=
      truthState60.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState60.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := truthState60.machineState.execLength + 1 }

def truthState62 : EVM.State :=
  { truthState61 with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: (⟨0x5e⟩ : Ethereum.UInt256) ::
      (⟨1⟩ : Ethereum.UInt256) :: truthFreeMemPtr :: (⟨0x75⟩ : Ethereum.UInt256) ::
      truthAbiEnd :: truthFreeMemPtr :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState61.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gmid
    machineState.pc := (⟨0x4c⟩ : Ethereum.UInt256)
    machineState.execLength := truthState61.machineState.execLength + 1 }

def truthState63 : EVM.State :=
  { truthState62 with
    machineState.gasAvailable :=
      truthState62.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gjumpdest
    machineState.pc := truthState62.machineState.pc + ⟨1⟩
    machineState.execLength := truthState62.machineState.execLength + 1 }

def truthState64 : EVM.State :=
  { truthState63 with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) :: truthState63.machineState.stack
    machineState.gasAvailable :=
      truthState63.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := truthState63.machineState.pc + ⟨1⟩
    machineState.execLength := truthState63.machineState.execLength + 1 }

def truthState65 : EVM.State :=
  { truthState64 with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨0x5e⟩ : Ethereum.UInt256) ::
      (⟨1⟩ : Ethereum.UInt256) :: truthFreeMemPtr :: (⟨0x75⟩ : Ethereum.UInt256) ::
      truthAbiEnd :: truthFreeMemPtr :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState64.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState64.machineState.pc + ⟨1⟩
    machineState.execLength := truthState64.machineState.execLength + 1 }

def truthState66 : EVM.State :=
  { truthState65 with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨0x5e⟩ : Ethereum.UInt256) ::
      (⟨1⟩ : Ethereum.UInt256) :: truthFreeMemPtr :: (⟨0x75⟩ : Ethereum.UInt256) ::
      truthAbiEnd :: truthFreeMemPtr :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState65.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState65.machineState.pc + ⟨1⟩
    machineState.execLength := truthState65.machineState.execLength + 1 }

def truthState67 : EVM.State :=
  { truthState66 with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨0x5e⟩ : Ethereum.UInt256) ::
      (⟨1⟩ : Ethereum.UInt256) :: truthFreeMemPtr :: (⟨0x75⟩ : Ethereum.UInt256) ::
      truthAbiEnd :: truthFreeMemPtr :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState66.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState66.machineState.pc + ⟨1⟩
    machineState.execLength := truthState66.machineState.execLength + 1 }

def truthState68 : EVM.State :=
  { truthState67 with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨0x5e⟩ : Ethereum.UInt256) ::
      (⟨1⟩ : Ethereum.UInt256) :: truthFreeMemPtr :: (⟨0x75⟩ : Ethereum.UInt256) ::
      truthAbiEnd :: truthFreeMemPtr :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState67.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState67.machineState.pc + ⟨1⟩
    machineState.execLength := truthState67.machineState.execLength + 1 }

def truthState69 : EVM.State :=
  { truthState68 with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x5e⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) :: truthFreeMemPtr ::
      (⟨0x75⟩ : Ethereum.UInt256) :: truthAbiEnd :: truthFreeMemPtr ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState68.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := truthState68.machineState.pc + ⟨1⟩
    machineState.execLength := truthState68.machineState.execLength + 1 }

def truthState70 : EVM.State :=
  { truthState69 with
    machineState.stack := (⟨0x5e⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) :: truthFreeMemPtr ::
      (⟨0x75⟩ : Ethereum.UInt256) :: truthAbiEnd :: truthFreeMemPtr ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState69.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState69.machineState.pc + ⟨1⟩
    machineState.execLength := truthState69.machineState.execLength + 1 }

def truthState71 : EVM.State :=
  { truthState70 with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: (⟨0x5e⟩ : Ethereum.UInt256) ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) :: truthFreeMemPtr ::
      (⟨0x75⟩ : Ethereum.UInt256) :: truthAbiEnd :: truthFreeMemPtr ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState70.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState70.machineState.pc + ⟨1⟩
    machineState.execLength := truthState70.machineState.execLength + 1 }

def truthState72 : EVM.State :=
  { truthState71 with
    machineState.stack := (⟨0x5e⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨1⟩ : Ethereum.UInt256) :: truthFreeMemPtr :: (⟨0x75⟩ : Ethereum.UInt256) ::
      truthAbiEnd :: truthFreeMemPtr :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState71.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := truthState71.machineState.pc + ⟨1⟩
    machineState.execLength := truthState71.machineState.execLength + 1 }

def truthState73 : EVM.State :=
  { truthState72 with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) ::
      truthFreeMemPtr :: (⟨0x75⟩ : Ethereum.UInt256) :: truthAbiEnd :: truthFreeMemPtr ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState72.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gmid
    machineState.pc := (⟨0x5e⟩ : Ethereum.UInt256)
    machineState.execLength := truthState72.machineState.execLength + 1 }

def truthState74 : EVM.State :=
  { truthState73 with
    machineState.gasAvailable :=
      truthState73.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gjumpdest
    machineState.pc := truthState73.machineState.pc + ⟨1⟩
    machineState.execLength := truthState73.machineState.execLength + 1 }

def truthState75 : EVM.State :=
  { truthState74 with
    machineState.stack := truthFreeMemPtr :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨1⟩ : Ethereum.UInt256) :: truthFreeMemPtr :: (⟨0x75⟩ : Ethereum.UInt256) ::
      truthAbiEnd :: truthFreeMemPtr :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState74.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState74.machineState.pc + ⟨1⟩
    machineState.execLength := truthState74.machineState.execLength + 1 }

def truthEncodedMemory : ByteArray :=
  (⟨1⟩ : Ethereum.UInt256).toByteArray.write 0
    truthState75.machineState.memory truthFreeMemPtr.toNat 32

def truthState76 : EVM.State :=
  { truthState75 with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: truthFreeMemPtr ::
      (⟨0x75⟩ : Ethereum.UInt256) :: truthAbiEnd :: truthFreeMemPtr ::
      (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.memory := truthEncodedMemory
    machineState.activeWords :=
      Ethereum.UInt256.ofNat
        (Ethereum.MachineState.M truthState75.machineState.activeWords.toNat
          truthFreeMemPtr.toNat 32)
    machineState.gasAvailable :=
      (truthState75.machineState.gasAvailable -
        Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost truthState75 .MSTORE)) -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState75.machineState.pc + ⟨1⟩
    machineState.execLength := truthState75.machineState.execLength + 1 }

def truthState77 : EVM.State :=
  { truthState76 with
    machineState.stack := truthFreeMemPtr :: (⟨0x75⟩ : Ethereum.UInt256) ::
      truthAbiEnd :: truthFreeMemPtr :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState76.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := truthState76.machineState.pc + ⟨1⟩
    machineState.execLength := truthState76.machineState.execLength + 1 }

def truthState78 : EVM.State :=
  { truthState77 with
    machineState.stack := (⟨0x75⟩ : Ethereum.UInt256) :: truthAbiEnd ::
      truthFreeMemPtr :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState77.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := truthState77.machineState.pc + ⟨1⟩
    machineState.execLength := truthState77.machineState.execLength + 1 }

def truthState79 : EVM.State :=
  { truthState78 with
    machineState.stack := truthAbiEnd :: truthFreeMemPtr :: (⟨1⟩ : Ethereum.UInt256) ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState78.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gmid
    machineState.pc := (⟨0x75⟩ : Ethereum.UInt256)
    machineState.execLength := truthState78.machineState.execLength + 1 }

def truthState80 : EVM.State :=
  { truthState79 with
    machineState.gasAvailable :=
      truthState79.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gjumpdest
    machineState.pc := truthState79.machineState.pc + ⟨1⟩
    machineState.execLength := truthState79.machineState.execLength + 1 }

def truthState81 : EVM.State :=
  { truthState80 with
    machineState.stack := (⟨0x3b⟩ : Ethereum.UInt256) :: truthFreeMemPtr ::
      (⟨1⟩ : Ethereum.UInt256) :: truthAbiEnd :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState80.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState80.machineState.pc + ⟨1⟩
    machineState.execLength := truthState80.machineState.execLength + 1 }

def truthState82 : EVM.State :=
  { truthState81 with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: truthFreeMemPtr ::
      (⟨0x3b⟩ : Ethereum.UInt256) :: truthAbiEnd :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState81.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState81.machineState.pc + ⟨1⟩
    machineState.execLength := truthState81.machineState.execLength + 1 }

def truthState83 : EVM.State :=
  { truthState82 with
    machineState.stack := truthFreeMemPtr :: (⟨0x3b⟩ : Ethereum.UInt256) ::
      truthAbiEnd :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState82.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := truthState82.machineState.pc + ⟨1⟩
    machineState.execLength := truthState82.machineState.execLength + 1 }

def truthState84 : EVM.State :=
  { truthState83 with
    machineState.stack := (⟨0x3b⟩ : Ethereum.UInt256) :: truthAbiEnd :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState83.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := truthState83.machineState.pc + ⟨1⟩
    machineState.execLength := truthState83.machineState.execLength + 1 }

def truthState85 : EVM.State :=
  { truthState84 with
    machineState.stack := truthAbiEnd :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState84.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gmid
    machineState.pc := (⟨0x3b⟩ : Ethereum.UInt256)
    machineState.execLength := truthState84.machineState.execLength + 1 }

def truthState86 : EVM.State :=
  { truthState85 with
    machineState.gasAvailable :=
      truthState85.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gjumpdest
    machineState.pc := truthState85.machineState.pc + ⟨1⟩
    machineState.execLength := truthState85.machineState.execLength + 1 }

def truthState87 : EVM.State :=
  { truthState86 with
    machineState.stack := (⟨0x40⟩ : Ethereum.UInt256) :: truthState86.machineState.stack
    machineState.gasAvailable :=
      truthState86.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState86.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := truthState86.machineState.execLength + 1 }

def truthFinalFreeMemPtr : Ethereum.UInt256 :=
  if (⟨0x40⟩ : Ethereum.UInt256).toNat ≥ truthState87.machineState.memory.size ∨
      (⟨0x40⟩ : Ethereum.UInt256) ≥ truthState87.machineState.activeWords * ⟨32⟩ then
    ⟨0⟩
  else
    Ethereum.UInt256.ofNat
      (Ethereum.fromByteArrayBigEndian
        (truthState87.machineState.memory.readWithPadding
          (⟨0x40⟩ : Ethereum.UInt256).toNat 32))

def truthState88 : EVM.State :=
  { truthState87 with
    machineState.stack := truthFinalFreeMemPtr :: truthAbiEnd :: truthSelectorWord :: []
    machineState.activeWords :=
      Ethereum.UInt256.ofNat
        (Ethereum.MachineState.M truthState87.machineState.activeWords.toNat
          (⟨0x40⟩ : Ethereum.UInt256).toNat 32)
    machineState.gasAvailable :=
      (truthState87.machineState.gasAvailable -
        Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost truthState87 .MLOAD)) -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState87.machineState.pc + ⟨1⟩
    machineState.execLength := truthState87.machineState.execLength + 1 }

def truthReturnLength : Ethereum.UInt256 :=
  Ethereum.UInt256.sub truthAbiEnd truthFinalFreeMemPtr

def truthState89 : EVM.State :=
  { truthState88 with
    machineState.stack := truthFinalFreeMemPtr :: truthFinalFreeMemPtr ::
      truthAbiEnd :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState88.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState88.machineState.pc + ⟨1⟩
    machineState.execLength := truthState88.machineState.execLength + 1 }

def truthState90 : EVM.State :=
  { truthState89 with
    machineState.stack := truthAbiEnd :: truthFinalFreeMemPtr ::
      truthFinalFreeMemPtr :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState89.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState89.machineState.pc + ⟨1⟩
    machineState.execLength := truthState89.machineState.execLength + 1 }

def truthState91 : EVM.State :=
  { truthState90 with
    machineState.stack := truthReturnLength :: truthFinalFreeMemPtr :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState90.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState90.machineState.pc + ⟨1⟩
    machineState.execLength := truthState90.machineState.execLength + 1 }

def truthState92 : EVM.State :=
  { truthState91 with
    machineState.stack := truthFinalFreeMemPtr :: truthReturnLength :: truthSelectorWord :: []
    machineState.gasAvailable :=
      truthState91.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthState91.machineState.pc + ⟨1⟩
    machineState.execLength := truthState91.machineState.execLength + 1 }

def truthFinalReturnData : ByteArray :=
  truthState92.machineState.memory.readWithPadding
    truthFinalFreeMemPtr.toNat truthReturnLength.toNat

def truthState93 : EVM.State :=
  { truthState92 with
    machineState.stack := [truthSelectorWord]
    machineState.H_return := truthFinalReturnData
    machineState.activeWords :=
      Ethereum.UInt256.ofNat
        (Ethereum.MachineState.M truthState92.machineState.activeWords.toNat
          truthFinalFreeMemPtr.toNat truthReturnLength.toNat)
    machineState.gasAvailable :=
      (truthState92.machineState.gasAvailable -
        Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost truthState92 .RETURN)) -
        Ethereum.UInt256.ofNat GasConstants.Gzero
    machineState.pc := truthState92.machineState.pc + ⟨1⟩
    machineState.execLength := truthState92.machineState.execLength + 1 }

def truthNonpayableExecutionEnv : Ethereum.ExecutionEnv :=
  { truthExecutionEnv with
      weiValue := (⟨1⟩ : Ethereum.UInt256) }

def truthNonpayableInitialState : EVM.State :=
  { truthInitialState with
      executionEnv := truthNonpayableExecutionEnv }

def truthNonpayableState1 : EVM.State :=
  { truthNonpayableInitialState with
    machineState.stack := (⟨0x80⟩ : Ethereum.UInt256) :: truthNonpayableInitialState.machineState.stack
    machineState.gasAvailable :=
      truthNonpayableInitialState.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthNonpayableInitialState.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := truthNonpayableInitialState.machineState.execLength + 1 }

def truthNonpayableState2 : EVM.State :=
  { truthNonpayableState1 with
    machineState.stack := (⟨0x40⟩ : Ethereum.UInt256) :: truthNonpayableState1.machineState.stack
    machineState.gasAvailable :=
      truthNonpayableState1.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthNonpayableState1.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := truthNonpayableState1.machineState.execLength + 1 }

def truthNonpayableState3 : EVM.State :=
  { truthNonpayableState2 with
    machineState.stack := []
    machineState.memory :=
      (⟨0x80⟩ : Ethereum.UInt256).toByteArray.write 0
        truthNonpayableState2.machineState.memory 0x40 32
    machineState.activeWords :=
      Ethereum.UInt256.ofNat
        (Ethereum.MachineState.M truthNonpayableState2.machineState.activeWords.toNat 0x40 32)
    machineState.gasAvailable :=
      (truthNonpayableState2.machineState.gasAvailable -
        Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost truthNonpayableState2 .MSTORE)) -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthNonpayableState2.machineState.pc + ⟨1⟩
    machineState.execLength := truthNonpayableState2.machineState.execLength + 1 }

def truthNonpayableState4 : EVM.State :=
  { truthNonpayableState3 with
    machineState.stack := truthNonpayableState3.executionEnv.weiValue ::
      truthNonpayableState3.machineState.stack
    machineState.gasAvailable :=
      truthNonpayableState3.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := truthNonpayableState3.machineState.pc + ⟨1⟩
    machineState.execLength := truthNonpayableState3.machineState.execLength + 1 }

def truthNonpayableState5 : EVM.State :=
  { truthNonpayableState4 with
    machineState.stack := (⟨1⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) :: []
    machineState.gasAvailable :=
      truthNonpayableState4.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthNonpayableState4.machineState.pc + ⟨1⟩
    machineState.execLength := truthNonpayableState4.machineState.execLength + 1 }

def truthNonpayableState6 : EVM.State :=
  { truthNonpayableState5 with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) :: (⟨1⟩ : Ethereum.UInt256) :: []
    machineState.gasAvailable :=
      truthNonpayableState5.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthNonpayableState5.machineState.pc + ⟨1⟩
    machineState.execLength := truthNonpayableState5.machineState.execLength + 1 }

def truthNonpayableState7 : EVM.State :=
  { truthNonpayableState6 with
    machineState.stack := (⟨0x0e⟩ : Ethereum.UInt256) :: truthNonpayableState6.machineState.stack
    machineState.gasAvailable :=
      truthNonpayableState6.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := truthNonpayableState6.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := truthNonpayableState6.machineState.execLength + 1 }

def truthNonpayableState8 : EVM.State :=
  { truthNonpayableState7 with
    machineState.stack := [(⟨1⟩ : Ethereum.UInt256)]
    machineState.gasAvailable :=
      truthNonpayableState7.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Ghigh
    machineState.pc := truthNonpayableState7.machineState.pc + ⟨1⟩
    machineState.execLength := truthNonpayableState7.machineState.execLength + 1 }

def truthNonpayableState9 : EVM.State :=
  { truthNonpayableState8 with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) :: truthNonpayableState8.machineState.stack
    machineState.gasAvailable :=
      truthNonpayableState8.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := truthNonpayableState8.machineState.pc + ⟨1⟩
    machineState.execLength := truthNonpayableState8.machineState.execLength + 1 }

def truthNonpayableState10 : EVM.State :=
  { truthNonpayableState9 with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) :: truthNonpayableState9.machineState.stack
    machineState.gasAvailable :=
      truthNonpayableState9.machineState.gasAvailable -
        Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := truthNonpayableState9.machineState.pc + ⟨1⟩
    machineState.execLength := truthNonpayableState9.machineState.execLength + 1 }

def truthNonpayableReturnData : ByteArray :=
  truthNonpayableState10.machineState.memory.readWithPadding 0 0

def truthNonpayableState11 : EVM.State :=
  { truthNonpayableState10 with
    machineState.stack := [(⟨1⟩ : Ethereum.UInt256)]
    machineState.H_return := truthNonpayableReturnData
    machineState.activeWords :=
      Ethereum.UInt256.ofNat
        (Ethereum.MachineState.M truthNonpayableState10.machineState.activeWords.toNat 0 0)
    machineState.gasAvailable :=
      (truthNonpayableState10.machineState.gasAvailable -
        Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost truthNonpayableState10 .REVERT)) -
        Ethereum.UInt256.ofNat GasConstants.Gzero
    machineState.pc := truthNonpayableState10.machineState.pc + ⟨1⟩
    machineState.execLength := truthNonpayableState10.machineState.execLength + 1 }

axiom truth_pc58_has_gas :
  ¬ truthState42.machineState.gasAvailable.toNat < GasConstants.Gmid

axiom truth_pc116_has_gas :
  ¬ truthState56.machineState.gasAvailable.toNat < GasConstants.Gmid

axiom truth_pc93_has_gas :
  ¬ truthState61.machineState.gasAvailable.toNat < GasConstants.Gmid

axiom truth_pc86_has_gas :
  ¬ truthState72.machineState.gasAvailable.toNat < GasConstants.Gmid

axiom truth_pc96_has_memory_gas :
  ¬ truthState75.machineState.gasAvailable.toNat <
    Ethereum.EVM.memoryExpansionCost truthState75 .MSTORE

axiom truth_pc96_has_verylow_gas :
  ¬ (truthState75.machineState.gasAvailable -
      Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost truthState75 .MSTORE)).toNat <
    GasConstants.Gverylow

axiom truth_pc97_has_gas :
  ¬ truthState76.machineState.gasAvailable.toNat < GasConstants.Gbase

axiom truth_pc98_has_gas :
  ¬ truthState77.machineState.gasAvailable.toNat < GasConstants.Gbase

axiom truth_pc99_has_gas :
  ¬ truthState78.machineState.gasAvailable.toNat < GasConstants.Gmid

axiom truth_pc117_has_gas :
  ¬ truthState79.machineState.gasAvailable.toNat < GasConstants.Gjumpdest

axiom truth_pc118_has_gas :
  ¬ truthState80.machineState.gasAvailable.toNat < GasConstants.Gverylow

axiom truth_pc119_has_gas :
  ¬ truthState81.machineState.gasAvailable.toNat < GasConstants.Gverylow

axiom truth_pc120_has_gas :
  ¬ truthState82.machineState.gasAvailable.toNat < GasConstants.Gbase

axiom truth_pc121_has_gas :
  ¬ truthState83.machineState.gasAvailable.toNat < GasConstants.Gbase

axiom truth_pc122_has_gas :
  ¬ truthState84.machineState.gasAvailable.toNat < GasConstants.Gmid

axiom truth_pc59_has_gas :
  ¬ truthState85.machineState.gasAvailable.toNat < GasConstants.Gjumpdest

axiom truth_pc60_has_gas :
  ¬ truthState86.machineState.gasAvailable.toNat < GasConstants.Gverylow

axiom truth_pc62_has_memory_gas :
  ¬ truthState87.machineState.gasAvailable.toNat <
    Ethereum.EVM.memoryExpansionCost truthState87 .MLOAD

axiom truth_pc62_has_verylow_gas :
  ¬ (truthState87.machineState.gasAvailable -
      Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost truthState87 .MLOAD)).toNat <
    GasConstants.Gverylow

axiom truth_pc63_has_gas :
  ¬ truthState88.machineState.gasAvailable.toNat < GasConstants.Gverylow

axiom truth_pc64_has_gas :
  ¬ truthState89.machineState.gasAvailable.toNat < GasConstants.Gverylow

axiom truth_pc65_has_gas :
  ¬ truthState90.machineState.gasAvailable.toNat < GasConstants.Gverylow

axiom truth_pc66_has_gas :
  ¬ truthState91.machineState.gasAvailable.toNat < GasConstants.Gverylow

axiom truth_pc67_has_gas :
  ¬ truthState92.machineState.gasAvailable.toNat <
    Ethereum.EVM.memoryExpansionCost truthState92 .RETURN

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

def truthWord128Bytes : ByteArray :=
  ⟨#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,128]⟩

def truthWordOneBytes : ByteArray :=
  ⟨#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]⟩

def truthMemoryAfterFreePtrStore : ByteArray :=
  ⟨#[
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,128
  ]⟩

def truthMemoryAfterReturnStore : ByteArray :=
  ⟨#[
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,128,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1
  ]⟩

theorem truth_state3_memory_eq :
    truthState3.machineState.memory = truthMemoryAfterFreePtrStore := by
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    simp [truthMemoryAfterFreePtrStore, truthState3, truthState2, truthState1,
      truthInitialState, truthExecutionEnv, Ethereum.UInt256.toByteArray, BE,
      Ethereum.toBytesBigEndian, Ethereum.toBytes', Ethereum.UInt256.toNat, UInt8.size,
      Ethereum.UInt256.size, truth_byteArray_zeroes_eq, USize.toNat, hbits, ByteArray.write]
  all_goals rfl

theorem truth_state37_activeWords_eq :
    truthState37.machineState.activeWords = (⟨3⟩ : Ethereum.UInt256) := by
  rw [show truthState37.machineState.activeWords = truthState3.machineState.activeWords by rfl]
  simp [truthState3, truthState2, truthState1, truthInitialState, truthExecutionEnv,
    Ethereum.MachineState.M, Ethereum.UInt256.toNat, Ethereum.UInt256.size]
  change Ethereum.UInt256.ofNat 3 = ({ val := 3 } : Ethereum.UInt256)
  rfl

theorem truth_read_free_ptr_word :
    truthMemoryAfterFreePtrStore.readWithPadding 64 32 = truthWord128Bytes := by
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    simp [truthMemoryAfterFreePtrStore, truthWord128Bytes, ByteArray.readWithPadding,
      ByteArray.readWithoutPadding, truth_byteArray_zeroes_eq, USize.toNat, hbits]
  all_goals rfl

theorem truth_from_word128 :
    Ethereum.fromByteArrayBigEndian truthWord128Bytes = 128 := by
  native_decide

theorem truth_free_mem_ptr_eq :
    truthFreeMemPtr = (⟨0x80⟩ : Ethereum.UInt256) := by
  unfold truthFreeMemPtr
  rw [show truthState37.machineState.memory = truthMemoryAfterFreePtrStore by
    rw [show truthState37.machineState.memory = truthState3.machineState.memory by rfl,
      truth_state3_memory_eq]]
  rw [truth_state37_activeWords_eq]
  rw [show (⟨0x40⟩ : Ethereum.UInt256).toNat = 64 by rfl]
  rw [truth_read_free_ptr_word, truth_from_word128]
  simp [truthMemoryAfterFreePtrStore]
  rfl

theorem truth_encoded_memory_eq :
    truthEncodedMemory = truthMemoryAfterReturnStore := by
  unfold truthEncodedMemory
  rw [truth_free_mem_ptr_eq]
  rw [show truthState75.machineState.memory = truthState3.machineState.memory by rfl,
    truth_state3_memory_eq]
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    simp [truthMemoryAfterReturnStore, truthMemoryAfterFreePtrStore,
      Ethereum.UInt256.toByteArray, BE, Ethereum.toBytesBigEndian, Ethereum.toBytes',
      Ethereum.UInt256.toNat, UInt8.size, Ethereum.UInt256.size, truth_byteArray_zeroes_eq,
      USize.toNat, hbits, ByteArray.write]
  all_goals rfl

theorem truth_state87_memory_eq :
    truthState87.machineState.memory = truthMemoryAfterReturnStore := by
  rw [show truthState87.machineState.memory = truthEncodedMemory by rfl, truth_encoded_memory_eq]

theorem truth_state87_activeWords_eq :
    truthState87.machineState.activeWords = (⟨5⟩ : Ethereum.UInt256) := by
  rw [show truthState87.machineState.activeWords = truthState76.machineState.activeWords by rfl]
  unfold truthState76
  rw [truth_free_mem_ptr_eq]
  rw [show truthState75.machineState.activeWords = truthState3.machineState.activeWords by rfl]
  simp [truthState3, truthState2, truthState1, truthInitialState, truthExecutionEnv,
    Ethereum.MachineState.M, Ethereum.UInt256.toNat, Ethereum.UInt256.size]
  change Ethereum.UInt256.ofNat 5 = ({ val := 5 } : Ethereum.UInt256)
  rfl

theorem truth_read_final_free_ptr_word :
    truthMemoryAfterReturnStore.readWithPadding 64 32 = truthWord128Bytes := by
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    simp [truthMemoryAfterReturnStore, truthWord128Bytes, ByteArray.readWithPadding,
      ByteArray.readWithoutPadding, truth_byteArray_zeroes_eq, USize.toNat, hbits]
  all_goals rfl

theorem truth_final_free_mem_ptr_eq :
    truthFinalFreeMemPtr = (⟨0x80⟩ : Ethereum.UInt256) := by
  unfold truthFinalFreeMemPtr
  rw [truth_state87_memory_eq, truth_state87_activeWords_eq]
  rw [show (⟨0x40⟩ : Ethereum.UInt256).toNat = 64 by rfl]
  rw [truth_read_final_free_ptr_word, truth_from_word128]
  simp [truthMemoryAfterReturnStore]
  rfl

theorem truth_return_length_eq :
    truthReturnLength = (⟨0x20⟩ : Ethereum.UInt256) := by
  unfold truthReturnLength truthAbiEnd
  rw [truth_free_mem_ptr_eq, truth_final_free_mem_ptr_eq]
  rfl

theorem truth_final_return_data_eq_word :
    truthFinalReturnData = truthWordOneBytes := by
  unfold truthFinalReturnData
  rw [show truthState92.machineState.memory = truthState87.machineState.memory by rfl,
    truth_state87_memory_eq]
  rw [truth_final_free_mem_ptr_eq, truth_return_length_eq]
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    simp [truthMemoryAfterReturnStore, truthWordOneBytes, ByteArray.readWithPadding,
      ByteArray.readWithoutPadding, truth_byteArray_zeroes_eq, USize.toNat, hbits]
  all_goals rfl

theorem truth_return_data_eq_word :
    truthReturnData = truthWordOneBytes := by
  simp [truthReturnData, truthWordOneBytes, EVM.UInt256.toBytes, Ethereum.toBytes',
    Ethereum.UInt256.size, UInt8.size]
  rfl

theorem truth_final_return_data_eq :
  truthFinalReturnData = truthReturnData := by
  rw [truth_final_return_data_eq_word, truth_return_data_eq_word]

theorem truth_uint256_add_zero (x : Ethereum.UInt256) :
    x + (⟨0⟩ : Ethereum.UInt256) = x := by
  cases x with
  | mk val =>
    apply congrArg Ethereum.UInt256.mk
    simp

theorem truth_uint256_ofNat_toNat (x : Ethereum.UInt256) :
    Ethereum.UInt256.ofNat x.toNat = x := by
  cases x with
  | mk val =>
    cases val with
    | mk n hn =>
      apply congrArg Ethereum.UInt256.mk
      apply Fin.ext
      simp [Ethereum.UInt256.toNat, Nat.mod_eq_of_lt hn]

theorem truth_uint256_ofNat_ofNat_toNat (n : Nat) :
    Ethereum.UInt256.ofNat (Ethereum.UInt256.ofNat n).toNat =
      Ethereum.UInt256.ofNat n := by
  exact truth_uint256_ofNat_toNat (Ethereum.UInt256.ofNat n)

theorem truth_machineState_M_zero_zero (n : Nat) :
    Ethereum.MachineState.M n 0 0 = n := by
  rfl

theorem truth_revert_activeWords_zero_zero (n : Nat) :
    Ethereum.UInt256.ofNat
        (Ethereum.MachineState.M
          (Ethereum.UInt256.ofNat (Ethereum.MachineState.M n 0 0)).toNat 0 0) =
      Ethereum.UInt256.ofNat (Ethereum.MachineState.M n 0 0) := by
  simp [truth_machineState_M_zero_zero, truth_uint256_ofNat_toNat]

theorem truth_readWithPadding_zero_zero (mem : ByteArray) :
    mem.readWithPadding 0 0 = ByteArray.empty := by
  simp [ByteArray.readWithPadding, ByteArray.readWithoutPadding, truth_byteArray_zeroes_eq]
  rfl

theorem truth_revert_zero_memoryExpansionCost (s : EVM.State)
    (hstack : s.machineState.stack = [(⟨0⟩ : Ethereum.UInt256), (⟨0⟩ : Ethereum.UInt256)]) :
    Ethereum.EVM.memoryExpansionCost s .REVERT = 0 := by
  simp [Ethereum.EVM.memoryExpansionCost, Ethereum.EVM.memoryExpansionCost.μᵢ', hstack,
    Ethereum.MachineState.M, Ethereum.UInt256.toNat]
  change Ethereum.EVM.Cₘ (Ethereum.UInt256.ofNat s.machineState.activeWords.toNat) -
      Ethereum.EVM.Cₘ s.machineState.activeWords = 0
  rw [truth_uint256_ofNat_toNat]
  simp

theorem truth_revert_zero_memoryExpansionCost_top (s : EVM.State) (t : List Ethereum.UInt256)
    (hstack : s.machineState.stack =
      (⟨0⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) :: t) :
    Ethereum.EVM.memoryExpansionCost s .REVERT = 0 := by
  simp [Ethereum.EVM.memoryExpansionCost, Ethereum.EVM.memoryExpansionCost.μᵢ', hstack,
    Ethereum.MachineState.M, Ethereum.UInt256.toNat]
  change Ethereum.EVM.Cₘ (Ethereum.UInt256.ofNat s.machineState.activeWords.toNat) -
      Ethereum.EVM.Cₘ s.machineState.activeWords = 0
  rw [truth_uint256_ofNat_toNat]
  simp

theorem truth_decode_pc0 :
    Ethereum.EVM.decode truthRuntimeBytecode truthInitialState.machineState.pc =
      some (.PUSH1, some ((⟨0x80⟩ : Ethereum.UInt256), 1)) := by
  native_decide

theorem truth_xstep_pc0 :
    Ethereum.EVM.Xstep truthValidJumps truthInitialState =
      .ok (truthState1, .none) := by
  simpa [truthValidJumps, truthInitialState, truthExecutionEnv] using
    Ethereum.EVM.step_push1 truthInitialState (⟨0x80⟩ : Ethereum.UInt256) truth_decode_pc0

theorem truth_decode_pc2 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState1.machineState.pc =
      some (.PUSH1, some ((⟨0x40⟩ : Ethereum.UInt256), 1)) := by
  native_decide

theorem truth_xstep_pc2 :
    Ethereum.EVM.Xstep truthValidJumps truthState1 =
      .ok (truthState2, .none) := by
  simpa [truthValidJumps, truthState1, truthInitialState, truthExecutionEnv] using
    Ethereum.EVM.step_push1 truthState1 (⟨0x40⟩ : Ethereum.UInt256) truth_decode_pc2

theorem truth_decode_pc4 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState2.machineState.pc =
      some (.MSTORE, none) := by
  native_decide

theorem truth_xstep_pc4 :
    Ethereum.EVM.Xstep truthValidJumps truthState2 =
      .ok (truthState3, .none) := by
  simpa [truthValidJumps, truthState3] using
    Ethereum.EVM.step_mstore truthState2 truth_decode_pc4

theorem truth_decode_pc5 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState3.machineState.pc =
      some (.CALLVALUE, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨5⟩ : Ethereum.UInt256) =
    some (.CALLVALUE, none)
  native_decide

theorem truth_xstep_pc5 :
    Ethereum.EVM.Xstep truthValidJumps truthState3 =
      .ok (truthState4, .none) := by
  simpa [truthValidJumps, truthState4] using
    Ethereum.EVM.step_callvalue truthState3 truth_decode_pc5

theorem truth_decode_pc6 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState4.machineState.pc =
      some (.DUP1, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨6⟩ : Ethereum.UInt256) =
    some (.DUP1, none)
  native_decide

theorem truth_xstep_pc6 :
    Ethereum.EVM.Xstep truthValidJumps truthState4 =
      .ok (truthState5, .none) := by
  simpa [truthValidJumps, truthState5, truthState4, truthState3, truthExecutionEnv] using
    Ethereum.EVM.step_dup1 truthState4 truth_decode_pc6

theorem truth_decode_pc7 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState5.machineState.pc =
      some (.ISZERO, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨7⟩ : Ethereum.UInt256) =
    some (.ISZERO, none)
  native_decide

theorem truth_xstep_pc7 :
    Ethereum.EVM.Xstep truthValidJumps truthState5 =
      .ok (truthState6, .none) := by
  simpa [truthValidJumps, truthState6, truthState5] using
    Ethereum.EVM.step_iszero truthState5 truth_decode_pc7

theorem truth_decode_pc8 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState6.machineState.pc =
      some (.PUSH1, some ((⟨0x0e⟩ : Ethereum.UInt256), 1)) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨8⟩ : Ethereum.UInt256) =
    some (.PUSH1, some ((⟨0x0e⟩ : Ethereum.UInt256), 1))
  native_decide

theorem truth_xstep_pc8 :
    Ethereum.EVM.Xstep truthValidJumps truthState6 =
      .ok (truthState7, .none) := by
  simpa [truthValidJumps, truthState7] using
    Ethereum.EVM.step_push1 truthState6 (⟨0x0e⟩ : Ethereum.UInt256) truth_decode_pc8

theorem truth_mstore_memoryExpansionCost :
    Ethereum.EVM.memoryExpansionCost truthState2 .MSTORE = 9 := by
  native_decide

theorem truth_nonpayable_mstore_memoryExpansionCost :
    Ethereum.EVM.memoryExpansionCost truthNonpayableState2 .MSTORE = 9 := by
  native_decide

theorem truth_short_mstore_memoryExpansionCost :
    Ethereum.EVM.memoryExpansionCost truthShortState2 .MSTORE = 9 := by
  native_decide

theorem truth_mismatch_mstore_memoryExpansionCost :
    Ethereum.EVM.memoryExpansionCost truthMismatchState2 .MSTORE = 9 := by
  native_decide

theorem truth_pc10_has_gas :
    ¬ truthState7.machineState.gasAvailable.toNat < GasConstants.Ghigh := by
  have hmem := truth_mstore_memoryExpansionCost
  simp only [truthState7, truthState6, truthState5, truthState4, truthState3]
  rw [hmem]
  native_decide

theorem truth_valid_jumpdest_0e :
    (Ethereum.EVM.D_J truthRuntimeBytecode ⟨0⟩).contains (⟨0x0e⟩ : Ethereum.UInt256) = true := by
  native_decide

theorem truth_decode_pc10 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState7.machineState.pc =
      some (.JUMPI, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x0a⟩ : Ethereum.UInt256) =
    some (.JUMPI, none)
  native_decide

theorem truth_xstep_pc10 :
    Ethereum.EVM.Xstep truthValidJumps truthState7 =
      .ok (truthState8, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthState7.executionEnv.code ⟨0⟩ by
    simp [truthValidJumps, truthState7, truthState6, truthState5, truthState4,
      truthState3, truthState2, truthState1, truthInitialState, truthExecutionEnv]]
  rw [Ethereum.EVM.step_jumpi truthState7 truth_decode_pc10]
  simp [truthState7, truthState6, truthState5, truthState4, truthState3]
  rw [truth_mstore_memoryExpansionCost]
  have hgas : ¬ ((truthState2.machineState.gasAvailable - Ethereum.UInt256.ofNat 9 -
                                  Ethereum.UInt256.ofNat GasConstants.Gverylow -
                                Ethereum.UInt256.ofNat GasConstants.Gbase -
                              Ethereum.UInt256.ofNat GasConstants.Gverylow -
                            Ethereum.UInt256.ofNat GasConstants.Gverylow -
                          Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Ghigh) := by
    native_decide
  rw [if_neg hgas]
  have hbad : ¬ ((({ val := 1 } : Ethereum.UInt256) != { val := 0 }) = true ∧
      (Ethereum.EVM.D_J truthState2.executionEnv.code { val := 0 }).contains { val := 14 } = false) := by
    have hcode : truthState2.executionEnv.code = truthRuntimeBytecode := by
      simp [truthState2, truthState1, truthInitialState, truthExecutionEnv]
    rw [hcode]
    simp [truth_valid_jumpdest_0e]
  rw [if_neg hbad]
  simp [truthState8, truthState7, truthState6, truthState5, truthState4, truthState3]
  constructor
  · native_decide
  · rw [truth_mstore_memoryExpansionCost]

theorem truth_nonpayable_xstep_pc0 :
    Ethereum.EVM.Xstep truthValidJumps truthNonpayableInitialState =
      .ok (truthNonpayableState1, .none) := by
  simpa [truthValidJumps, truthNonpayableInitialState, truthNonpayableExecutionEnv,
    truthInitialState, truthExecutionEnv] using
    Ethereum.EVM.step_push1 truthNonpayableInitialState (⟨0x80⟩ : Ethereum.UInt256)
      truth_decode_pc0

theorem truth_nonpayable_xstep_pc2 :
    Ethereum.EVM.Xstep truthValidJumps truthNonpayableState1 =
      .ok (truthNonpayableState2, .none) := by
  simpa [truthValidJumps, truthNonpayableState1, truthNonpayableInitialState,
    truthNonpayableExecutionEnv, truthInitialState, truthExecutionEnv] using
    Ethereum.EVM.step_push1 truthNonpayableState1 (⟨0x40⟩ : Ethereum.UInt256)
      truth_decode_pc2

theorem truth_nonpayable_xstep_pc4 :
    Ethereum.EVM.Xstep truthValidJumps truthNonpayableState2 =
      .ok (truthNonpayableState3, .none) := by
  simpa [truthValidJumps, truthNonpayableState3] using
    Ethereum.EVM.step_mstore truthNonpayableState2 truth_decode_pc4

theorem truth_nonpayable_decode_pc5 :
    Ethereum.EVM.decode truthRuntimeBytecode truthNonpayableState3.machineState.pc =
      some (.CALLVALUE, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨5⟩ : Ethereum.UInt256) =
    some (.CALLVALUE, none)
  native_decide

theorem truth_nonpayable_xstep_pc5 :
    Ethereum.EVM.Xstep truthValidJumps truthNonpayableState3 =
      .ok (truthNonpayableState4, .none) := by
  simpa [truthValidJumps, truthNonpayableState4] using
    Ethereum.EVM.step_callvalue truthNonpayableState3 truth_nonpayable_decode_pc5

theorem truth_nonpayable_decode_pc6 :
    Ethereum.EVM.decode truthRuntimeBytecode truthNonpayableState4.machineState.pc =
      some (.DUP1, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨6⟩ : Ethereum.UInt256) =
    some (.DUP1, none)
  native_decide

theorem truth_nonpayable_xstep_pc6 :
    Ethereum.EVM.Xstep truthValidJumps truthNonpayableState4 =
      .ok (truthNonpayableState5, .none) := by
  simpa [truthValidJumps, truthNonpayableState5, truthNonpayableState4,
    truthNonpayableState3, truthNonpayableExecutionEnv] using
    Ethereum.EVM.step_dup1 truthNonpayableState4 truth_nonpayable_decode_pc6

theorem truth_nonpayable_decode_pc7 :
    Ethereum.EVM.decode truthRuntimeBytecode truthNonpayableState5.machineState.pc =
      some (.ISZERO, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨7⟩ : Ethereum.UInt256) =
    some (.ISZERO, none)
  native_decide

theorem truth_nonpayable_xstep_pc7 :
    Ethereum.EVM.Xstep truthValidJumps truthNonpayableState5 =
      .ok (truthNonpayableState6, .none) := by
  simpa [truthValidJumps, truthNonpayableState6, truthNonpayableState5] using
    Ethereum.EVM.step_iszero truthNonpayableState5 truth_nonpayable_decode_pc7

theorem truth_nonpayable_decode_pc8 :
    Ethereum.EVM.decode truthRuntimeBytecode truthNonpayableState6.machineState.pc =
      some (.PUSH1, some ((⟨0x0e⟩ : Ethereum.UInt256), 1)) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨8⟩ : Ethereum.UInt256) =
    some (.PUSH1, some ((⟨0x0e⟩ : Ethereum.UInt256), 1))
  native_decide

theorem truth_nonpayable_xstep_pc8 :
    Ethereum.EVM.Xstep truthValidJumps truthNonpayableState6 =
      .ok (truthNonpayableState7, .none) := by
  simpa [truthValidJumps, truthNonpayableState7] using
    Ethereum.EVM.step_push1 truthNonpayableState6 (⟨0x0e⟩ : Ethereum.UInt256)
      truth_nonpayable_decode_pc8

theorem truth_nonpayable_decode_pc10 :
    Ethereum.EVM.decode truthRuntimeBytecode truthNonpayableState7.machineState.pc =
      some (.JUMPI, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x0a⟩ : Ethereum.UInt256) =
    some (.JUMPI, none)
  native_decide

theorem truth_nonpayable_xstep_pc10 :
    Ethereum.EVM.Xstep truthValidJumps truthNonpayableState7 =
      .ok (truthNonpayableState8, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthNonpayableState7.executionEnv.code ⟨0⟩ by
    simp [truthValidJumps, truthNonpayableState7, truthNonpayableState6, truthNonpayableState5,
      truthNonpayableState4, truthNonpayableState3, truthNonpayableState2, truthNonpayableState1,
      truthNonpayableInitialState, truthNonpayableExecutionEnv, truthInitialState,
      truthExecutionEnv]]
  rw [Ethereum.EVM.step_jumpi truthNonpayableState7 truth_nonpayable_decode_pc10]
  simp [truthNonpayableState7, truthNonpayableState6, truthNonpayableState5,
    truthNonpayableState4, truthNonpayableState3]
  rw [truth_nonpayable_mstore_memoryExpansionCost]
  have hgas : ¬ ((truthNonpayableState2.machineState.gasAvailable - Ethereum.UInt256.ofNat 9 -
                                  Ethereum.UInt256.ofNat GasConstants.Gverylow -
                                Ethereum.UInt256.ofNat GasConstants.Gbase -
                              Ethereum.UInt256.ofNat GasConstants.Gverylow -
                            Ethereum.UInt256.ofNat GasConstants.Gverylow -
                          Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Ghigh) := by
    native_decide
  rw [if_neg hgas]
  have hzero : (((⟨0⟩ : Ethereum.UInt256) != (⟨0⟩ : Ethereum.UInt256)) = false) := by
    decide
  simp [truthNonpayableState8, truthNonpayableState7, truthNonpayableState6,
    truthNonpayableState5, truthNonpayableState4, truthNonpayableState3,
    truthNonpayableState2, truthNonpayableState1, truthNonpayableInitialState,
    truthNonpayableExecutionEnv, truthInitialState, truthExecutionEnv, hzero]
  native_decide

theorem truth_nonpayable_decode_pc11 :
    Ethereum.EVM.decode truthRuntimeBytecode truthNonpayableState8.machineState.pc =
      some (.PUSH0, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x0b⟩ : Ethereum.UInt256) =
    some (.PUSH0, none)
  native_decide

theorem truth_nonpayable_xstep_pc11 :
    Ethereum.EVM.Xstep truthValidJumps truthNonpayableState8 =
      .ok (truthNonpayableState9, .none) := by
  simpa [truthValidJumps, truthNonpayableState9] using
    Ethereum.EVM.step_push0 truthNonpayableState8 truth_nonpayable_decode_pc11

theorem truth_nonpayable_decode_pc12 :
    Ethereum.EVM.decode truthRuntimeBytecode truthNonpayableState9.machineState.pc =
      some (.PUSH0, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x0c⟩ : Ethereum.UInt256) =
    some (.PUSH0, none)
  native_decide

theorem truth_nonpayable_xstep_pc12 :
    Ethereum.EVM.Xstep truthValidJumps truthNonpayableState9 =
      .ok (truthNonpayableState10, .none) := by
  simpa [truthValidJumps, truthNonpayableState10] using
    Ethereum.EVM.step_push0 truthNonpayableState9 truth_nonpayable_decode_pc12

theorem truth_nonpayable_decode_pc13 :
    Ethereum.EVM.decode truthRuntimeBytecode truthNonpayableState10.machineState.pc =
      some (.REVERT, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x0d⟩ : Ethereum.UInt256) =
    some (.REVERT, none)
  native_decide

theorem truth_nonpayable_xstep_pc13 :
    Ethereum.EVM.Xstep truthValidJumps truthNonpayableState10 =
      .ok (truthNonpayableState11, .some (false, truthNonpayableReturnData)) := by
  rw [show truthValidJumps =
      Ethereum.EVM.D_J truthNonpayableState10.executionEnv.code ⟨0⟩ by
    simp [truthValidJumps, truthNonpayableState10, truthNonpayableState9,
      truthNonpayableState8, truthNonpayableState7, truthNonpayableState6,
      truthNonpayableState5, truthNonpayableState4, truthNonpayableState3,
      truthNonpayableState2, truthNonpayableState1, truthNonpayableInitialState,
      truthNonpayableExecutionEnv, truthInitialState, truthExecutionEnv]]
  rw [Ethereum.EVM.step_revert truthNonpayableState10 truth_nonpayable_decode_pc13]
  simp only [truthNonpayableState10, truthNonpayableState11, truthNonpayableReturnData]
  change (if truthNonpayableState10.machineState.gasAvailable.toNat <
      Ethereum.EVM.memoryExpansionCost truthNonpayableState10 .REVERT then _ else _) = _
  have hstack : truthNonpayableState10.machineState.stack =
      (⟨0⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) ::
        [(⟨1⟩ : Ethereum.UInt256)] := by
    simp [truthNonpayableState10, truthNonpayableState9, truthNonpayableState8]
  have hmem : ¬ truthNonpayableState10.machineState.gasAvailable.toNat <
      Ethereum.EVM.memoryExpansionCost truthNonpayableState10 .REVERT := by
    rw [truth_revert_zero_memoryExpansionCost_top truthNonpayableState10
      [(⟨1⟩ : Ethereum.UInt256)] hstack]
    simp
  rw [if_neg hmem]
  have hoverflow :
      ¬ ((⟨0⟩ : Ethereum.UInt256) :: truthNonpayableState9.machineState.stack).length - 2 + 0 >
        1024 := by
    simp [truthNonpayableState9, truthNonpayableState8]
  rw [if_neg hoverflow]
  simp [truthNonpayableState9, truthNonpayableState8, Ethereum.UInt256.toNat,
    Ethereum.MachineState.M]
  change Ethereum.UInt256.ofNat
      (Ethereum.UInt256.ofNat truthNonpayableState9.machineState.activeWords.toNat).toNat =
    Ethereum.UInt256.ofNat truthNonpayableState9.machineState.activeWords.toNat
  exact truth_uint256_ofNat_ofNat_toNat truthNonpayableState9.machineState.activeWords.toNat

theorem truth_short_xstep_pc0 :
    Ethereum.EVM.Xstep truthValidJumps truthShortInitialState =
      .ok (truthShortState1, .none) := by
  simpa [truthValidJumps, truthShortInitialState, truthShortExecutionEnv, truthInitialState,
    truthExecutionEnv] using
    Ethereum.EVM.step_push1 truthShortInitialState (⟨0x80⟩ : Ethereum.UInt256) truth_decode_pc0

theorem truth_short_xstep_pc2 :
    Ethereum.EVM.Xstep truthValidJumps truthShortState1 =
      .ok (truthShortState2, .none) := by
  simpa [truthValidJumps, truthShortState1, truthShortInitialState, truthShortExecutionEnv,
    truthInitialState, truthExecutionEnv] using
    Ethereum.EVM.step_push1 truthShortState1 (⟨0x40⟩ : Ethereum.UInt256) truth_decode_pc2

theorem truth_short_xstep_pc4 :
    Ethereum.EVM.Xstep truthValidJumps truthShortState2 =
      .ok (truthShortState3, .none) := by
  simpa [truthValidJumps, truthShortState3] using
    Ethereum.EVM.step_mstore truthShortState2 truth_decode_pc4

theorem truth_short_decode_pc5 :
    Ethereum.EVM.decode truthRuntimeBytecode truthShortState3.machineState.pc =
      some (.CALLVALUE, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨5⟩ : Ethereum.UInt256) =
    some (.CALLVALUE, none)
  native_decide

theorem truth_short_xstep_pc5 :
    Ethereum.EVM.Xstep truthValidJumps truthShortState3 =
      .ok (truthShortState4, .none) := by
  simpa [truthValidJumps, truthShortState4] using
    Ethereum.EVM.step_callvalue truthShortState3 truth_short_decode_pc5

theorem truth_short_decode_pc6 :
    Ethereum.EVM.decode truthRuntimeBytecode truthShortState4.machineState.pc =
      some (.DUP1, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨6⟩ : Ethereum.UInt256) =
    some (.DUP1, none)
  native_decide

theorem truth_short_xstep_pc6 :
    Ethereum.EVM.Xstep truthValidJumps truthShortState4 =
      .ok (truthShortState5, .none) := by
  simpa [truthValidJumps, truthShortState5, truthShortState4, truthShortState3,
    truthShortExecutionEnv] using
    Ethereum.EVM.step_dup1 truthShortState4 truth_short_decode_pc6

theorem truth_short_decode_pc7 :
    Ethereum.EVM.decode truthRuntimeBytecode truthShortState5.machineState.pc =
      some (.ISZERO, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨7⟩ : Ethereum.UInt256) =
    some (.ISZERO, none)
  native_decide

theorem truth_short_xstep_pc7 :
    Ethereum.EVM.Xstep truthValidJumps truthShortState5 =
      .ok (truthShortState6, .none) := by
  simpa [truthValidJumps, truthShortState6, truthShortState5] using
    Ethereum.EVM.step_iszero truthShortState5 truth_short_decode_pc7

theorem truth_short_decode_pc8 :
    Ethereum.EVM.decode truthRuntimeBytecode truthShortState6.machineState.pc =
      some (.PUSH1, some ((⟨0x0e⟩ : Ethereum.UInt256), 1)) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨8⟩ : Ethereum.UInt256) =
    some (.PUSH1, some ((⟨0x0e⟩ : Ethereum.UInt256), 1))
  native_decide

theorem truth_short_xstep_pc8 :
    Ethereum.EVM.Xstep truthValidJumps truthShortState6 =
      .ok (truthShortState7, .none) := by
  simpa [truthValidJumps, truthShortState7] using
    Ethereum.EVM.step_push1 truthShortState6 (⟨0x0e⟩ : Ethereum.UInt256) truth_short_decode_pc8

theorem truth_short_decode_pc10 :
    Ethereum.EVM.decode truthRuntimeBytecode truthShortState7.machineState.pc =
      some (.JUMPI, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x0a⟩ : Ethereum.UInt256) =
    some (.JUMPI, none)
  native_decide

theorem truth_short_xstep_pc10 :
    Ethereum.EVM.Xstep truthValidJumps truthShortState7 =
      .ok (truthShortState8, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthShortState7.executionEnv.code ⟨0⟩ by
    simp [truthValidJumps, truthShortState7, truthShortState6, truthShortState5,
      truthShortState4, truthShortState3, truthShortState2, truthShortState1,
      truthShortInitialState, truthShortExecutionEnv, truthInitialState, truthExecutionEnv]]
  rw [Ethereum.EVM.step_jumpi truthShortState7 truth_short_decode_pc10]
  simp [truthShortState7, truthShortState6, truthShortState5, truthShortState4,
    truthShortState3]
  rw [truth_short_mstore_memoryExpansionCost]
  have hgas : ¬ ((truthShortState2.machineState.gasAvailable - Ethereum.UInt256.ofNat 9 -
                                  Ethereum.UInt256.ofNat GasConstants.Gverylow -
                                Ethereum.UInt256.ofNat GasConstants.Gbase -
                              Ethereum.UInt256.ofNat GasConstants.Gverylow -
                            Ethereum.UInt256.ofNat GasConstants.Gverylow -
                          Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Ghigh) := by
    native_decide
  rw [if_neg hgas]
  have hbad : ¬ ((({ val := 1 } : Ethereum.UInt256) != { val := 0 }) = true ∧
      (Ethereum.EVM.D_J truthShortState2.executionEnv.code { val := 0 }).contains { val := 14 } = false) := by
    have hcode : truthShortState2.executionEnv.code = truthRuntimeBytecode := by
      simp [truthShortState2, truthShortState1, truthShortInitialState, truthShortExecutionEnv,
        truthInitialState, truthExecutionEnv]
    rw [hcode]
    simp [truth_valid_jumpdest_0e]
  rw [if_neg hbad]
  simp [truthShortState8, truthShortState7, truthShortState6, truthShortState5,
    truthShortState4, truthShortState3]
  constructor
  · native_decide
  · rw [truth_short_mstore_memoryExpansionCost]

theorem truth_short_decode_pc14 :
    Ethereum.EVM.decode truthRuntimeBytecode truthShortState8.machineState.pc =
      some (.JUMPDEST, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x0e⟩ : Ethereum.UInt256) =
    some (.JUMPDEST, none)
  native_decide

theorem truth_short_xstep_pc14 :
    Ethereum.EVM.Xstep truthValidJumps truthShortState8 =
      .ok (truthShortState9, .none) := by
  simpa [truthValidJumps, truthShortState9, truthShortState8] using
    Ethereum.EVM.step_jumpdest truthShortState8 truth_short_decode_pc14

theorem truth_short_decode_pc15 :
    Ethereum.EVM.decode truthRuntimeBytecode truthShortState9.machineState.pc =
      some (.POP, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x0f⟩ : Ethereum.UInt256) =
    some (.POP, none)
  native_decide

theorem truth_short_xstep_pc15 :
    Ethereum.EVM.Xstep truthValidJumps truthShortState9 =
      .ok (truthShortState10, .none) := by
  simpa [truthValidJumps, truthShortState10, truthShortState9] using
    Ethereum.EVM.step_pop truthShortState9 truth_short_decode_pc15

theorem truth_short_decode_pc16 :
    Ethereum.EVM.decode truthRuntimeBytecode truthShortState10.machineState.pc =
      some (.PUSH1, some ((⟨0x04⟩ : Ethereum.UInt256), 1)) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x10⟩ : Ethereum.UInt256) =
    some (.PUSH1, some ((⟨0x04⟩ : Ethereum.UInt256), 1))
  native_decide

theorem truth_short_xstep_pc16 :
    Ethereum.EVM.Xstep truthValidJumps truthShortState10 =
      .ok (truthShortState11, .none) := by
  simpa [truthValidJumps, truthShortState11] using
    Ethereum.EVM.step_push1 truthShortState10 (⟨0x04⟩ : Ethereum.UInt256) truth_short_decode_pc16

theorem truth_short_decode_pc18 :
    Ethereum.EVM.decode truthRuntimeBytecode truthShortState11.machineState.pc =
      some (.CALLDATASIZE, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x12⟩ : Ethereum.UInt256) =
    some (.CALLDATASIZE, none)
  native_decide

theorem truth_short_xstep_pc18 :
    Ethereum.EVM.Xstep truthValidJumps truthShortState11 =
      .ok (truthShortState12, .none) := by
  simpa [truthValidJumps, truthShortState12] using
    Ethereum.EVM.step_calldatasize truthShortState11 truth_short_decode_pc18

theorem truth_short_decode_pc19 :
    Ethereum.EVM.decode truthRuntimeBytecode truthShortState12.machineState.pc =
      some (.LT, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x13⟩ : Ethereum.UInt256) =
    some (.LT, none)
  native_decide

theorem truth_short_xstep_pc19 :
    Ethereum.EVM.Xstep truthValidJumps truthShortState12 =
      .ok (truthShortState13, .none) := by
  simpa [truthValidJumps, truthShortState13, truthShortState12, truthShortState11,
    truthShortExecutionEnv, truthShortCallData] using
    Ethereum.EVM.step_lt truthShortState12 truth_short_decode_pc19

theorem truth_short_decode_pc20 :
    Ethereum.EVM.decode truthRuntimeBytecode truthShortState13.machineState.pc =
      some (.PUSH1, some ((⟨0x26⟩ : Ethereum.UInt256), 1)) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x14⟩ : Ethereum.UInt256) =
    some (.PUSH1, some ((⟨0x26⟩ : Ethereum.UInt256), 1))
  native_decide

theorem truth_short_xstep_pc20 :
    Ethereum.EVM.Xstep truthValidJumps truthShortState13 =
      .ok (truthShortState14, .none) := by
  simpa [truthValidJumps, truthShortState14] using
    Ethereum.EVM.step_push1 truthShortState13 (⟨0x26⟩ : Ethereum.UInt256) truth_short_decode_pc20

theorem truth_short_decode_pc22 :
    Ethereum.EVM.decode truthRuntimeBytecode truthShortState14.machineState.pc =
      some (.JUMPI, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x16⟩ : Ethereum.UInt256) =
    some (.JUMPI, none)
  native_decide

theorem truth_valid_jumpdest_26 :
    (Ethereum.EVM.D_J truthRuntimeBytecode ⟨0⟩).contains (⟨0x26⟩ : Ethereum.UInt256) = true := by
  native_decide

theorem truth_short_xstep_pc22 :
    Ethereum.EVM.Xstep truthValidJumps truthShortState14 =
      .ok (truthShortState15, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthShortState14.executionEnv.code ⟨0⟩ by
    simp [truthValidJumps, truthShortState14, truthShortState13, truthShortState12,
      truthShortState11, truthShortState10, truthShortState9, truthShortState8,
      truthShortState7, truthShortState6, truthShortState5, truthShortState4,
      truthShortState3, truthShortState2, truthShortState1, truthShortInitialState,
      truthShortExecutionEnv, truthInitialState, truthExecutionEnv]]
  rw [Ethereum.EVM.step_jumpi truthShortState14 truth_short_decode_pc22]
  simp [truthShortState14, truthShortState13]
  have hgas : ¬ ((truthShortState12.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow -
      Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Ghigh) := by
    simp only [truthShortState12, truthShortState11, truthShortState10, truthShortState9,
      truthShortState8, truthShortState7, truthShortState6, truthShortState5,
      truthShortState4, truthShortState3]
    rw [truth_short_mstore_memoryExpansionCost]
    native_decide
  rw [if_neg hgas]
  have hcontains :
      (Ethereum.EVM.D_J truthShortState12.executionEnv.code ⟨0⟩).contains
        (⟨0x26⟩ : Ethereum.UInt256) = true := by
    have hcode : truthShortState12.executionEnv.code = truthRuntimeBytecode := by
      simp [truthShortState12, truthShortState11, truthShortState10, truthShortState9,
        truthShortState8, truthShortState7, truthShortState6, truthShortState5,
        truthShortState4, truthShortState3, truthShortState2, truthShortState1,
        truthShortInitialState, truthShortExecutionEnv, truthInitialState, truthExecutionEnv]
    rw [hcode]
    exact truth_valid_jumpdest_26
  rw [hcontains]
  have hnonzero : (((⟨1⟩ : Ethereum.UInt256) != (⟨0⟩ : Ethereum.UInt256)) = true) := by
    native_decide
  simp [truthShortState15, truthShortState14, truthShortState13, hnonzero]

theorem truth_short_decode_pc38 :
    Ethereum.EVM.decode truthRuntimeBytecode truthShortState15.machineState.pc =
      some (.JUMPDEST, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x26⟩ : Ethereum.UInt256) =
    some (.JUMPDEST, none)
  native_decide

theorem truth_short_xstep_pc38 :
    Ethereum.EVM.Xstep truthValidJumps truthShortState15 =
      .ok (truthShortState16, .none) := by
  simpa [truthValidJumps, truthShortState16, truthShortState15] using
    Ethereum.EVM.step_jumpdest truthShortState15 truth_short_decode_pc38

theorem truth_short_decode_pc39 :
    Ethereum.EVM.decode truthRuntimeBytecode truthShortState16.machineState.pc =
      some (.PUSH0, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x27⟩ : Ethereum.UInt256) =
    some (.PUSH0, none)
  native_decide

theorem truth_short_xstep_pc39 :
    Ethereum.EVM.Xstep truthValidJumps truthShortState16 =
      .ok (truthShortState17, .none) := by
  simpa [truthValidJumps, truthShortState17] using
    Ethereum.EVM.step_push0 truthShortState16 truth_short_decode_pc39

theorem truth_short_decode_pc40 :
    Ethereum.EVM.decode truthRuntimeBytecode truthShortState17.machineState.pc =
      some (.PUSH0, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x28⟩ : Ethereum.UInt256) =
    some (.PUSH0, none)
  native_decide

theorem truth_short_xstep_pc40 :
    Ethereum.EVM.Xstep truthValidJumps truthShortState17 =
      .ok (truthShortState18, .none) := by
  simpa [truthValidJumps, truthShortState18] using
    Ethereum.EVM.step_push0 truthShortState17 truth_short_decode_pc40

theorem truth_short_decode_pc41 :
    Ethereum.EVM.decode truthRuntimeBytecode truthShortState18.machineState.pc =
      some (.REVERT, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x29⟩ : Ethereum.UInt256) =
    some (.REVERT, none)
  native_decide

theorem truth_short_xstep_pc41 :
    Ethereum.EVM.Xstep truthValidJumps truthShortState18 =
      .ok (truthShortState19, .some (false, truthShortReturnData)) := by
  rw [show truthValidJumps =
      Ethereum.EVM.D_J truthShortState18.executionEnv.code ⟨0⟩ by
    simp [truthValidJumps, truthShortState18, truthShortState17, truthShortState16,
      truthShortState15, truthShortState14, truthShortState13, truthShortState12,
      truthShortState11, truthShortState10, truthShortState9, truthShortState8,
      truthShortState7, truthShortState6, truthShortState5, truthShortState4,
      truthShortState3, truthShortState2, truthShortState1, truthShortInitialState,
      truthShortExecutionEnv, truthInitialState, truthExecutionEnv]]
  rw [Ethereum.EVM.step_revert truthShortState18 truth_short_decode_pc41]
  simp only [truthShortState18, truthShortState19, truthShortReturnData]
  change (if truthShortState18.machineState.gasAvailable.toNat <
      Ethereum.EVM.memoryExpansionCost truthShortState18 .REVERT then _ else _) = _
  have hstack : truthShortState18.machineState.stack =
      [(⟨0⟩ : Ethereum.UInt256), (⟨0⟩ : Ethereum.UInt256)] := by
    simp [truthShortState18, truthShortState17, truthShortState16, truthShortState15]
  have hmem : ¬ truthShortState18.machineState.gasAvailable.toNat <
      Ethereum.EVM.memoryExpansionCost truthShortState18 .REVERT := by
    rw [truth_revert_zero_memoryExpansionCost truthShortState18 hstack]
    simp
  rw [if_neg hmem]
  have hoverflow :
      ¬ ((⟨0⟩ : Ethereum.UInt256) :: truthShortState17.machineState.stack).length - 2 + 0 >
        1024 := by
    simp [truthShortState17, truthShortState16, truthShortState15]
  rw [if_neg hoverflow]
  simp [truthShortState16, truthShortState15, Ethereum.UInt256.toNat, Ethereum.MachineState.M]
  change Ethereum.UInt256.ofNat
      (Ethereum.UInt256.ofNat truthShortState17.machineState.activeWords.toNat).toNat =
    Ethereum.UInt256.ofNat truthShortState17.machineState.activeWords.toNat
  exact truth_uint256_ofNat_ofNat_toNat truthShortState17.machineState.activeWords.toNat

theorem truth_short_xstep_pc38_to_revert (f : Nat) :
    Ethereum.EVM.X (f + 4) truthValidJumps truthShortState15 =
      .ok (.revert truthShortState19.machineState.gasAvailable truthShortReturnData) := by
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact truth_short_xstep_pc38
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact truth_short_xstep_pc39
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact truth_short_xstep_pc40
  apply Ethereum.EVM.Xstep_X_X_halt_revert
  exact truth_short_xstep_pc41

theorem truth_decode_pc14 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState8.machineState.pc =
      some (.JUMPDEST, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x0e⟩ : Ethereum.UInt256) =
    some (.JUMPDEST, none)
  native_decide

theorem truth_xstep_pc14 :
    Ethereum.EVM.Xstep truthValidJumps truthState8 =
      .ok (truthState9, .none) := by
  simpa [truthValidJumps, truthState9, truthState8] using
    Ethereum.EVM.step_jumpdest truthState8 truth_decode_pc14

theorem truth_decode_pc15 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState9.machineState.pc =
      some (.POP, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x0f⟩ : Ethereum.UInt256) =
    some (.POP, none)
  native_decide

theorem truth_xstep_pc15 :
    Ethereum.EVM.Xstep truthValidJumps truthState9 =
      .ok (truthState10, .none) := by
  simpa [truthValidJumps, truthState10, truthState9] using
    Ethereum.EVM.step_pop truthState9 truth_decode_pc15

theorem truth_decode_pc16 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState10.machineState.pc =
      some (.PUSH1, some ((⟨0x04⟩ : Ethereum.UInt256), 1)) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x10⟩ : Ethereum.UInt256) =
    some (.PUSH1, some ((⟨0x04⟩ : Ethereum.UInt256), 1))
  native_decide

theorem truth_xstep_pc16 :
    Ethereum.EVM.Xstep truthValidJumps truthState10 =
      .ok (truthState11, .none) := by
  simpa [truthValidJumps, truthState11] using
    Ethereum.EVM.step_push1 truthState10 (⟨0x04⟩ : Ethereum.UInt256) truth_decode_pc16

theorem truth_decode_pc18 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState11.machineState.pc =
      some (.CALLDATASIZE, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x12⟩ : Ethereum.UInt256) =
    some (.CALLDATASIZE, none)
  native_decide

theorem truth_xstep_pc18 :
    Ethereum.EVM.Xstep truthValidJumps truthState11 =
      .ok (truthState12, .none) := by
  simpa [truthValidJumps, truthState12] using
    Ethereum.EVM.step_calldatasize truthState11 truth_decode_pc18

theorem truth_decode_pc19 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState12.machineState.pc =
      some (.LT, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x13⟩ : Ethereum.UInt256) =
    some (.LT, none)
  native_decide

theorem truth_xstep_pc19 :
    Ethereum.EVM.Xstep truthValidJumps truthState12 =
      .ok (truthState13, .none) := by
  simpa [truthValidJumps, truthState13, truthState12, truthState11, truthExecutionEnv, truthCallData,
    truthSelector] using
    Ethereum.EVM.step_lt truthState12 truth_decode_pc19

theorem truth_decode_pc20 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState13.machineState.pc =
      some (.PUSH1, some ((⟨0x26⟩ : Ethereum.UInt256), 1)) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x14⟩ : Ethereum.UInt256) =
    some (.PUSH1, some ((⟨0x26⟩ : Ethereum.UInt256), 1))
  native_decide

theorem truth_xstep_pc20 :
    Ethereum.EVM.Xstep truthValidJumps truthState13 =
      .ok (truthState14, .none) := by
  simpa [truthValidJumps, truthState14] using
    Ethereum.EVM.step_push1 truthState13 (⟨0x26⟩ : Ethereum.UInt256) truth_decode_pc20

theorem truth_decode_pc22 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState14.machineState.pc =
      some (.JUMPI, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x16⟩ : Ethereum.UInt256) =
    some (.JUMPI, none)
  native_decide

theorem truth_xstep_pc22 :
    Ethereum.EVM.Xstep truthValidJumps truthState14 =
      .ok (truthState15, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthState14.executionEnv.code ⟨0⟩ by
    simp [truthValidJumps, truthState14, truthState13, truthState12, truthState11, truthState10,
      truthState9, truthState8, truthState7, truthState6, truthState5, truthState4,
      truthState3, truthState2, truthState1, truthInitialState, truthExecutionEnv]]
  rw [Ethereum.EVM.step_jumpi truthState14 truth_decode_pc22]
  simp [truthState14, truthState13]
  have hgas : ¬ ((truthState12.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow -
      Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Ghigh) := by
    simp only [truthState12, truthState11, truthState10, truthState9, truthState8, truthState7,
      truthState6, truthState5, truthState4, truthState3]
    rw [truth_mstore_memoryExpansionCost]
    native_decide
  rw [if_neg hgas]
  have hzero : (((⟨0⟩ : Ethereum.UInt256) != (⟨0⟩ : Ethereum.UInt256)) = false) := by
    decide
  simp [truthState15, truthState14, truthState13, hzero]

theorem truth_decode_pc23 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState15.machineState.pc =
      some (.PUSH0, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x17⟩ : Ethereum.UInt256) =
    some (.PUSH0, none)
  native_decide

theorem truth_xstep_pc23 :
    Ethereum.EVM.Xstep truthValidJumps truthState15 =
      .ok (truthState16, .none) := by
  simpa [truthValidJumps, truthState16] using
    Ethereum.EVM.step_push0 truthState15 truth_decode_pc23

theorem truth_decode_pc24 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState16.machineState.pc =
      some (.CALLDATALOAD, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x18⟩ : Ethereum.UInt256) =
    some (.CALLDATALOAD, none)
  native_decide

theorem truth_xstep_pc24 :
    Ethereum.EVM.Xstep truthValidJumps truthState16 =
      .ok (truthState17, .none) := by
  simpa [truthValidJumps, truthState17, truthCalldataWord] using
    Ethereum.EVM.step_calldataload truthState16 truth_decode_pc24

theorem truth_decode_pc25 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState17.machineState.pc =
      some (.PUSH1, some ((⟨0xe0⟩ : Ethereum.UInt256), 1)) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x19⟩ : Ethereum.UInt256) =
    some (.PUSH1, some ((⟨0xe0⟩ : Ethereum.UInt256), 1))
  native_decide

theorem truth_xstep_pc25 :
    Ethereum.EVM.Xstep truthValidJumps truthState17 =
      .ok (truthState18, .none) := by
  simpa [truthValidJumps, truthState18] using
    Ethereum.EVM.step_push1 truthState17 (⟨0xe0⟩ : Ethereum.UInt256) truth_decode_pc25

theorem truth_decode_pc27 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState18.machineState.pc =
      some (.SHR, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x1b⟩ : Ethereum.UInt256) =
    some (.SHR, none)
  native_decide

theorem truth_xstep_pc27 :
    Ethereum.EVM.Xstep truthValidJumps truthState18 =
      .ok (truthState19, .none) := by
  simpa [truthValidJumps, truthState19, truthSelectorWord] using
    Ethereum.EVM.step_shr truthState18 truth_decode_pc27

theorem truth_decode_pc28 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState19.machineState.pc =
      some (.DUP1, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x1c⟩ : Ethereum.UInt256) =
    some (.DUP1, none)
  native_decide

theorem truth_xstep_pc28 :
    Ethereum.EVM.Xstep truthValidJumps truthState19 =
      .ok (truthState20, .none) := by
  simpa [truthValidJumps, truthState20] using
    Ethereum.EVM.step_dup1 truthState19 truth_decode_pc28

theorem truth_decode_pc29 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState20.machineState.pc =
      some (.PUSH4, some (truthExpectedSelectorWord, 4)) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x1d⟩ : Ethereum.UInt256) =
    some (.PUSH4, some (truthExpectedSelectorWord, 4))
  native_decide

theorem truth_xstep_pc29 :
    Ethereum.EVM.Xstep truthValidJumps truthState20 =
      .ok (truthState21, .none) := by
  simpa [truthValidJumps, truthState21, truthExpectedSelectorWord] using
    Ethereum.EVM.step_push4 truthState20 truthExpectedSelectorWord truth_decode_pc29

theorem truth_decode_pc34 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState21.machineState.pc =
      some (.EQ, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x22⟩ : Ethereum.UInt256) =
    some (.EQ, none)
  native_decide

theorem truth_xstep_pc34 :
    Ethereum.EVM.Xstep truthValidJumps truthState21 =
      .ok (truthState22, .none) := by
  simpa [truthValidJumps, truthState22, truthSelectorEqWord] using
    Ethereum.EVM.step_eq truthState21 truth_decode_pc34

theorem truth_decode_pc35 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState22.machineState.pc =
      some (.PUSH1, some ((⟨0x2a⟩ : Ethereum.UInt256), 1)) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x23⟩ : Ethereum.UInt256) =
    some (.PUSH1, some ((⟨0x2a⟩ : Ethereum.UInt256), 1))
  native_decide

theorem truth_xstep_pc35 :
    Ethereum.EVM.Xstep truthValidJumps truthState22 =
      .ok (truthState23, .none) := by
  simpa [truthValidJumps, truthState23] using
    Ethereum.EVM.step_push1 truthState22 (⟨0x2a⟩ : Ethereum.UInt256) truth_decode_pc35

theorem truth_selector_eq_word_eq_one :
    truthSelectorEqWord = (⟨1⟩ : Ethereum.UInt256) := by
  unfold truthSelectorEqWord
  rw [truth_selector_word_eq]
  native_decide

theorem truth_selector_eq_word_nonzero :
    (truthSelectorEqWord != (⟨0⟩ : Ethereum.UInt256)) = true := by
  rw [truth_selector_eq_word_eq_one]
  native_decide

theorem truth_valid_jumpdest_2a :
    (Ethereum.EVM.D_J truthRuntimeBytecode ⟨0⟩).contains (⟨0x2a⟩ : Ethereum.UInt256) = true := by
  native_decide

theorem truth_decode_pc37 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState23.machineState.pc =
      some (.JUMPI, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x25⟩ : Ethereum.UInt256) =
    some (.JUMPI, none)
  native_decide

theorem truth_xstep_pc37 :
    Ethereum.EVM.Xstep truthValidJumps truthState23 =
      .ok (truthState24, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthState23.executionEnv.code ⟨0⟩ by
    simp [truthValidJumps, truthState23, truthState22, truthState21, truthState20,
      truthState19, truthState18, truthState17, truthState16, truthState15, truthState14,
      truthState13, truthState12, truthState11, truthState10, truthState9, truthState8,
      truthState7, truthState6, truthState5, truthState4, truthState3, truthState2,
      truthState1, truthInitialState, truthExecutionEnv]]
  rw [Ethereum.EVM.step_jumpi truthState23 truth_decode_pc37]
  simp [truthState23, truthState22, truth_selector_eq_word_nonzero]
  have hgas : ¬ truthState23.machineState.gasAvailable.toNat < GasConstants.Ghigh := by
    simp only [truthState23, truthState22, truthState21, truthState20, truthState19,
      truthState18, truthState17, truthState16, truthState15, truthState14, truthState13,
      truthState12, truthState11, truthState10, truthState9, truthState8, truthState7,
      truthState6, truthState5, truthState4, truthState3]
    rw [truth_mstore_memoryExpansionCost]
    native_decide
  have hgas' :
      ¬ (truthState21.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow -
        Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Ghigh := by
    simpa [truthState23, truthState22] using hgas
  rw [if_neg hgas']
  have hcontains :
      (Ethereum.EVM.D_J truthState21.executionEnv.code ⟨0⟩).contains
        (⟨0x2a⟩ : Ethereum.UInt256) = true := by
    have hcode : truthState21.executionEnv.code = truthRuntimeBytecode := by
      simp [truthState21, truthState20, truthState19, truthState18, truthState17,
        truthState16, truthState15, truthState14, truthState13, truthState12, truthState11,
        truthState10, truthState9, truthState8, truthState7, truthState6, truthState5,
        truthState4, truthState3, truthState2, truthState1, truthInitialState, truthExecutionEnv]
    rw [hcode]
    exact truth_valid_jumpdest_2a
  rw [hcontains]
  simp [truthState24, truthState23, truthState22]

theorem truth_mismatch_xstep_pc0 :
    Ethereum.EVM.Xstep truthValidJumps truthMismatchInitialState =
      .ok (truthMismatchState1, .none) := by
  simpa [truthValidJumps, truthMismatchInitialState, truthMismatchState1,
    truthMismatchExecutionEnv, truthState1, truthInitialState, truthExecutionEnv] using
    Ethereum.EVM.step_push1 truthMismatchInitialState (⟨0x80⟩ : Ethereum.UInt256) truth_decode_pc0

theorem truth_mismatch_xstep_pc2 :
    Ethereum.EVM.Xstep truthValidJumps truthMismatchState1 =
      .ok (truthMismatchState2, .none) := by
  simpa [truthValidJumps, truthMismatchState1, truthMismatchState2, truthState1,
    truthState2, truthMismatchExecutionEnv, truthInitialState, truthExecutionEnv] using
    Ethereum.EVM.step_push1 truthMismatchState1 (⟨0x40⟩ : Ethereum.UInt256) truth_decode_pc2

theorem truth_mismatch_xstep_pc4 :
    Ethereum.EVM.Xstep truthValidJumps truthMismatchState2 =
      .ok (truthMismatchState3, .none) := by
  simpa [truthValidJumps, truthMismatchState2, truthMismatchState3, truthState2,
    truthState3] using
    Ethereum.EVM.step_mstore truthMismatchState2 truth_decode_pc4

theorem truth_mismatch_xstep_pc5 :
    Ethereum.EVM.Xstep truthValidJumps truthMismatchState3 =
      .ok (truthMismatchState4, .none) := by
  simpa [truthValidJumps, truthMismatchState3, truthMismatchState4, truthState3,
    truthState4, truthMismatchExecutionEnv] using
    Ethereum.EVM.step_callvalue truthMismatchState3 truth_decode_pc5

theorem truth_mismatch_xstep_pc6 :
    Ethereum.EVM.Xstep truthValidJumps truthMismatchState4 =
      .ok (truthMismatchState5, .none) := by
  simpa [truthValidJumps, truthMismatchState4, truthMismatchState5, truthState4,
    truthState5, truthMismatchExecutionEnv] using
    Ethereum.EVM.step_dup1 truthMismatchState4 truth_decode_pc6

theorem truth_mismatch_xstep_pc7 :
    Ethereum.EVM.Xstep truthValidJumps truthMismatchState5 =
      .ok (truthMismatchState6, .none) := by
  simpa [truthValidJumps, truthMismatchState5, truthMismatchState6, truthState5,
    truthState6] using
    Ethereum.EVM.step_iszero truthMismatchState5 truth_decode_pc7

theorem truth_mismatch_xstep_pc8 :
    Ethereum.EVM.Xstep truthValidJumps truthMismatchState6 =
      .ok (truthMismatchState7, .none) := by
  simpa [truthValidJumps, truthMismatchState6, truthMismatchState7, truthState6,
    truthState7] using
    Ethereum.EVM.step_push1 truthMismatchState6 (⟨0x0e⟩ : Ethereum.UInt256) truth_decode_pc8

theorem truth_mismatch_xstep_pc10 :
    Ethereum.EVM.Xstep truthValidJumps truthMismatchState7 =
      .ok (truthMismatchState8, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthMismatchState7.executionEnv.code ⟨0⟩ by
    simp [truthValidJumps, truthMismatchState7, truthMismatchState6, truthMismatchState5,
      truthMismatchState4, truthMismatchState3, truthMismatchState2, truthMismatchState1,
      truthMismatchInitialState, truthMismatchExecutionEnv, truthExecutionEnv]]
  rw [Ethereum.EVM.step_jumpi truthMismatchState7 (by
    simpa [truthMismatchState7, truthMismatchState6, truthMismatchState5, truthMismatchState4,
      truthMismatchState3, truthMismatchState2, truthMismatchState1, truthMismatchInitialState,
      truthMismatchExecutionEnv] using truth_decode_pc10)]
  simp [truthMismatchState7, truthMismatchState6, truthMismatchState5, truthMismatchState4,
    truthMismatchState3, truthState7, truthState6, truthState5, truthState4, truthState3]
  rw [truth_mstore_memoryExpansionCost]
  have hgas : ¬ ((truthState2.machineState.gasAvailable - Ethereum.UInt256.ofNat 9 -
                                  Ethereum.UInt256.ofNat GasConstants.Gverylow -
                                Ethereum.UInt256.ofNat GasConstants.Gbase -
                              Ethereum.UInt256.ofNat GasConstants.Gverylow -
                            Ethereum.UInt256.ofNat GasConstants.Gverylow -
                          Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Ghigh) := by
    native_decide
  rw [if_neg hgas]
  have hbad : ¬ ((({ val := 1 } : Ethereum.UInt256) != { val := 0 }) = true ∧
      (Ethereum.EVM.D_J truthMismatchExecutionEnv.code { val := 0 }).contains { val := 14 } = false) := by
    have hcode : truthMismatchExecutionEnv.code = truthRuntimeBytecode := by
      simp [truthMismatchExecutionEnv, truthExecutionEnv]
    rw [hcode]
    simp [truth_valid_jumpdest_0e]
  rw [if_neg hbad]
  simp [truthMismatchState8, truthMismatchState7, truthMismatchState6, truthMismatchState5,
    truthMismatchState4, truthMismatchState3, truthState8, truthState7, truthState6,
    truthState5, truthState4, truthState3]
  rw [truth_mstore_memoryExpansionCost]
  native_decide

theorem truth_mismatch_xstep_pc14 :
    Ethereum.EVM.Xstep truthValidJumps truthMismatchState8 =
      .ok (truthMismatchState9, .none) := by
  simpa [truthValidJumps, truthMismatchState8, truthMismatchState9, truthState8,
    truthState9] using
    Ethereum.EVM.step_jumpdest truthMismatchState8 truth_decode_pc14

theorem truth_mismatch_xstep_pc15 :
    Ethereum.EVM.Xstep truthValidJumps truthMismatchState9 =
      .ok (truthMismatchState10, .none) := by
  simpa [truthValidJumps, truthMismatchState9, truthMismatchState10, truthState9,
    truthState10] using
    Ethereum.EVM.step_pop truthMismatchState9 truth_decode_pc15

theorem truth_mismatch_xstep_pc16 :
    Ethereum.EVM.Xstep truthValidJumps truthMismatchState10 =
      .ok (truthMismatchState11, .none) := by
  simpa [truthValidJumps, truthMismatchState10, truthMismatchState11, truthState10,
    truthState11] using
    Ethereum.EVM.step_push1 truthMismatchState10 (⟨0x04⟩ : Ethereum.UInt256) truth_decode_pc16

theorem truth_mismatch_xstep_pc18 :
    Ethereum.EVM.Xstep truthValidJumps truthMismatchState11 =
      .ok (truthMismatchState12, .none) := by
  simpa [truthValidJumps, truthMismatchState11, truthMismatchState12, truthState11,
    truthState12, truthMismatchExecutionEnv, truthMismatchCallData, truthCallData,
    truthSelector] using
    Ethereum.EVM.step_calldatasize truthMismatchState11 truth_decode_pc18

theorem truth_mismatch_xstep_pc19 :
    Ethereum.EVM.Xstep truthValidJumps truthMismatchState12 =
      .ok (truthMismatchState13, .none) := by
  simpa [truthValidJumps, truthMismatchState12, truthMismatchState13, truthState12,
    truthState13, truthMismatchExecutionEnv, truthMismatchCallData, truthCallData,
    truthSelector] using
    Ethereum.EVM.step_lt truthMismatchState12 truth_decode_pc19

theorem truth_mismatch_xstep_pc20 :
    Ethereum.EVM.Xstep truthValidJumps truthMismatchState13 =
      .ok (truthMismatchState14, .none) := by
  simpa [truthValidJumps, truthMismatchState13, truthMismatchState14, truthState13,
    truthState14] using
    Ethereum.EVM.step_push1 truthMismatchState13 (⟨0x26⟩ : Ethereum.UInt256) truth_decode_pc20

theorem truth_mismatch_xstep_pc22 :
    Ethereum.EVM.Xstep truthValidJumps truthMismatchState14 =
      .ok (truthMismatchState15, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthMismatchState14.executionEnv.code ⟨0⟩ by
    simp [truthValidJumps, truthMismatchState14, truthMismatchState13, truthMismatchState12,
      truthMismatchState11, truthMismatchState10, truthMismatchState9, truthMismatchState8,
      truthMismatchState7, truthMismatchState6, truthMismatchState5, truthMismatchState4,
      truthMismatchState3, truthMismatchState2, truthMismatchState1, truthMismatchInitialState,
      truthMismatchExecutionEnv, truthExecutionEnv]]
  rw [Ethereum.EVM.step_jumpi truthMismatchState14 (by
    simpa [truthMismatchState14, truthMismatchState13, truthMismatchState12,
      truthMismatchState11, truthMismatchState10, truthMismatchState9, truthMismatchState8,
      truthMismatchState7, truthMismatchState6, truthMismatchState5, truthMismatchState4,
      truthMismatchState3, truthMismatchState2, truthMismatchState1, truthMismatchInitialState,
      truthMismatchExecutionEnv] using truth_decode_pc22)]
  simp [truthMismatchState14, truthMismatchState13, truthState14, truthState13]
  have hgas : ¬ ((truthState12.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow -
      Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Ghigh) := by
    simp only [truthState12, truthState11, truthState10, truthState9, truthState8, truthState7,
      truthState6, truthState5, truthState4, truthState3]
    rw [truth_mstore_memoryExpansionCost]
    native_decide
  rw [if_neg hgas]
  have hzero : (((⟨0⟩ : Ethereum.UInt256) != (⟨0⟩ : Ethereum.UInt256)) = false) := by
    decide
  simp [truthMismatchState15, truthMismatchState14, truthMismatchState13, truthState15,
    truthState14, truthState13, hzero]

theorem truth_mismatch_xstep_pc23 :
    Ethereum.EVM.Xstep truthValidJumps truthMismatchState15 =
      .ok (truthMismatchState16, .none) := by
  simpa [truthValidJumps, truthMismatchState15, truthMismatchState16, truthState15,
    truthState16] using
    Ethereum.EVM.step_push0 truthMismatchState15 truth_decode_pc23

theorem truth_mismatch_xstep_pc24 :
    Ethereum.EVM.Xstep truthValidJumps truthMismatchState16 =
      .ok (truthMismatchState17, .none) := by
  simpa [truthValidJumps, truthMismatchState16, truthMismatchState17,
    truthMismatchCalldataWord] using
    Ethereum.EVM.step_calldataload truthMismatchState16 truth_decode_pc24

theorem truth_mismatch_xstep_pc25 :
    Ethereum.EVM.Xstep truthValidJumps truthMismatchState17 =
      .ok (truthMismatchState18, .none) := by
  simpa [truthValidJumps, truthMismatchState17, truthMismatchState18] using
    Ethereum.EVM.step_push1 truthMismatchState17 (⟨0xe0⟩ : Ethereum.UInt256) truth_decode_pc25

theorem truth_mismatch_xstep_pc27 :
    Ethereum.EVM.Xstep truthValidJumps truthMismatchState18 =
      .ok (truthMismatchState19, .none) := by
  simpa [truthValidJumps, truthMismatchState18, truthMismatchState19,
    truthMismatchSelectorWord] using
    Ethereum.EVM.step_shr truthMismatchState18 truth_decode_pc27

theorem truth_mismatch_xstep_pc28 :
    Ethereum.EVM.Xstep truthValidJumps truthMismatchState19 =
      .ok (truthMismatchState20, .none) := by
  simpa [truthValidJumps, truthMismatchState19, truthMismatchState20] using
    Ethereum.EVM.step_dup1 truthMismatchState19 truth_decode_pc28

theorem truth_mismatch_xstep_pc29 :
    Ethereum.EVM.Xstep truthValidJumps truthMismatchState20 =
      .ok (truthMismatchState21, .none) := by
  simpa [truthValidJumps, truthMismatchState20, truthMismatchState21,
    truthExpectedSelectorWord] using
    Ethereum.EVM.step_push4 truthMismatchState20 truthExpectedSelectorWord truth_decode_pc29

theorem truth_mismatch_xstep_pc34 :
    Ethereum.EVM.Xstep truthValidJumps truthMismatchState21 =
      .ok (truthMismatchState22, .none) := by
  simpa [truthValidJumps, truthMismatchState21, truthMismatchState22,
    truthMismatchSelectorEqWord] using
    Ethereum.EVM.step_eq truthMismatchState21 truth_decode_pc34

theorem truth_mismatch_xstep_pc35 :
    Ethereum.EVM.Xstep truthValidJumps truthMismatchState22 =
      .ok (truthMismatchState23, .none) := by
  simpa [truthValidJumps, truthMismatchState22, truthMismatchState23] using
    Ethereum.EVM.step_push1 truthMismatchState22 (⟨0x2a⟩ : Ethereum.UInt256) truth_decode_pc35

theorem truth_mismatch_selector_eq_word_eq_zero :
    truthMismatchSelectorEqWord = (⟨0⟩ : Ethereum.UInt256) := by
  unfold truthMismatchSelectorEqWord truthMismatchSelectorWord truthMismatchCalldataWord
  simp [truthMismatchState16, truthMismatchExecutionEnv, truthMismatchCallData,
    ByteArray.readBytes, truth_byteArray_zeroes_eq, truthExpectedSelectorWord]
  native_decide

theorem truth_mismatch_xstep_pc37 :
    Ethereum.EVM.Xstep truthValidJumps truthMismatchState23 =
      .ok (truthMismatchState24, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthMismatchState23.executionEnv.code ⟨0⟩ by
    simp [truthValidJumps, truthMismatchState23, truthMismatchState22, truthMismatchState21,
      truthMismatchState20, truthMismatchState19, truthMismatchState18, truthMismatchState17,
      truthMismatchState16, truthMismatchState15, truthMismatchState14, truthMismatchState13,
      truthMismatchState12, truthMismatchState11, truthMismatchState10, truthMismatchState9,
      truthMismatchState8, truthMismatchState7, truthMismatchState6, truthMismatchState5,
      truthMismatchState4, truthMismatchState3, truthMismatchState2, truthMismatchState1,
      truthMismatchInitialState, truthMismatchExecutionEnv, truthExecutionEnv]]
  rw [Ethereum.EVM.step_jumpi truthMismatchState23 (by
    simpa [truthMismatchState23, truthMismatchState22, truthMismatchState21,
      truthMismatchState20, truthMismatchState19, truthMismatchState18, truthMismatchState17,
      truthMismatchState16, truthMismatchState15, truthMismatchState14, truthMismatchState13,
      truthMismatchState12, truthMismatchState11, truthMismatchState10, truthMismatchState9,
      truthMismatchState8, truthMismatchState7, truthMismatchState6, truthMismatchState5,
      truthMismatchState4, truthMismatchState3, truthMismatchState2, truthMismatchState1,
      truthMismatchInitialState, truthMismatchExecutionEnv] using truth_decode_pc37)]
  simp [truthMismatchState23, truthMismatchState22, truth_mismatch_selector_eq_word_eq_zero]
  have hgas : ¬ truthMismatchState23.machineState.gasAvailable.toNat < GasConstants.Ghigh := by
    simp only [truthMismatchState23, truthMismatchState22, truthMismatchState21,
      truthMismatchState20, truthMismatchState19, truthMismatchState18, truthMismatchState17,
      truthMismatchState16, truthMismatchState15, truthMismatchState14, truthMismatchState13,
      truthMismatchState12, truthMismatchState11, truthMismatchState10, truthMismatchState9,
      truthMismatchState8, truthMismatchState7, truthMismatchState6, truthMismatchState5,
      truthMismatchState4, truthMismatchState3, truthState23, truthState22, truthState21,
      truthState20, truthState19, truthState18, truthState17, truthState16, truthState15,
      truthState14, truthState13, truthState12, truthState11, truthState10, truthState9,
      truthState8, truthState7, truthState6, truthState5, truthState4, truthState3]
    rw [truth_mstore_memoryExpansionCost]
    native_decide
  have hgas' :
      ¬ (truthMismatchState21.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow -
        Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Ghigh := by
    simpa [truthMismatchState23, truthMismatchState22] using hgas
  rw [if_neg hgas']
  have hzero : (((⟨0⟩ : Ethereum.UInt256) != (⟨0⟩ : Ethereum.UInt256)) = false) := by
    decide
  simp [truthMismatchState24, truthMismatchState23, truthMismatchState22,
    truth_mismatch_selector_eq_word_eq_zero, hzero]

theorem truth_mismatch_xstep_pc38 :
    Ethereum.EVM.Xstep truthValidJumps truthMismatchState24 =
      .ok (truthMismatchState25, .none) := by
  simpa [truthValidJumps, truthMismatchState24, truthMismatchState25] using
    Ethereum.EVM.step_jumpdest truthMismatchState24 truth_short_decode_pc38

theorem truth_mismatch_xstep_pc39 :
    Ethereum.EVM.Xstep truthValidJumps truthMismatchState25 =
      .ok (truthMismatchState26, .none) := by
  simpa [truthValidJumps, truthMismatchState25, truthMismatchState26] using
    Ethereum.EVM.step_push0 truthMismatchState25 truth_short_decode_pc39

theorem truth_mismatch_xstep_pc40 :
    Ethereum.EVM.Xstep truthValidJumps truthMismatchState26 =
      .ok (truthMismatchState27, .none) := by
  simpa [truthValidJumps, truthMismatchState26, truthMismatchState27] using
    Ethereum.EVM.step_push0 truthMismatchState26 truth_short_decode_pc40

theorem truth_mismatch_xstep_pc41 :
    Ethereum.EVM.Xstep truthValidJumps truthMismatchState27 =
      .ok (truthMismatchState28, .some (false, truthMismatchReturnData)) := by
  rw [show truthValidJumps =
      Ethereum.EVM.D_J truthMismatchState27.executionEnv.code ⟨0⟩ by
    have hcode : truthMismatchState27.executionEnv.code = truthRuntimeBytecode := by
      simp [truthMismatchState27, truthMismatchState26, truthMismatchState25,
        truthMismatchState24, truthMismatchState23, truthMismatchState22,
        truthMismatchState21, truthMismatchState20, truthMismatchState19,
        truthMismatchState18, truthMismatchState17, truthMismatchState16,
        truthMismatchState15, truthMismatchState14, truthMismatchState13,
        truthMismatchState12, truthMismatchState11, truthMismatchState10,
        truthMismatchState9, truthMismatchState8, truthMismatchState7,
        truthMismatchState6, truthMismatchState5, truthMismatchState4,
        truthMismatchState3, truthMismatchState2, truthMismatchState1,
        truthMismatchInitialState, truthMismatchExecutionEnv, truthInitialState,
        truthExecutionEnv]
    simp [truthValidJumps, hcode]]
  rw [Ethereum.EVM.step_revert truthMismatchState27 truth_short_decode_pc41]
  simp only [truthMismatchState27, truthMismatchState28, truthMismatchReturnData]
  change (if truthMismatchState27.machineState.gasAvailable.toNat <
      Ethereum.EVM.memoryExpansionCost truthMismatchState27 .REVERT then _ else _) = _
  have hstack : truthMismatchState27.machineState.stack =
      (⟨0⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) :: [truthMismatchSelectorWord] := by
    simp [truthMismatchState27, truthMismatchState26, truthMismatchState25, truthMismatchState24]
  have hmem : ¬ truthMismatchState27.machineState.gasAvailable.toNat <
      Ethereum.EVM.memoryExpansionCost truthMismatchState27 .REVERT := by
    rw [truth_revert_zero_memoryExpansionCost_top truthMismatchState27
      [truthMismatchSelectorWord] hstack]
    simp
  rw [if_neg hmem]
  have hoverflow :
      ¬ ((⟨0⟩ : Ethereum.UInt256) :: truthMismatchState26.machineState.stack).length - 2 + 0 >
        1024 := by
    simp [truthMismatchState26, truthMismatchState25, truthMismatchState24]
  rw [if_neg hoverflow]
  simp [truthMismatchState26, truthMismatchState25, truthMismatchState24,
    Ethereum.UInt256.toNat, Ethereum.MachineState.M]
  change Ethereum.UInt256.ofNat
      (Ethereum.UInt256.ofNat truthMismatchState24.machineState.activeWords.toNat).toNat =
    Ethereum.UInt256.ofNat truthMismatchState24.machineState.activeWords.toNat
  exact truth_uint256_ofNat_ofNat_toNat truthMismatchState24.machineState.activeWords.toNat

theorem truth_decode_pc42 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState24.machineState.pc =
      some (.JUMPDEST, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x2a⟩ : Ethereum.UInt256) =
    some (.JUMPDEST, none)
  native_decide

theorem truth_xstep_pc42 :
    Ethereum.EVM.Xstep truthValidJumps truthState24 =
      .ok (truthState25, .none) := by
  simpa [truthValidJumps, truthState25, truthState24] using
    Ethereum.EVM.step_jumpdest truthState24 truth_decode_pc42

theorem truth_decode_pc43 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState25.machineState.pc =
      some (.PUSH1, some ((⟨0x30⟩ : Ethereum.UInt256), 1)) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x2b⟩ : Ethereum.UInt256) =
    some (.PUSH1, some ((⟨0x30⟩ : Ethereum.UInt256), 1))
  native_decide

theorem truth_xstep_pc43 :
    Ethereum.EVM.Xstep truthValidJumps truthState25 =
      .ok (truthState26, .none) := by
  simpa [truthValidJumps, truthState26] using
    Ethereum.EVM.step_push1 truthState25 (⟨0x30⟩ : Ethereum.UInt256) truth_decode_pc43

theorem truth_decode_pc45 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState26.machineState.pc =
      some (.PUSH1, some ((⟨0x44⟩ : Ethereum.UInt256), 1)) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x2d⟩ : Ethereum.UInt256) =
    some (.PUSH1, some ((⟨0x44⟩ : Ethereum.UInt256), 1))
  native_decide

theorem truth_xstep_pc45 :
    Ethereum.EVM.Xstep truthValidJumps truthState26 =
      .ok (truthState27, .none) := by
  simpa [truthValidJumps, truthState27] using
    Ethereum.EVM.step_push1 truthState26 (⟨0x44⟩ : Ethereum.UInt256) truth_decode_pc45

theorem truth_valid_jumpdest_44 :
    (Ethereum.EVM.D_J truthRuntimeBytecode ⟨0⟩).contains (⟨0x44⟩ : Ethereum.UInt256) = true := by
  native_decide

theorem truth_decode_pc47 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState27.machineState.pc =
      some (.JUMP, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x2f⟩ : Ethereum.UInt256) =
    some (.JUMP, none)
  native_decide

theorem truth_xstep_pc47 :
    Ethereum.EVM.Xstep truthValidJumps truthState27 =
      .ok (truthState28, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthState27.executionEnv.code ⟨0⟩ by
    simp [truthValidJumps, truthState27, truthState26, truthState25, truthState24,
      truthState23, truthState22, truthState21, truthState20, truthState19, truthState18,
      truthState17, truthState16, truthState15, truthState14, truthState13, truthState12,
      truthState11, truthState10, truthState9, truthState8, truthState7, truthState6,
      truthState5, truthState4, truthState3, truthState2, truthState1, truthInitialState,
      truthExecutionEnv]]
  rw [Ethereum.EVM.step_jump truthState27 truth_decode_pc47]
  simp [truthState27, truthState26]
  have hgas : ¬ truthState27.machineState.gasAvailable.toNat < GasConstants.Gmid := by
    simp only [truthState27, truthState26, truthState25, truthState24, truthState23,
      truthState22, truthState21, truthState20, truthState19, truthState18, truthState17,
      truthState16, truthState15, truthState14, truthState13, truthState12, truthState11,
      truthState10, truthState9, truthState8, truthState7, truthState6, truthState5,
      truthState4, truthState3]
    rw [truth_mstore_memoryExpansionCost]
    native_decide
  have hgas' :
      ¬ (truthState25.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow -
        Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Gmid := by
    simpa [truthState27, truthState26] using hgas
  rw [if_neg hgas']
  have hcontains :
      (Ethereum.EVM.D_J truthState25.executionEnv.code ⟨0⟩).contains
        (⟨0x44⟩ : Ethereum.UInt256) = true := by
    have hcode : truthState25.executionEnv.code = truthRuntimeBytecode := by
      simp [truthState25, truthState24, truthState23, truthState22, truthState21, truthState20,
        truthState19, truthState18, truthState17, truthState16, truthState15, truthState14,
        truthState13, truthState12, truthState11, truthState10, truthState9, truthState8,
        truthState7, truthState6, truthState5, truthState4, truthState3, truthState2,
        truthState1, truthInitialState, truthExecutionEnv]
    rw [hcode]
    exact truth_valid_jumpdest_44
  rw [hcontains]
  simp [truthState28, truthState27, truthState26, truthState25, truthState24]

theorem truth_decode_pc68 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState28.machineState.pc =
      some (.JUMPDEST, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x44⟩ : Ethereum.UInt256) =
    some (.JUMPDEST, none)
  native_decide

theorem truth_xstep_pc68 :
    Ethereum.EVM.Xstep truthValidJumps truthState28 =
      .ok (truthState29, .none) := by
  simpa [truthValidJumps, truthState29, truthState28] using
    Ethereum.EVM.step_jumpdest truthState28 truth_decode_pc68

theorem truth_decode_pc69 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState29.machineState.pc =
      some (.PUSH0, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x45⟩ : Ethereum.UInt256) =
    some (.PUSH0, none)
  native_decide

theorem truth_xstep_pc69 :
    Ethereum.EVM.Xstep truthValidJumps truthState29 =
      .ok (truthState30, .none) := by
  simpa [truthValidJumps, truthState30] using
    Ethereum.EVM.step_push0 truthState29 truth_decode_pc69

theorem truth_decode_pc70 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState30.machineState.pc =
      some (.PUSH1, some ((⟨1⟩ : Ethereum.UInt256), 1)) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x46⟩ : Ethereum.UInt256) =
    some (.PUSH1, some ((⟨1⟩ : Ethereum.UInt256), 1))
  native_decide

theorem truth_xstep_pc70 :
    Ethereum.EVM.Xstep truthValidJumps truthState30 =
      .ok (truthState31, .none) := by
  simpa [truthValidJumps, truthState31] using
    Ethereum.EVM.step_push1 truthState30 (⟨1⟩ : Ethereum.UInt256) truth_decode_pc70

theorem truth_decode_pc72 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState31.machineState.pc =
      some (.SWAP1, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x48⟩ : Ethereum.UInt256) =
    some (.SWAP1, none)
  native_decide

theorem truth_xstep_pc72 :
    Ethereum.EVM.Xstep truthValidJumps truthState31 =
      .ok (truthState32, .none) := by
  simpa [truthValidJumps, truthState32] using
    Ethereum.EVM.step_swap1 truthState31 truth_decode_pc72

theorem truth_decode_pc73 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState32.machineState.pc =
      some (.POP, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x49⟩ : Ethereum.UInt256) =
    some (.POP, none)
  native_decide

theorem truth_xstep_pc73 :
    Ethereum.EVM.Xstep truthValidJumps truthState32 =
      .ok (truthState33, .none) := by
  simpa [truthValidJumps, truthState33] using
    Ethereum.EVM.step_pop truthState32 truth_decode_pc73

theorem truth_decode_pc74 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState33.machineState.pc =
      some (.SWAP1, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x4a⟩ : Ethereum.UInt256) =
    some (.SWAP1, none)
  native_decide

theorem truth_xstep_pc74 :
    Ethereum.EVM.Xstep truthValidJumps truthState33 =
      .ok (truthState34, .none) := by
  simpa [truthValidJumps, truthState34] using
    Ethereum.EVM.step_swap1 truthState33 truth_decode_pc74

theorem truth_valid_jumpdest_30 :
    (Ethereum.EVM.D_J truthRuntimeBytecode ⟨0⟩).contains (⟨0x30⟩ : Ethereum.UInt256) = true := by
  native_decide

theorem truth_decode_pc75 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState34.machineState.pc =
      some (.JUMP, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x4b⟩ : Ethereum.UInt256) =
    some (.JUMP, none)
  native_decide

theorem truth_xstep_pc75 :
    Ethereum.EVM.Xstep truthValidJumps truthState34 =
      .ok (truthState35, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthState34.executionEnv.code ⟨0⟩ by
    simp [truthValidJumps, truthState34, truthState33, truthState32, truthState31, truthState30,
      truthState29, truthState28, truthState27, truthState26, truthState25, truthState24,
      truthState23, truthState22, truthState21, truthState20, truthState19, truthState18,
      truthState17, truthState16, truthState15, truthState14, truthState13, truthState12,
      truthState11, truthState10, truthState9, truthState8, truthState7, truthState6,
      truthState5, truthState4, truthState3, truthState2, truthState1, truthInitialState,
      truthExecutionEnv]]
  rw [Ethereum.EVM.step_jump truthState34 truth_decode_pc75]
  simp [truthState34, truthState33]
  have hgas : ¬ truthState34.machineState.gasAvailable.toNat < GasConstants.Gmid := by
    simp only [truthState34, truthState33, truthState32, truthState31, truthState30,
      truthState29, truthState28, truthState27, truthState26, truthState25, truthState24,
      truthState23, truthState22, truthState21, truthState20, truthState19, truthState18,
      truthState17, truthState16, truthState15, truthState14, truthState13, truthState12,
      truthState11, truthState10, truthState9, truthState8, truthState7, truthState6,
      truthState5, truthState4, truthState3]
    rw [truth_mstore_memoryExpansionCost]
    native_decide
  have hgas' :
      ¬ (truthState32.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gbase -
        Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Gmid := by
    simpa [truthState34, truthState33] using hgas
  rw [if_neg hgas']
  have hcontains :
      (Ethereum.EVM.D_J truthState32.executionEnv.code ⟨0⟩).contains
        (⟨0x30⟩ : Ethereum.UInt256) = true := by
    have hcode : truthState32.executionEnv.code = truthRuntimeBytecode := by
      simp [truthState32, truthState31, truthState30, truthState29, truthState28, truthState27,
        truthState26, truthState25, truthState24, truthState23, truthState22, truthState21,
        truthState20, truthState19, truthState18, truthState17, truthState16, truthState15,
        truthState14, truthState13, truthState12, truthState11, truthState10, truthState9,
        truthState8, truthState7, truthState6, truthState5, truthState4, truthState3,
        truthState2, truthState1, truthInitialState, truthExecutionEnv]
    rw [hcode]
    exact truth_valid_jumpdest_30
  rw [hcontains]
  simp [truthState35, truthState34, truthState33, truthState32]

theorem truth_decode_pc48 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState35.machineState.pc =
      some (.JUMPDEST, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x30⟩ : Ethereum.UInt256) =
    some (.JUMPDEST, none)
  native_decide

theorem truth_xstep_pc48 :
    Ethereum.EVM.Xstep truthValidJumps truthState35 =
      .ok (truthState36, .none) := by
  simpa [truthValidJumps, truthState36, truthState35] using
    Ethereum.EVM.step_jumpdest truthState35 truth_decode_pc48

theorem truth_decode_pc49 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState36.machineState.pc =
      some (.PUSH1, some ((⟨0x40⟩ : Ethereum.UInt256), 1)) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x31⟩ : Ethereum.UInt256) =
    some (.PUSH1, some ((⟨0x40⟩ : Ethereum.UInt256), 1))
  native_decide

theorem truth_xstep_pc49 :
    Ethereum.EVM.Xstep truthValidJumps truthState36 =
      .ok (truthState37, .none) := by
  simpa [truthValidJumps, truthState37] using
    Ethereum.EVM.step_push1 truthState36 (⟨0x40⟩ : Ethereum.UInt256) truth_decode_pc49

theorem truth_decode_pc51 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState37.machineState.pc =
      some (.MLOAD, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x33⟩ : Ethereum.UInt256) =
    some (.MLOAD, none)
  native_decide

theorem truth_xstep_pc51 :
    Ethereum.EVM.Xstep truthValidJumps truthState37 =
      .ok (truthState38, .none) := by
  simpa [truthValidJumps, truthState38, truthFreeMemPtr] using
    Ethereum.EVM.step_mload truthState37 truth_decode_pc51

theorem truth_decode_pc52 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState38.machineState.pc =
      some (.PUSH1, some ((⟨0x3b⟩ : Ethereum.UInt256), 1)) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x34⟩ : Ethereum.UInt256) =
    some (.PUSH1, some ((⟨0x3b⟩ : Ethereum.UInt256), 1))
  native_decide

theorem truth_xstep_pc52 :
    Ethereum.EVM.Xstep truthValidJumps truthState38 =
      .ok (truthState39, .none) := by
  simpa [truthValidJumps, truthState39] using
    Ethereum.EVM.step_push1 truthState38 (⟨0x3b⟩ : Ethereum.UInt256) truth_decode_pc52

theorem truth_decode_pc54 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState39.machineState.pc =
      some (.SWAP2, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x36⟩ : Ethereum.UInt256) =
    some (.SWAP2, none)
  native_decide

theorem truth_xstep_pc54 :
    Ethereum.EVM.Xstep truthValidJumps truthState39 =
      .ok (truthState40, .none) := by
  simpa [truthValidJumps, truthState40] using
    Ethereum.EVM.step_swap2 truthState39 truth_decode_pc54

theorem truth_decode_pc55 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState40.machineState.pc =
      some (.SWAP1, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x37⟩ : Ethereum.UInt256) =
    some (.SWAP1, none)
  native_decide

theorem truth_xstep_pc55 :
    Ethereum.EVM.Xstep truthValidJumps truthState40 =
      .ok (truthState41, .none) := by
  simpa [truthValidJumps, truthState41] using
    Ethereum.EVM.step_swap1 truthState40 truth_decode_pc55

theorem truth_decode_pc56 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState41.machineState.pc =
      some (.PUSH1, some ((⟨0x64⟩ : Ethereum.UInt256), 1)) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x38⟩ : Ethereum.UInt256) =
    some (.PUSH1, some ((⟨0x64⟩ : Ethereum.UInt256), 1))
  native_decide

theorem truth_xstep_pc56 :
    Ethereum.EVM.Xstep truthValidJumps truthState41 =
      .ok (truthState42, .none) := by
  simpa [truthValidJumps, truthState42] using
    Ethereum.EVM.step_push1 truthState41 (⟨0x64⟩ : Ethereum.UInt256) truth_decode_pc56

theorem truth_valid_jumpdest_64 :
    (Ethereum.EVM.D_J truthRuntimeBytecode ⟨0⟩).contains (⟨0x64⟩ : Ethereum.UInt256) = true := by
  native_decide

theorem truth_decode_pc58 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState42.machineState.pc =
      some (.JUMP, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x3a⟩ : Ethereum.UInt256) =
    some (.JUMP, none)
  native_decide

theorem truth_xstep_pc58 :
    Ethereum.EVM.Xstep truthValidJumps truthState42 =
      .ok (truthState43, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthState42.executionEnv.code ⟨0⟩ by
    simp [truthValidJumps, truthState42, truthState41, truthState40, truthState39, truthState38,
      truthState37, truthState36, truthState35, truthState34, truthState33, truthState32,
      truthState31, truthState30, truthState29, truthState28, truthState27, truthState26,
      truthState25, truthState24, truthState23, truthState22, truthState21, truthState20,
      truthState19, truthState18, truthState17, truthState16, truthState15, truthState14,
      truthState13, truthState12, truthState11, truthState10, truthState9, truthState8,
      truthState7, truthState6, truthState5, truthState4, truthState3, truthState2,
      truthState1, truthInitialState, truthExecutionEnv]]
  rw [Ethereum.EVM.step_jump truthState42 truth_decode_pc58]
  simp [truthState42, truthState41]
  have hgas : ¬ truthState42.machineState.gasAvailable.toNat < GasConstants.Gmid :=
    truth_pc58_has_gas
  have hgas' :
      ¬ (truthState40.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow -
          Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat <
        GasConstants.Gmid := by
    simpa [truthState42, truthState41] using hgas
  rw [if_neg hgas']
  have hcontains :
      (Ethereum.EVM.D_J truthState40.executionEnv.code ⟨0⟩).contains
        (⟨0x64⟩ : Ethereum.UInt256) = true := by
    have hcode : truthState40.executionEnv.code = truthRuntimeBytecode := by
      simp [truthState40, truthState39, truthState38, truthState37, truthState36,
        truthState35, truthState34, truthState33, truthState32, truthState31, truthState30,
        truthState29, truthState28, truthState27, truthState26, truthState25, truthState24,
        truthState23, truthState22, truthState21, truthState20, truthState19, truthState18,
        truthState17, truthState16, truthState15, truthState14, truthState13, truthState12,
        truthState11, truthState10, truthState9, truthState8, truthState7, truthState6,
        truthState5, truthState4, truthState3, truthState2, truthState1, truthInitialState,
        truthExecutionEnv]
    rw [hcode]
    exact truth_valid_jumpdest_64
  rw [hcontains]
  simp [truthState43, truthState42, truthState41]

theorem truth_decode_pc100 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState43.machineState.pc =
      some (.JUMPDEST, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x64⟩ : Ethereum.UInt256) =
    some (.JUMPDEST, none)
  native_decide

theorem truth_xstep_pc100 :
    Ethereum.EVM.Xstep truthValidJumps truthState43 =
      .ok (truthState44, .none) := by
  simpa [truthValidJumps, truthState44, truthState43] using
    Ethereum.EVM.step_jumpdest truthState43 truth_decode_pc100

theorem truth_decode_pc101 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState44.machineState.pc =
      some (.PUSH0, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x65⟩ : Ethereum.UInt256) =
    some (.PUSH0, none)
  native_decide

theorem truth_xstep_pc101 :
    Ethereum.EVM.Xstep truthValidJumps truthState44 =
      .ok (truthState45, .none) := by
  simpa [truthValidJumps, truthState45] using
    Ethereum.EVM.step_push0 truthState44 truth_decode_pc101

theorem truth_decode_pc102 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState45.machineState.pc =
      some (.PUSH1, some ((⟨0x20⟩ : Ethereum.UInt256), 1)) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x66⟩ : Ethereum.UInt256) =
    some (.PUSH1, some ((⟨0x20⟩ : Ethereum.UInt256), 1))
  native_decide

theorem truth_xstep_pc102 :
    Ethereum.EVM.Xstep truthValidJumps truthState45 =
      .ok (truthState46, .none) := by
  simpa [truthValidJumps, truthState46] using
    Ethereum.EVM.step_push1 truthState45 (⟨0x20⟩ : Ethereum.UInt256) truth_decode_pc102

theorem truth_decode_pc104 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState46.machineState.pc =
      some (.DUP3, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x68⟩ : Ethereum.UInt256) =
    some (.DUP3, none)
  native_decide

theorem truth_xstep_pc104 :
    Ethereum.EVM.Xstep truthValidJumps truthState46 =
      .ok (truthState47, .none) := by
  simpa [truthValidJumps, truthState47] using
    Ethereum.EVM.step_dup3 truthState46 truth_decode_pc104

theorem truth_decode_pc105 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState47.machineState.pc =
      some (.ADD, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x69⟩ : Ethereum.UInt256) =
    some (.ADD, none)
  native_decide

theorem truth_xstep_pc105 :
    Ethereum.EVM.Xstep truthValidJumps truthState47 =
      .ok (truthState48, .none) := by
  simpa [truthValidJumps, truthState48, truthAbiEnd] using
    Ethereum.EVM.step_add truthState47 truth_decode_pc105

theorem truth_decode_pc106 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState48.machineState.pc =
      some (.SWAP1, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x6a⟩ : Ethereum.UInt256) =
    some (.SWAP1, none)
  native_decide

theorem truth_xstep_pc106 :
    Ethereum.EVM.Xstep truthValidJumps truthState48 =
      .ok (truthState49, .none) := by
  simpa [truthValidJumps, truthState49] using
    Ethereum.EVM.step_swap1 truthState48 truth_decode_pc106

theorem truth_decode_pc107 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState49.machineState.pc =
      some (.POP, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x6b⟩ : Ethereum.UInt256) =
    some (.POP, none)
  native_decide

theorem truth_xstep_pc107 :
    Ethereum.EVM.Xstep truthValidJumps truthState49 =
      .ok (truthState50, .none) := by
  simpa [truthValidJumps, truthState50] using
    Ethereum.EVM.step_pop truthState49 truth_decode_pc107

theorem truth_decode_pc108 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState50.machineState.pc =
      some (.PUSH1, some ((⟨0x75⟩ : Ethereum.UInt256), 1)) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x6c⟩ : Ethereum.UInt256) =
    some (.PUSH1, some ((⟨0x75⟩ : Ethereum.UInt256), 1))
  native_decide

theorem truth_xstep_pc108 :
    Ethereum.EVM.Xstep truthValidJumps truthState50 =
      .ok (truthState51, .none) := by
  simpa [truthValidJumps, truthState51] using
    Ethereum.EVM.step_push1 truthState50 (⟨0x75⟩ : Ethereum.UInt256) truth_decode_pc108

theorem truth_decode_pc110 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState51.machineState.pc =
      some (.PUSH0, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x6e⟩ : Ethereum.UInt256) =
    some (.PUSH0, none)
  native_decide

theorem truth_xstep_pc110 :
    Ethereum.EVM.Xstep truthValidJumps truthState51 =
      .ok (truthState52, .none) := by
  simpa [truthValidJumps, truthState52] using
    Ethereum.EVM.step_push0 truthState51 truth_decode_pc110

theorem truth_decode_pc111 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState52.machineState.pc =
      some (.DUP4, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x6f⟩ : Ethereum.UInt256) =
    some (.DUP4, none)
  native_decide

theorem truth_xstep_pc111 :
    Ethereum.EVM.Xstep truthValidJumps truthState52 =
      .ok (truthState53, .none) := by
  simpa [truthValidJumps, truthState53] using
    Ethereum.EVM.step_dup4 truthState52 truth_decode_pc111

theorem truth_decode_pc112 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState53.machineState.pc =
      some (.ADD, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x70⟩ : Ethereum.UInt256) =
    some (.ADD, none)
  native_decide

theorem truth_xstep_pc112 :
    Ethereum.EVM.Xstep truthValidJumps truthState53 =
      .ok (truthState54, .none) := by
  simpa [truthValidJumps, truthState54, truthState53, truth_uint256_add_zero] using
    Ethereum.EVM.step_add truthState53 truth_decode_pc112

theorem truth_decode_pc113 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState54.machineState.pc =
      some (.DUP5, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x71⟩ : Ethereum.UInt256) =
    some (.DUP5, none)
  native_decide

theorem truth_xstep_pc113 :
    Ethereum.EVM.Xstep truthValidJumps truthState54 =
      .ok (truthState55, .none) := by
  simpa [truthValidJumps, truthState55] using
    Ethereum.EVM.step_dup5 truthState54 truth_decode_pc113

theorem truth_decode_pc114 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState55.machineState.pc =
      some (.PUSH1, some ((⟨0x57⟩ : Ethereum.UInt256), 1)) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x72⟩ : Ethereum.UInt256) =
    some (.PUSH1, some ((⟨0x57⟩ : Ethereum.UInt256), 1))
  native_decide

theorem truth_xstep_pc114 :
    Ethereum.EVM.Xstep truthValidJumps truthState55 =
      .ok (truthState56, .none) := by
  simpa [truthValidJumps, truthState56] using
    Ethereum.EVM.step_push1 truthState55 (⟨0x57⟩ : Ethereum.UInt256) truth_decode_pc114

theorem truth_valid_jumpdest_57 :
    (Ethereum.EVM.D_J truthRuntimeBytecode ⟨0⟩).contains (⟨0x57⟩ : Ethereum.UInt256) = true := by
  native_decide

theorem truth_decode_pc116 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState56.machineState.pc =
      some (.JUMP, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x74⟩ : Ethereum.UInt256) =
    some (.JUMP, none)
  native_decide

theorem truth_xstep_pc116 :
    Ethereum.EVM.Xstep truthValidJumps truthState56 =
      .ok (truthState57, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthState56.executionEnv.code ⟨0⟩ by
    simp [truthValidJumps, truthState56, truthState55, truthState54, truthState53, truthState52,
      truthState51, truthState50, truthState49, truthState48, truthState47, truthState46,
      truthState45, truthState44, truthState43, truthState42, truthState41, truthState40,
      truthState39, truthState38, truthState37, truthState36, truthState35, truthState34,
      truthState33, truthState32, truthState31, truthState30, truthState29, truthState28,
      truthState27, truthState26, truthState25, truthState24, truthState23, truthState22,
      truthState21, truthState20, truthState19, truthState18, truthState17, truthState16,
      truthState15, truthState14, truthState13, truthState12, truthState11, truthState10,
      truthState9, truthState8, truthState7, truthState6, truthState5, truthState4,
      truthState3, truthState2, truthState1, truthInitialState, truthExecutionEnv]]
  rw [Ethereum.EVM.step_jump truthState56 truth_decode_pc116]
  simp [truthState56, truthState55]
  have hgas : ¬ truthState56.machineState.gasAvailable.toNat < GasConstants.Gmid :=
    truth_pc116_has_gas
  have hgas' :
      ¬ (truthState54.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow -
          Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat <
        GasConstants.Gmid := by
    simpa [truthState56, truthState55] using hgas
  rw [if_neg hgas']
  have hcontains :
      (Ethereum.EVM.D_J truthState54.executionEnv.code ⟨0⟩).contains
        (⟨0x57⟩ : Ethereum.UInt256) = true := by
    have hcode : truthState54.executionEnv.code = truthRuntimeBytecode := by
      simp [truthState54, truthState53, truthState52, truthState51, truthState50,
        truthState49, truthState48, truthState47, truthState46, truthState45, truthState44,
        truthState43, truthState42, truthState41, truthState40, truthState39, truthState38,
        truthState37, truthState36, truthState35, truthState34, truthState33, truthState32,
        truthState31, truthState30, truthState29, truthState28, truthState27, truthState26,
        truthState25, truthState24, truthState23, truthState22, truthState21, truthState20,
        truthState19, truthState18, truthState17, truthState16, truthState15, truthState14,
        truthState13, truthState12, truthState11, truthState10, truthState9, truthState8,
        truthState7, truthState6, truthState5, truthState4, truthState3, truthState2,
        truthState1, truthInitialState, truthExecutionEnv]
    rw [hcode]
    exact truth_valid_jumpdest_57
  rw [hcontains]
  simp [truthState57, truthState56, truthState55]

theorem truth_decode_pc87 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState57.machineState.pc =
      some (.JUMPDEST, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x57⟩ : Ethereum.UInt256) =
    some (.JUMPDEST, none)
  native_decide

theorem truth_xstep_pc87 :
    Ethereum.EVM.Xstep truthValidJumps truthState57 =
      .ok (truthState58, .none) := by
  simpa [truthValidJumps, truthState58, truthState57] using
    Ethereum.EVM.step_jumpdest truthState57 truth_decode_pc87

theorem truth_decode_pc88 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState58.machineState.pc =
      some (.PUSH1, some ((⟨0x5e⟩ : Ethereum.UInt256), 1)) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x58⟩ : Ethereum.UInt256) =
    some (.PUSH1, some ((⟨0x5e⟩ : Ethereum.UInt256), 1))
  native_decide

theorem truth_xstep_pc88 :
    Ethereum.EVM.Xstep truthValidJumps truthState58 =
      .ok (truthState59, .none) := by
  simpa [truthValidJumps, truthState59] using
    Ethereum.EVM.step_push1 truthState58 (⟨0x5e⟩ : Ethereum.UInt256) truth_decode_pc88

theorem truth_decode_pc90 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState59.machineState.pc =
      some (.DUP2, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x5a⟩ : Ethereum.UInt256) =
    some (.DUP2, none)
  native_decide

theorem truth_xstep_pc90 :
    Ethereum.EVM.Xstep truthValidJumps truthState59 =
      .ok (truthState60, .none) := by
  simpa [truthValidJumps, truthState60] using
    Ethereum.EVM.step_dup2 truthState59 truth_decode_pc90

theorem truth_decode_pc91 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState60.machineState.pc =
      some (.PUSH1, some ((⟨0x4c⟩ : Ethereum.UInt256), 1)) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x5b⟩ : Ethereum.UInt256) =
    some (.PUSH1, some ((⟨0x4c⟩ : Ethereum.UInt256), 1))
  native_decide

theorem truth_xstep_pc91 :
    Ethereum.EVM.Xstep truthValidJumps truthState60 =
      .ok (truthState61, .none) := by
  simpa [truthValidJumps, truthState61] using
    Ethereum.EVM.step_push1 truthState60 (⟨0x4c⟩ : Ethereum.UInt256) truth_decode_pc91

theorem truth_valid_jumpdest_4c :
    (Ethereum.EVM.D_J truthRuntimeBytecode ⟨0⟩).contains (⟨0x4c⟩ : Ethereum.UInt256) = true := by
  native_decide

theorem truth_decode_pc93 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState61.machineState.pc =
      some (.JUMP, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x5d⟩ : Ethereum.UInt256) =
    some (.JUMP, none)
  native_decide

theorem truth_xstep_pc93 :
    Ethereum.EVM.Xstep truthValidJumps truthState61 =
      .ok (truthState62, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthState61.executionEnv.code ⟨0⟩ by
    simp [truthValidJumps, truthState61, truthState60, truthState59, truthState58, truthState57,
      truthState56, truthState55, truthState54, truthState53, truthState52, truthState51,
      truthState50, truthState49, truthState48, truthState47, truthState46, truthState45,
      truthState44, truthState43, truthState42, truthState41, truthState40, truthState39,
      truthState38, truthState37, truthState36, truthState35, truthState34, truthState33,
      truthState32, truthState31, truthState30, truthState29, truthState28, truthState27,
      truthState26, truthState25, truthState24, truthState23, truthState22, truthState21,
      truthState20, truthState19, truthState18, truthState17, truthState16, truthState15,
      truthState14, truthState13, truthState12, truthState11, truthState10, truthState9,
      truthState8, truthState7, truthState6, truthState5, truthState4, truthState3,
      truthState2, truthState1, truthInitialState, truthExecutionEnv]]
  rw [Ethereum.EVM.step_jump truthState61 truth_decode_pc93]
  simp [truthState61, truthState60]
  have hgas : ¬ truthState61.machineState.gasAvailable.toNat < GasConstants.Gmid :=
    truth_pc93_has_gas
  have hgas' :
      ¬ (truthState59.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow -
          Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Gmid := by
    simpa [truthState61, truthState60] using hgas
  rw [if_neg hgas']
  have hcontains :
      (Ethereum.EVM.D_J truthState59.executionEnv.code ⟨0⟩).contains
        (⟨0x4c⟩ : Ethereum.UInt256) = true := by
    have hcode : truthState59.executionEnv.code = truthRuntimeBytecode := by
      simp [truthState59, truthState58, truthState57, truthState56, truthState55,
        truthState54, truthState53, truthState52, truthState51, truthState50, truthState49,
        truthState48, truthState47, truthState46, truthState45, truthState44, truthState43,
        truthState42, truthState41, truthState40, truthState39, truthState38, truthState37,
        truthState36, truthState35, truthState34, truthState33, truthState32, truthState31,
        truthState30, truthState29, truthState28, truthState27, truthState26, truthState25,
        truthState24, truthState23, truthState22, truthState21, truthState20, truthState19,
        truthState18, truthState17, truthState16, truthState15, truthState14, truthState13,
        truthState12, truthState11, truthState10, truthState9, truthState8, truthState7,
        truthState6, truthState5, truthState4, truthState3, truthState2, truthState1,
        truthInitialState, truthExecutionEnv]
    rw [hcode]
    exact truth_valid_jumpdest_4c
  rw [hcontains]
  simp [truthState62, truthState61, truthState60]

theorem truth_decode_pc76 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState62.machineState.pc =
      some (.JUMPDEST, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x4c⟩ : Ethereum.UInt256) =
    some (.JUMPDEST, none)
  native_decide

theorem truth_xstep_pc76 :
    Ethereum.EVM.Xstep truthValidJumps truthState62 =
      .ok (truthState63, .none) := by
  simpa [truthValidJumps, truthState63, truthState62] using
    Ethereum.EVM.step_jumpdest truthState62 truth_decode_pc76

theorem truth_decode_pc77 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState63.machineState.pc =
      some (.PUSH0, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x4d⟩ : Ethereum.UInt256) =
    some (.PUSH0, none)
  native_decide

theorem truth_xstep_pc77 :
    Ethereum.EVM.Xstep truthValidJumps truthState63 =
      .ok (truthState64, .none) := by
  simpa [truthValidJumps, truthState64] using
    Ethereum.EVM.step_push0 truthState63 truth_decode_pc77

theorem truth_decode_pc78 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState64.machineState.pc =
      some (.DUP2, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x4e⟩ : Ethereum.UInt256) =
    some (.DUP2, none)
  native_decide

theorem truth_xstep_pc78 :
    Ethereum.EVM.Xstep truthValidJumps truthState64 =
      .ok (truthState65, .none) := by
  simpa [truthValidJumps, truthState65] using
    Ethereum.EVM.step_dup2 truthState64 truth_decode_pc78

theorem truth_decode_pc79 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState65.machineState.pc =
      some (.ISZERO, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x4f⟩ : Ethereum.UInt256) =
    some (.ISZERO, none)
  native_decide

theorem truth_xstep_pc79 :
    Ethereum.EVM.Xstep truthValidJumps truthState65 =
      .ok (truthState66, .none) := by
  simpa [truthValidJumps, truthState66] using
    Ethereum.EVM.step_iszero truthState65 truth_decode_pc79

theorem truth_decode_pc80 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState66.machineState.pc =
      some (.ISZERO, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x50⟩ : Ethereum.UInt256) =
    some (.ISZERO, none)
  native_decide

theorem truth_xstep_pc80 :
    Ethereum.EVM.Xstep truthValidJumps truthState66 =
      .ok (truthState67, .none) := by
  simpa [truthValidJumps, truthState67] using
    Ethereum.EVM.step_iszero truthState66 truth_decode_pc80

theorem truth_decode_pc81 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState67.machineState.pc =
      some (.SWAP1, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x51⟩ : Ethereum.UInt256) =
    some (.SWAP1, none)
  native_decide

theorem truth_xstep_pc81 :
    Ethereum.EVM.Xstep truthValidJumps truthState67 =
      .ok (truthState68, .none) := by
  simpa [truthValidJumps, truthState68] using
    Ethereum.EVM.step_swap1 truthState67 truth_decode_pc81

theorem truth_decode_pc82 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState68.machineState.pc =
      some (.POP, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x52⟩ : Ethereum.UInt256) =
    some (.POP, none)
  native_decide

theorem truth_xstep_pc82 :
    Ethereum.EVM.Xstep truthValidJumps truthState68 =
      .ok (truthState69, .none) := by
  simpa [truthValidJumps, truthState69] using
    Ethereum.EVM.step_pop truthState68 truth_decode_pc82

theorem truth_decode_pc83 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState69.machineState.pc =
      some (.SWAP2, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x53⟩ : Ethereum.UInt256) =
    some (.SWAP2, none)
  native_decide

theorem truth_xstep_pc83 :
    Ethereum.EVM.Xstep truthValidJumps truthState69 =
      .ok (truthState70, .none) := by
  simpa [truthValidJumps, truthState70] using
    Ethereum.EVM.step_swap2 truthState69 truth_decode_pc83

theorem truth_decode_pc84 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState70.machineState.pc =
      some (.SWAP1, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x54⟩ : Ethereum.UInt256) =
    some (.SWAP1, none)
  native_decide

theorem truth_xstep_pc84 :
    Ethereum.EVM.Xstep truthValidJumps truthState70 =
      .ok (truthState71, .none) := by
  simpa [truthValidJumps, truthState71] using
    Ethereum.EVM.step_swap1 truthState70 truth_decode_pc84

theorem truth_decode_pc85 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState71.machineState.pc =
      some (.POP, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x55⟩ : Ethereum.UInt256) =
    some (.POP, none)
  native_decide

theorem truth_xstep_pc85 :
    Ethereum.EVM.Xstep truthValidJumps truthState71 =
      .ok (truthState72, .none) := by
  simpa [truthValidJumps, truthState72] using
    Ethereum.EVM.step_pop truthState71 truth_decode_pc85

theorem truth_valid_jumpdest_5e :
    (Ethereum.EVM.D_J truthRuntimeBytecode ⟨0⟩).contains (⟨0x5e⟩ : Ethereum.UInt256) = true := by
  native_decide

theorem truth_decode_pc86 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState72.machineState.pc =
      some (.JUMP, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x56⟩ : Ethereum.UInt256) =
    some (.JUMP, none)
  native_decide

theorem truth_xstep_pc86 :
    Ethereum.EVM.Xstep truthValidJumps truthState72 =
      .ok (truthState73, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthState72.executionEnv.code ⟨0⟩ by
    simp [truthValidJumps, truthState72, truthState71, truthState70, truthState69, truthState68,
      truthState67, truthState66, truthState65, truthState64, truthState63, truthState62,
      truthState61, truthState60, truthState59, truthState58, truthState57, truthState56,
      truthState55, truthState54, truthState53, truthState52, truthState51, truthState50,
      truthState49, truthState48, truthState47, truthState46, truthState45, truthState44,
      truthState43, truthState42, truthState41, truthState40, truthState39, truthState38,
      truthState37, truthState36, truthState35, truthState34, truthState33, truthState32,
      truthState31, truthState30, truthState29, truthState28, truthState27, truthState26,
      truthState25, truthState24, truthState23, truthState22, truthState21, truthState20,
      truthState19, truthState18, truthState17, truthState16, truthState15, truthState14,
      truthState13, truthState12, truthState11, truthState10, truthState9, truthState8,
      truthState7, truthState6, truthState5, truthState4, truthState3, truthState2,
      truthState1, truthInitialState, truthExecutionEnv]]
  rw [Ethereum.EVM.step_jump truthState72 truth_decode_pc86]
  simp [truthState72, truthState71]
  have hgas : ¬ truthState72.machineState.gasAvailable.toNat < GasConstants.Gmid :=
    truth_pc86_has_gas
  have hgas' :
      ¬ (truthState70.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow -
          Ethereum.UInt256.ofNat GasConstants.Gbase).toNat < GasConstants.Gmid := by
    simpa [truthState72, truthState71] using hgas
  rw [if_neg hgas']
  have hcontains :
      (Ethereum.EVM.D_J truthState70.executionEnv.code ⟨0⟩).contains
        (⟨0x5e⟩ : Ethereum.UInt256) = true := by
    have hcode : truthState70.executionEnv.code = truthRuntimeBytecode := by
      simp [truthState70, truthState69, truthState68, truthState67, truthState66,
        truthState65, truthState64, truthState63, truthState62, truthState61, truthState60,
        truthState59, truthState58, truthState57, truthState56, truthState55, truthState54,
        truthState53, truthState52, truthState51, truthState50, truthState49, truthState48,
        truthState47, truthState46, truthState45, truthState44, truthState43, truthState42,
        truthState41, truthState40, truthState39, truthState38, truthState37, truthState36,
        truthState35, truthState34, truthState33, truthState32, truthState31, truthState30,
        truthState29, truthState28, truthState27, truthState26, truthState25, truthState24,
        truthState23, truthState22, truthState21, truthState20, truthState19, truthState18,
        truthState17, truthState16, truthState15, truthState14, truthState13, truthState12,
        truthState11, truthState10, truthState9, truthState8, truthState7, truthState6,
        truthState5, truthState4, truthState3, truthState2, truthState1, truthInitialState,
        truthExecutionEnv]
    rw [hcode]
    exact truth_valid_jumpdest_5e
  rw [hcontains]
  simp [truthState73, truthState72, truthState71]

theorem truth_decode_pc94 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState73.machineState.pc =
      some (.JUMPDEST, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x5e⟩ : Ethereum.UInt256) =
    some (.JUMPDEST, none)
  native_decide

set_option maxRecDepth 10000 in
theorem truth_xstep_pc94 :
    Ethereum.EVM.Xstep truthValidJumps truthState73 =
      .ok (truthState74, .none) := by
  simpa [truthValidJumps, truthState74, truthState73] using
    Ethereum.EVM.step_jumpdest truthState73 truth_decode_pc94

theorem truth_decode_pc95 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState74.machineState.pc =
      some (.DUP3, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x5f⟩ : Ethereum.UInt256) =
    some (.DUP3, none)
  native_decide

set_option maxRecDepth 10000 in
theorem truth_xstep_pc95 :
    Ethereum.EVM.Xstep truthValidJumps truthState74 =
      .ok (truthState75, .none) := by
  simpa [truthValidJumps, truthState75] using
    Ethereum.EVM.step_dup3 truthState74 truth_decode_pc95

theorem truth_decode_pc96 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState75.machineState.pc =
      some (.MSTORE, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x60⟩ : Ethereum.UInt256) =
    some (.MSTORE, none)
  native_decide

theorem truth_xstep_pc96 :
    Ethereum.EVM.Xstep truthValidJumps truthState75 =
      .ok (truthState76, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthState75.executionEnv.code ⟨0⟩ by
    rw [show truthState75.executionEnv.code = truthRuntimeBytecode by
      change truthState15.executionEnv.code = truthRuntimeBytecode
      simp [truthState15, truthState14, truthState13, truthState12, truthState11,
        truthState10, truthState9, truthState8, truthState7, truthState6, truthState5,
        truthState4, truthState3, truthState2, truthState1, truthInitialState, truthExecutionEnv]]
    rfl]
  rw [Ethereum.EVM.step_mstore truthState75 truth_decode_pc96]
  rw [show truthState75.machineState.stack =
      truthFreeMemPtr :: (⟨1⟩ : Ethereum.UInt256) ::
        (⟨1⟩ : Ethereum.UInt256) :: truthFreeMemPtr :: (⟨0x75⟩ : Ethereum.UInt256) ::
        truthAbiEnd :: truthFreeMemPtr :: (⟨1⟩ : Ethereum.UInt256) ::
        (⟨0x3b⟩ : Ethereum.UInt256) :: truthSelectorWord :: [] by rfl]
  change
    (if truthState75.machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost truthState75 .MSTORE then _ else _) = _
  rw [if_neg truth_pc96_has_memory_gas]
  change
    (if (truthState75.machineState.gasAvailable -
          Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost truthState75 .MSTORE)).toNat <
        GasConstants.Gverylow then _ else _) = _
  rw [if_neg truth_pc96_has_verylow_gas]
  simp only [truthState75, truthState76, truthEncodedMemory, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  have hoverflow : ¬ 8 > 1024 := by native_decide
  rw [if_neg hoverflow]

theorem truth_decode_pc97 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState76.machineState.pc =
      some (.POP, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x61⟩ : Ethereum.UInt256) =
    some (.POP, none)
  native_decide

theorem truth_xstep_pc97 :
    Ethereum.EVM.Xstep truthValidJumps truthState76 =
      .ok (truthState77, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthState76.executionEnv.code ⟨0⟩ by
    rw [show truthState76.executionEnv.code = truthRuntimeBytecode by
      rw [show truthState76.executionEnv = truthState75.executionEnv by rfl]
      rw [show truthState75.executionEnv = truthState74.executionEnv by rfl]
      rw [show truthState74.executionEnv = truthState73.executionEnv by rfl]
      rw [show truthState73.executionEnv = truthState72.executionEnv by rfl]
      rw [show truthState72.executionEnv = truthState71.executionEnv by rfl]
      rw [show truthState71.executionEnv = truthState70.executionEnv by rfl]
      rw [show truthState70.executionEnv = truthState69.executionEnv by rfl]
      rw [show truthState69.executionEnv = truthState68.executionEnv by rfl]
      rw [show truthState68.executionEnv = truthState67.executionEnv by rfl]
      rw [show truthState67.executionEnv = truthState66.executionEnv by rfl]
      rw [show truthState66.executionEnv = truthState65.executionEnv by rfl]
      rw [show truthState65.executionEnv = truthState64.executionEnv by rfl]
      rw [show truthState64.executionEnv = truthState63.executionEnv by rfl]
      rw [show truthState63.executionEnv = truthState62.executionEnv by rfl]
      rw [show truthState62.executionEnv = truthState61.executionEnv by rfl]
      rw [show truthState61.executionEnv = truthState60.executionEnv by rfl]
      rw [show truthState60.executionEnv = truthState59.executionEnv by rfl]
      rw [show truthState59.executionEnv = truthState58.executionEnv by rfl]
      rw [show truthState58.executionEnv = truthState57.executionEnv by rfl]
      rw [show truthState57.executionEnv = truthState56.executionEnv by rfl]
      rw [show truthState56.executionEnv = truthState55.executionEnv by rfl]
      rw [show truthState55.executionEnv = truthState54.executionEnv by rfl]
      rw [show truthState54.executionEnv = truthState53.executionEnv by rfl]
      rw [show truthState53.executionEnv = truthState52.executionEnv by rfl]
      rw [show truthState52.executionEnv = truthState51.executionEnv by rfl]
      rw [show truthState51.executionEnv = truthState50.executionEnv by rfl]
      rw [show truthState50.executionEnv = truthState49.executionEnv by rfl]
      rw [show truthState49.executionEnv = truthState48.executionEnv by rfl]
      rw [show truthState48.executionEnv = truthState47.executionEnv by rfl]
      rw [show truthState47.executionEnv = truthState46.executionEnv by rfl]
      rw [show truthState46.executionEnv = truthState45.executionEnv by rfl]
      rw [show truthState45.executionEnv = truthState44.executionEnv by rfl]
      rw [show truthState44.executionEnv = truthState43.executionEnv by rfl]
      rw [show truthState43.executionEnv = truthState42.executionEnv by rfl]
      rw [show truthState42.executionEnv = truthState41.executionEnv by rfl]
      rw [show truthState41.executionEnv = truthState40.executionEnv by rfl]
      rw [show truthState40.executionEnv = truthState39.executionEnv by rfl]
      rw [show truthState39.executionEnv = truthState38.executionEnv by rfl]
      rw [show truthState38.executionEnv = truthState37.executionEnv by rfl]
      rw [show truthState37.executionEnv = truthState36.executionEnv by rfl]
      rw [show truthState36.executionEnv = truthState35.executionEnv by rfl]
      rw [show truthState35.executionEnv = truthState34.executionEnv by rfl]
      rw [show truthState34.executionEnv = truthState33.executionEnv by rfl]
      rw [show truthState33.executionEnv = truthState32.executionEnv by rfl]
      rw [show truthState32.executionEnv = truthState31.executionEnv by rfl]
      rw [show truthState31.executionEnv = truthState30.executionEnv by rfl]
      rw [show truthState30.executionEnv = truthState29.executionEnv by rfl]
      rw [show truthState29.executionEnv = truthState28.executionEnv by rfl]
      rw [show truthState28.executionEnv = truthState27.executionEnv by rfl]
      rw [show truthState27.executionEnv = truthState26.executionEnv by rfl]
      rw [show truthState26.executionEnv = truthState25.executionEnv by rfl]
      rw [show truthState25.executionEnv = truthState24.executionEnv by rfl]
      rw [show truthState24.executionEnv = truthState23.executionEnv by rfl]
      rw [show truthState23.executionEnv = truthState22.executionEnv by rfl]
      rw [show truthState22.executionEnv = truthState21.executionEnv by rfl]
      rw [show truthState21.executionEnv = truthState20.executionEnv by rfl]
      rw [show truthState20.executionEnv = truthState19.executionEnv by rfl]
      rw [show truthState19.executionEnv = truthState18.executionEnv by rfl]
      rw [show truthState18.executionEnv = truthState17.executionEnv by rfl]
      rw [show truthState17.executionEnv = truthState16.executionEnv by rfl]
      rw [show truthState16.executionEnv = truthState15.executionEnv by rfl]
      simp [truthState15, truthState14, truthState13, truthState12, truthState11,
        truthState10, truthState9, truthState8, truthState7, truthState6, truthState5,
        truthState4, truthState3, truthState2, truthState1, truthInitialState, truthExecutionEnv]]
    rfl]
  rw [Ethereum.EVM.step_pop truthState76 truth_decode_pc97]
  change (if truthState76.machineState.gasAvailable.toNat < GasConstants.Gbase then _ else _) = _
  rw [if_neg truth_pc97_has_gas]
  simp only [truthState76, truthState77, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub]
  have hoverflow : ¬ 7 > 1024 := by native_decide
  rw [if_neg hoverflow]

theorem truth_decode_pc98 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState77.machineState.pc =
      some (.POP, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x62⟩ : Ethereum.UInt256) =
    some (.POP, none)
  native_decide

theorem truth_xstep_pc98 :
    Ethereum.EVM.Xstep truthValidJumps truthState77 =
      .ok (truthState78, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthState77.executionEnv.code ⟨0⟩ by
    rw [show truthState77.executionEnv = truthState76.executionEnv by rfl]
    rw [show truthState76.executionEnv.code = truthRuntimeBytecode by
      rw [show truthState76.executionEnv = truthState75.executionEnv by rfl]
      rw [show truthState75.executionEnv = truthState74.executionEnv by rfl]
      rw [show truthState74.executionEnv = truthState73.executionEnv by rfl]
      rw [show truthState73.executionEnv = truthState72.executionEnv by rfl]
      rw [show truthState72.executionEnv = truthState71.executionEnv by rfl]
      rw [show truthState71.executionEnv = truthState70.executionEnv by rfl]
      rw [show truthState70.executionEnv = truthState69.executionEnv by rfl]
      rw [show truthState69.executionEnv = truthState68.executionEnv by rfl]
      rw [show truthState68.executionEnv = truthState67.executionEnv by rfl]
      rw [show truthState67.executionEnv = truthState66.executionEnv by rfl]
      rw [show truthState66.executionEnv = truthState65.executionEnv by rfl]
      rw [show truthState65.executionEnv = truthState64.executionEnv by rfl]
      rw [show truthState64.executionEnv = truthState63.executionEnv by rfl]
      rw [show truthState63.executionEnv = truthState62.executionEnv by rfl]
      rw [show truthState62.executionEnv = truthState61.executionEnv by rfl]
      rw [show truthState61.executionEnv = truthState60.executionEnv by rfl]
      rw [show truthState60.executionEnv = truthState59.executionEnv by rfl]
      rw [show truthState59.executionEnv = truthState58.executionEnv by rfl]
      rw [show truthState58.executionEnv = truthState57.executionEnv by rfl]
      rw [show truthState57.executionEnv = truthState56.executionEnv by rfl]
      rw [show truthState56.executionEnv = truthState55.executionEnv by rfl]
      rw [show truthState55.executionEnv = truthState54.executionEnv by rfl]
      rw [show truthState54.executionEnv = truthState53.executionEnv by rfl]
      rw [show truthState53.executionEnv = truthState52.executionEnv by rfl]
      rw [show truthState52.executionEnv = truthState51.executionEnv by rfl]
      rw [show truthState51.executionEnv = truthState50.executionEnv by rfl]
      rw [show truthState50.executionEnv = truthState49.executionEnv by rfl]
      rw [show truthState49.executionEnv = truthState48.executionEnv by rfl]
      rw [show truthState48.executionEnv = truthState47.executionEnv by rfl]
      rw [show truthState47.executionEnv = truthState46.executionEnv by rfl]
      rw [show truthState46.executionEnv = truthState45.executionEnv by rfl]
      rw [show truthState45.executionEnv = truthState44.executionEnv by rfl]
      rw [show truthState44.executionEnv = truthState43.executionEnv by rfl]
      rw [show truthState43.executionEnv = truthState42.executionEnv by rfl]
      rw [show truthState42.executionEnv = truthState41.executionEnv by rfl]
      rw [show truthState41.executionEnv = truthState40.executionEnv by rfl]
      rw [show truthState40.executionEnv = truthState39.executionEnv by rfl]
      rw [show truthState39.executionEnv = truthState38.executionEnv by rfl]
      rw [show truthState38.executionEnv = truthState37.executionEnv by rfl]
      rw [show truthState37.executionEnv = truthState36.executionEnv by rfl]
      rw [show truthState36.executionEnv = truthState35.executionEnv by rfl]
      rw [show truthState35.executionEnv = truthState34.executionEnv by rfl]
      rw [show truthState34.executionEnv = truthState33.executionEnv by rfl]
      rw [show truthState33.executionEnv = truthState32.executionEnv by rfl]
      rw [show truthState32.executionEnv = truthState31.executionEnv by rfl]
      rw [show truthState31.executionEnv = truthState30.executionEnv by rfl]
      rw [show truthState30.executionEnv = truthState29.executionEnv by rfl]
      rw [show truthState29.executionEnv = truthState28.executionEnv by rfl]
      rw [show truthState28.executionEnv = truthState27.executionEnv by rfl]
      rw [show truthState27.executionEnv = truthState26.executionEnv by rfl]
      rw [show truthState26.executionEnv = truthState25.executionEnv by rfl]
      rw [show truthState25.executionEnv = truthState24.executionEnv by rfl]
      rw [show truthState24.executionEnv = truthState23.executionEnv by rfl]
      rw [show truthState23.executionEnv = truthState22.executionEnv by rfl]
      rw [show truthState22.executionEnv = truthState21.executionEnv by rfl]
      rw [show truthState21.executionEnv = truthState20.executionEnv by rfl]
      rw [show truthState20.executionEnv = truthState19.executionEnv by rfl]
      rw [show truthState19.executionEnv = truthState18.executionEnv by rfl]
      rw [show truthState18.executionEnv = truthState17.executionEnv by rfl]
      rw [show truthState17.executionEnv = truthState16.executionEnv by rfl]
      rw [show truthState16.executionEnv = truthState15.executionEnv by rfl]
      simp [truthState15, truthState14, truthState13, truthState12, truthState11,
        truthState10, truthState9, truthState8, truthState7, truthState6, truthState5,
        truthState4, truthState3, truthState2, truthState1, truthInitialState, truthExecutionEnv]]
    rfl]
  rw [Ethereum.EVM.step_pop truthState77 truth_decode_pc98]
  change (if truthState77.machineState.gasAvailable.toNat < GasConstants.Gbase then _ else _) = _
  rw [if_neg truth_pc98_has_gas]
  simp only [truthState77, truthState78, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub]
  have hoverflow : ¬ 6 > 1024 := by native_decide
  rw [if_neg hoverflow]

theorem truth_valid_jumpdest_75 :
    (Ethereum.EVM.D_J truthRuntimeBytecode ⟨0⟩).contains (⟨0x75⟩ : Ethereum.UInt256) = true := by
  native_decide

theorem truth_decode_pc99 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState78.machineState.pc =
      some (.JUMP, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x63⟩ : Ethereum.UInt256) =
    some (.JUMP, none)
  native_decide

theorem truth_xstep_pc99 :
    Ethereum.EVM.Xstep truthValidJumps truthState78 =
      .ok (truthState79, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthState78.executionEnv.code ⟨0⟩ by
    rw [show truthState78.executionEnv.code = truthRuntimeBytecode by
      change truthState15.executionEnv.code = truthRuntimeBytecode
      simp [truthState15, truthState14, truthState13, truthState12, truthState11,
        truthState10, truthState9, truthState8, truthState7, truthState6, truthState5,
        truthState4, truthState3, truthState2, truthState1, truthInitialState, truthExecutionEnv]]
    rfl]
  rw [Ethereum.EVM.step_jump truthState78 truth_decode_pc99]
  rw [show truthState78.machineState.stack =
      (⟨0x75⟩ : Ethereum.UInt256) :: truthAbiEnd :: truthFreeMemPtr ::
        (⟨1⟩ : Ethereum.UInt256) :: (⟨0x3b⟩ : Ethereum.UInt256) :: truthSelectorWord :: [] by rfl]
  change
    (if truthState78.machineState.gasAvailable.toNat < GasConstants.Gmid then _ else _) = _
  rw [if_neg truth_pc99_has_gas]
  rw [show (Ethereum.EVM.D_J truthState78.executionEnv.code ⟨0⟩).contains
      (⟨0x75⟩ : Ethereum.UInt256) = true by
    rw [show truthState78.executionEnv.code = truthRuntimeBytecode by
      change truthState15.executionEnv.code = truthRuntimeBytecode
      simp [truthState15, truthState14, truthState13, truthState12, truthState11,
        truthState10, truthState9, truthState8, truthState7, truthState6, truthState5,
        truthState4, truthState3, truthState2, truthState1, truthInitialState, truthExecutionEnv]]
    exact truth_valid_jumpdest_75]
  simp only [not_true_eq_false, ↓reduceIte, truthState78, truthState79, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  have hlen : List.length truthState78.machineState.stack - 1 + 0 = 5 := by rfl
  try rw [hlen]
  have hoverflow : ¬ 5 > 1024 := by native_decide
  rw [if_neg hoverflow]

theorem truth_decode_pc117 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState79.machineState.pc =
      some (.JUMPDEST, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x75⟩ : Ethereum.UInt256) =
    some (.JUMPDEST, none)
  native_decide

theorem truth_xstep_pc117 :
    Ethereum.EVM.Xstep truthValidJumps truthState79 =
      .ok (truthState80, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthState79.executionEnv.code ⟨0⟩ by
    rw [show truthState79.executionEnv.code = truthRuntimeBytecode by
      change truthState15.executionEnv.code = truthRuntimeBytecode
      simp [truthState15, truthState14, truthState13, truthState12, truthState11,
        truthState10, truthState9, truthState8, truthState7, truthState6, truthState5,
        truthState4, truthState3, truthState2, truthState1, truthInitialState, truthExecutionEnv]]
    rfl]
  rw [Ethereum.EVM.step_jumpdest truthState79 truth_decode_pc117]
  rw [if_neg truth_pc117_has_gas]
  simp only [truthState79, truthState80, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub]
  have hoverflow : ¬ 5 > 1024 := by native_decide
  rw [if_neg hoverflow]

theorem truth_decode_pc118 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState80.machineState.pc =
      some (.SWAP3, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x76⟩ : Ethereum.UInt256) =
    some (.SWAP3, none)
  native_decide

theorem truth_xstep_pc118 :
    Ethereum.EVM.Xstep truthValidJumps truthState80 =
      .ok (truthState81, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthState80.executionEnv.code ⟨0⟩ by
    rw [show truthState80.executionEnv.code = truthRuntimeBytecode by
      change truthState15.executionEnv.code = truthRuntimeBytecode
      simp [truthState15, truthState14, truthState13, truthState12, truthState11,
        truthState10, truthState9, truthState8, truthState7, truthState6, truthState5,
        truthState4, truthState3, truthState2, truthState1, truthInitialState, truthExecutionEnv]]
    rfl]
  rw [Ethereum.EVM.step_swap3 truthState80 truth_decode_pc118]
  change (if truthState80.machineState.gasAvailable.toNat < GasConstants.Gverylow then _ else _) = _
  rw [if_neg truth_pc118_has_gas]
  simp only [truthState80, truthState81]
  have hlen : List.length truthState79.machineState.stack - 4 + 4 = 5 := by rfl
  rw [hlen]
  have hoverflow : ¬ 5 > 1024 := by native_decide
  rw [if_neg hoverflow]

theorem truth_decode_pc119 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState81.machineState.pc =
      some (.SWAP2, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x77⟩ : Ethereum.UInt256) =
    some (.SWAP2, none)
  native_decide

theorem truth_xstep_pc119 :
    Ethereum.EVM.Xstep truthValidJumps truthState81 =
      .ok (truthState82, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthState81.executionEnv.code ⟨0⟩ by
    rw [show truthState81.executionEnv.code = truthRuntimeBytecode by
      change truthState15.executionEnv.code = truthRuntimeBytecode
      simp [truthState15, truthState14, truthState13, truthState12, truthState11,
        truthState10, truthState9, truthState8, truthState7, truthState6, truthState5,
        truthState4, truthState3, truthState2, truthState1, truthInitialState, truthExecutionEnv]]
    rfl]
  rw [Ethereum.EVM.step_swap2 truthState81 truth_decode_pc119]
  change (if truthState81.machineState.gasAvailable.toNat < GasConstants.Gverylow then _ else _) = _
  rw [if_neg truth_pc119_has_gas]
  simp only [truthState81, truthState82, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub]
  have hoverflow : ¬ 5 > 1024 := by native_decide
  rw [if_neg hoverflow]

theorem truth_decode_pc120 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState82.machineState.pc =
      some (.POP, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x78⟩ : Ethereum.UInt256) =
    some (.POP, none)
  native_decide

theorem truth_xstep_pc120 :
    Ethereum.EVM.Xstep truthValidJumps truthState82 =
      .ok (truthState83, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthState82.executionEnv.code ⟨0⟩ by
    rw [show truthState82.executionEnv.code = truthRuntimeBytecode by
      change truthState15.executionEnv.code = truthRuntimeBytecode
      simp [truthState15, truthState14, truthState13, truthState12, truthState11,
        truthState10, truthState9, truthState8, truthState7, truthState6, truthState5,
        truthState4, truthState3, truthState2, truthState1, truthInitialState, truthExecutionEnv]]
    rfl]
  rw [Ethereum.EVM.step_pop truthState82 truth_decode_pc120]
  change (if truthState82.machineState.gasAvailable.toNat < GasConstants.Gbase then _ else _) = _
  rw [if_neg truth_pc120_has_gas]
  simp only [truthState82, truthState83, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub]
  have hoverflow : ¬ 4 > 1024 := by native_decide
  rw [if_neg hoverflow]

theorem truth_decode_pc121 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState83.machineState.pc =
      some (.POP, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x79⟩ : Ethereum.UInt256) =
    some (.POP, none)
  native_decide

theorem truth_xstep_pc121 :
    Ethereum.EVM.Xstep truthValidJumps truthState83 =
      .ok (truthState84, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthState83.executionEnv.code ⟨0⟩ by
    rw [show truthState83.executionEnv.code = truthRuntimeBytecode by
      change truthState15.executionEnv.code = truthRuntimeBytecode
      simp [truthState15, truthState14, truthState13, truthState12, truthState11,
        truthState10, truthState9, truthState8, truthState7, truthState6, truthState5,
        truthState4, truthState3, truthState2, truthState1, truthInitialState, truthExecutionEnv]]
    rfl]
  rw [Ethereum.EVM.step_pop truthState83 truth_decode_pc121]
  change (if truthState83.machineState.gasAvailable.toNat < GasConstants.Gbase then _ else _) = _
  rw [if_neg truth_pc121_has_gas]
  simp only [truthState83, truthState84, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub]
  have hoverflow : ¬ 3 > 1024 := by native_decide
  rw [if_neg hoverflow]

theorem truth_valid_jumpdest_3b :
    (Ethereum.EVM.D_J truthRuntimeBytecode ⟨0⟩).contains (⟨0x3b⟩ : Ethereum.UInt256) = true := by
  native_decide

theorem truth_decode_pc122 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState84.machineState.pc =
      some (.JUMP, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x7a⟩ : Ethereum.UInt256) =
    some (.JUMP, none)
  native_decide

theorem truth_xstep_pc122 :
    Ethereum.EVM.Xstep truthValidJumps truthState84 =
      .ok (truthState85, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthState84.executionEnv.code ⟨0⟩ by
    rw [show truthState84.executionEnv.code = truthRuntimeBytecode by
      change truthState15.executionEnv.code = truthRuntimeBytecode
      simp [truthState15, truthState14, truthState13, truthState12, truthState11,
        truthState10, truthState9, truthState8, truthState7, truthState6, truthState5,
        truthState4, truthState3, truthState2, truthState1, truthInitialState, truthExecutionEnv]]
    rfl]
  rw [Ethereum.EVM.step_jump truthState84 truth_decode_pc122]
  change
    (if truthState84.machineState.gasAvailable.toNat < GasConstants.Gmid then _ else _) = _
  rw [if_neg truth_pc122_has_gas]
  rw [show (Ethereum.EVM.D_J truthState84.executionEnv.code ⟨0⟩).contains
      (⟨0x3b⟩ : Ethereum.UInt256) = true by
    rw [show truthState84.executionEnv.code = truthRuntimeBytecode by
      change truthState15.executionEnv.code = truthRuntimeBytecode
      simp [truthState15, truthState14, truthState13, truthState12, truthState11,
        truthState10, truthState9, truthState8, truthState7, truthState6, truthState5,
        truthState4, truthState3, truthState2, truthState1, truthInitialState, truthExecutionEnv]]
    exact truth_valid_jumpdest_3b]
  simp only [not_true_eq_false, ↓reduceIte, truthState84, truthState85, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  have hoverflow : ¬ 2 > 1024 := by native_decide
  rw [if_neg hoverflow]

theorem truth_decode_pc59 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState85.machineState.pc =
      some (.JUMPDEST, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x3b⟩ : Ethereum.UInt256) =
    some (.JUMPDEST, none)
  native_decide

theorem truth_xstep_pc59 :
    Ethereum.EVM.Xstep truthValidJumps truthState85 =
      .ok (truthState86, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthState85.executionEnv.code ⟨0⟩ by
    rw [show truthState85.executionEnv.code = truthRuntimeBytecode by
      change truthState15.executionEnv.code = truthRuntimeBytecode
      simp [truthState15, truthState14, truthState13, truthState12, truthState11,
        truthState10, truthState9, truthState8, truthState7, truthState6, truthState5,
        truthState4, truthState3, truthState2, truthState1, truthInitialState, truthExecutionEnv]]
    rfl]
  rw [Ethereum.EVM.step_jumpdest truthState85 truth_decode_pc59]
  rw [if_neg truth_pc59_has_gas]
  simp only [truthState85, truthState86, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub]
  have hoverflow : ¬ 2 > 1024 := by native_decide
  rw [if_neg hoverflow]

theorem truth_decode_pc60 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState86.machineState.pc =
      some (.PUSH1, some ((⟨0x40⟩ : Ethereum.UInt256), 1)) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x3c⟩ : Ethereum.UInt256) =
    some (.PUSH1, some ((⟨0x40⟩ : Ethereum.UInt256), 1))
  native_decide

theorem truth_xstep_pc60 :
    Ethereum.EVM.Xstep truthValidJumps truthState86 =
      .ok (truthState87, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthState86.executionEnv.code ⟨0⟩ by
    rw [show truthState86.executionEnv.code = truthRuntimeBytecode by
      change truthState15.executionEnv.code = truthRuntimeBytecode
      simp [truthState15, truthState14, truthState13, truthState12, truthState11,
        truthState10, truthState9, truthState8, truthState7, truthState6, truthState5,
        truthState4, truthState3, truthState2, truthState1, truthInitialState, truthExecutionEnv]]
    rfl]
  rw [Ethereum.EVM.step_push1 truthState86 (⟨0x40⟩ : Ethereum.UInt256) truth_decode_pc60]
  rw [if_neg truth_pc60_has_gas]
  simp only [truthState86, truthState87]
  have hlen : List.length truthState85.machineState.stack - 0 + 1 = 3 := by rfl
  rw [hlen]
  have hoverflow : ¬ 3 > 1024 := by native_decide
  rw [if_neg hoverflow]

theorem truth_decode_pc62 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState87.machineState.pc =
      some (.MLOAD, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x3e⟩ : Ethereum.UInt256) =
    some (.MLOAD, none)
  native_decide

theorem truth_xstep_pc62 :
    Ethereum.EVM.Xstep truthValidJumps truthState87 =
      .ok (truthState88, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthState87.executionEnv.code ⟨0⟩ by
    rw [show truthState87.executionEnv.code = truthRuntimeBytecode by
      change truthState15.executionEnv.code = truthRuntimeBytecode
      simp [truthState15, truthState14, truthState13, truthState12, truthState11,
        truthState10, truthState9, truthState8, truthState7, truthState6, truthState5,
        truthState4, truthState3, truthState2, truthState1, truthInitialState, truthExecutionEnv]]
    rfl]
  rw [Ethereum.EVM.step_mload truthState87 truth_decode_pc62]
  rw [show truthState87.machineState.stack =
      (⟨0x40⟩ : Ethereum.UInt256) :: truthAbiEnd :: truthSelectorWord :: [] by rfl]
  change
    (if truthState87.machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost truthState87 .MLOAD then _ else _) = _
  rw [if_neg truth_pc62_has_memory_gas]
  change
    (if (truthState87.machineState.gasAvailable -
          Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost truthState87 .MLOAD)).toNat <
        GasConstants.Gverylow then _ else _) = _
  rw [if_neg truth_pc62_has_verylow_gas]
  simp only [truthState87, truthState88, truthFinalFreeMemPtr, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  have hoverflow : ¬ 3 > 1024 := by native_decide
  rw [if_neg hoverflow]

theorem truth_decode_pc63 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState88.machineState.pc =
      some (.DUP1, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x3f⟩ : Ethereum.UInt256) =
    some (.DUP1, none)
  native_decide

theorem truth_xstep_pc63 :
    Ethereum.EVM.Xstep truthValidJumps truthState88 =
      .ok (truthState89, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthState88.executionEnv.code ⟨0⟩ by
    rw [show truthState88.executionEnv.code = truthRuntimeBytecode by
      change truthState15.executionEnv.code = truthRuntimeBytecode
      simp [truthState15, truthState14, truthState13, truthState12, truthState11,
        truthState10, truthState9, truthState8, truthState7, truthState6, truthState5,
        truthState4, truthState3, truthState2, truthState1, truthInitialState, truthExecutionEnv]]
    rfl]
  rw [Ethereum.EVM.step_dup1 truthState88 truth_decode_pc63]
  rw [show truthState88.machineState.stack =
      truthFinalFreeMemPtr :: truthAbiEnd :: truthSelectorWord :: [] by rfl]
  change (if truthState88.machineState.gasAvailable.toNat < GasConstants.Gverylow then _ else _) = _
  rw [if_neg truth_pc63_has_gas]
  simp only [truthState88, truthState89, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub]
  have hlen : List.length truthState88.machineState.stack - 1 + 2 = 4 := by rfl
  try rw [hlen]
  have hoverflow : ¬ 4 > 1024 := by native_decide
  rw [if_neg hoverflow]

theorem truth_decode_pc64 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState89.machineState.pc =
      some (.SWAP2, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x40⟩ : Ethereum.UInt256) =
    some (.SWAP2, none)
  native_decide

theorem truth_xstep_pc64 :
    Ethereum.EVM.Xstep truthValidJumps truthState89 =
      .ok (truthState90, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthState89.executionEnv.code ⟨0⟩ by
    rw [show truthState89.executionEnv.code = truthRuntimeBytecode by
      change truthState15.executionEnv.code = truthRuntimeBytecode
      simp [truthState15, truthState14, truthState13, truthState12, truthState11,
        truthState10, truthState9, truthState8, truthState7, truthState6, truthState5,
        truthState4, truthState3, truthState2, truthState1, truthInitialState, truthExecutionEnv]]
    rfl]
  rw [Ethereum.EVM.step_swap2 truthState89 truth_decode_pc64]
  rw [show truthState89.machineState.stack =
      truthFinalFreeMemPtr :: truthFinalFreeMemPtr :: truthAbiEnd :: truthSelectorWord :: [] by rfl]
  change (if truthState89.machineState.gasAvailable.toNat < GasConstants.Gverylow then _ else _) = _
  rw [if_neg truth_pc64_has_gas]
  simp only [truthState89, truthState90, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub]
  have hlen : List.length truthState89.machineState.stack - 3 + 3 = 4 := by rfl
  try rw [hlen]
  have hoverflow : ¬ 4 > 1024 := by native_decide
  rw [if_neg hoverflow]

theorem truth_decode_pc65 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState90.machineState.pc =
      some (.SUB, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x41⟩ : Ethereum.UInt256) =
    some (.SUB, none)
  native_decide

theorem truth_xstep_pc65 :
    Ethereum.EVM.Xstep truthValidJumps truthState90 =
      .ok (truthState91, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthState90.executionEnv.code ⟨0⟩ by
    rw [show truthState90.executionEnv.code = truthRuntimeBytecode by
      change truthState15.executionEnv.code = truthRuntimeBytecode
      simp [truthState15, truthState14, truthState13, truthState12, truthState11,
        truthState10, truthState9, truthState8, truthState7, truthState6, truthState5,
        truthState4, truthState3, truthState2, truthState1, truthInitialState, truthExecutionEnv]]
    rfl]
  rw [Ethereum.EVM.step_sub truthState90 truth_decode_pc65]
  rw [show truthState90.machineState.stack =
      truthAbiEnd :: truthFinalFreeMemPtr :: truthFinalFreeMemPtr :: truthSelectorWord :: [] by rfl]
  change (if truthState90.machineState.gasAvailable.toNat < GasConstants.Gverylow then _ else _) = _
  rw [if_neg truth_pc65_has_gas]
  simp only [truthState90, truthState91, truthReturnLength, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  have hlen : List.length truthState90.machineState.stack - 2 + 1 = 3 := by rfl
  try rw [hlen]
  have hoverflow : ¬ 3 > 1024 := by native_decide
  rw [if_neg hoverflow]

theorem truth_decode_pc66 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState91.machineState.pc =
      some (.SWAP1, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x42⟩ : Ethereum.UInt256) =
    some (.SWAP1, none)
  native_decide

theorem truth_xstep_pc66 :
    Ethereum.EVM.Xstep truthValidJumps truthState91 =
      .ok (truthState92, .none) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthState91.executionEnv.code ⟨0⟩ by
    rw [show truthState91.executionEnv.code = truthRuntimeBytecode by
      change truthState15.executionEnv.code = truthRuntimeBytecode
      simp [truthState15, truthState14, truthState13, truthState12, truthState11,
        truthState10, truthState9, truthState8, truthState7, truthState6, truthState5,
        truthState4, truthState3, truthState2, truthState1, truthInitialState, truthExecutionEnv]]
    rfl]
  rw [Ethereum.EVM.step_swap1 truthState91 truth_decode_pc66]
  rw [show truthState91.machineState.stack =
      truthReturnLength :: truthFinalFreeMemPtr :: truthSelectorWord :: [] by rfl]
  change (if truthState91.machineState.gasAvailable.toNat < GasConstants.Gverylow then _ else _) = _
  rw [if_neg truth_pc66_has_gas]
  simp only [truthState91, truthState92, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub]
  have hlen : List.length truthState91.machineState.stack - 2 + 2 = 3 := by rfl
  try rw [hlen]
  have hoverflow : ¬ 3 > 1024 := by native_decide
  rw [if_neg hoverflow]

theorem truth_decode_pc67 :
    Ethereum.EVM.decode truthRuntimeBytecode truthState92.machineState.pc =
      some (.RETURN, none) := by
  change Ethereum.EVM.decode truthRuntimeBytecode (⟨0x43⟩ : Ethereum.UInt256) =
    some (.RETURN, none)
  native_decide

theorem truth_xstep_pc67 :
    Ethereum.EVM.Xstep truthValidJumps truthState92 =
      .ok (truthState93, some (true, truthReturnData)) := by
  rw [show truthValidJumps = Ethereum.EVM.D_J truthState92.executionEnv.code ⟨0⟩ by
    rw [show truthState92.executionEnv.code = truthRuntimeBytecode by
      change truthState15.executionEnv.code = truthRuntimeBytecode
      simp [truthState15, truthState14, truthState13, truthState12, truthState11,
        truthState10, truthState9, truthState8, truthState7, truthState6, truthState5,
        truthState4, truthState3, truthState2, truthState1, truthInitialState, truthExecutionEnv]]
    rfl]
  rw [Ethereum.EVM.step_return truthState92 truth_decode_pc67]
  rw [show truthState92.machineState.stack =
      truthFinalFreeMemPtr :: truthReturnLength :: truthSelectorWord :: [] by rfl]
  change
    (if truthState92.machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost truthState92 .RETURN then _ else _) = _
  rw [if_neg truth_pc67_has_gas]
  simp only [truthState92, truthState93, truthFinalReturnData, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  have hoverflow : ¬ 1 > 1024 := by native_decide
  rw [if_neg hoverflow]
  have hret :
      truthState91.machineState.memory.readWithPadding
        truthFinalFreeMemPtr.toNat truthReturnLength.toNat = truthReturnData := by
    rw [← truth_final_return_data_eq]
    rfl
  rw [hret]

macro "truth_continue_step " h:term : tactic =>
  `(tactic| (apply Ethereum.EVM.Xstep_X_X_continue
             · exact $h))

theorem truth_X_trace :
    Ethereum.EVM.X 100001 truthValidJumps truthInitialState =
      .ok (.success truthState93 truthReturnData) := by
  truth_continue_step truth_xstep_pc0
  truth_continue_step truth_xstep_pc2
  truth_continue_step truth_xstep_pc4
  truth_continue_step truth_xstep_pc5
  truth_continue_step truth_xstep_pc6
  truth_continue_step truth_xstep_pc7
  truth_continue_step truth_xstep_pc8
  truth_continue_step truth_xstep_pc10
  truth_continue_step truth_xstep_pc14
  truth_continue_step truth_xstep_pc15
  truth_continue_step truth_xstep_pc16
  truth_continue_step truth_xstep_pc18
  truth_continue_step truth_xstep_pc19
  truth_continue_step truth_xstep_pc20
  truth_continue_step truth_xstep_pc22
  truth_continue_step truth_xstep_pc23
  truth_continue_step truth_xstep_pc24
  truth_continue_step truth_xstep_pc25
  truth_continue_step truth_xstep_pc27
  truth_continue_step truth_xstep_pc28
  truth_continue_step truth_xstep_pc29
  truth_continue_step truth_xstep_pc34
  truth_continue_step truth_xstep_pc35
  truth_continue_step truth_xstep_pc37
  truth_continue_step truth_xstep_pc42
  truth_continue_step truth_xstep_pc43
  truth_continue_step truth_xstep_pc45
  truth_continue_step truth_xstep_pc47
  truth_continue_step truth_xstep_pc68
  truth_continue_step truth_xstep_pc69
  truth_continue_step truth_xstep_pc70
  truth_continue_step truth_xstep_pc72
  truth_continue_step truth_xstep_pc73
  truth_continue_step truth_xstep_pc74
  truth_continue_step truth_xstep_pc75
  truth_continue_step truth_xstep_pc48
  truth_continue_step truth_xstep_pc49
  truth_continue_step truth_xstep_pc51
  truth_continue_step truth_xstep_pc52
  truth_continue_step truth_xstep_pc54
  truth_continue_step truth_xstep_pc55
  truth_continue_step truth_xstep_pc56
  truth_continue_step truth_xstep_pc58
  truth_continue_step truth_xstep_pc100
  truth_continue_step truth_xstep_pc101
  truth_continue_step truth_xstep_pc102
  truth_continue_step truth_xstep_pc104
  truth_continue_step truth_xstep_pc105
  truth_continue_step truth_xstep_pc106
  truth_continue_step truth_xstep_pc107
  truth_continue_step truth_xstep_pc108
  truth_continue_step truth_xstep_pc110
  truth_continue_step truth_xstep_pc111
  truth_continue_step truth_xstep_pc112
  truth_continue_step truth_xstep_pc113
  truth_continue_step truth_xstep_pc114
  truth_continue_step truth_xstep_pc116
  truth_continue_step truth_xstep_pc87
  truth_continue_step truth_xstep_pc88
  truth_continue_step truth_xstep_pc90
  truth_continue_step truth_xstep_pc91
  truth_continue_step truth_xstep_pc93
  truth_continue_step truth_xstep_pc76
  truth_continue_step truth_xstep_pc77
  truth_continue_step truth_xstep_pc78
  truth_continue_step truth_xstep_pc79
  truth_continue_step truth_xstep_pc80
  truth_continue_step truth_xstep_pc81
  truth_continue_step truth_xstep_pc82
  truth_continue_step truth_xstep_pc83
  truth_continue_step truth_xstep_pc84
  truth_continue_step truth_xstep_pc85
  truth_continue_step truth_xstep_pc86
  truth_continue_step truth_xstep_pc94
  truth_continue_step truth_xstep_pc95
  truth_continue_step truth_xstep_pc96
  truth_continue_step truth_xstep_pc97
  truth_continue_step truth_xstep_pc98
  truth_continue_step truth_xstep_pc99
  truth_continue_step truth_xstep_pc117
  truth_continue_step truth_xstep_pc118
  truth_continue_step truth_xstep_pc119
  truth_continue_step truth_xstep_pc120
  truth_continue_step truth_xstep_pc121
  truth_continue_step truth_xstep_pc122
  truth_continue_step truth_xstep_pc59
  truth_continue_step truth_xstep_pc60
  truth_continue_step truth_xstep_pc62
  truth_continue_step truth_xstep_pc63
  truth_continue_step truth_xstep_pc64
  truth_continue_step truth_xstep_pc65
  truth_continue_step truth_xstep_pc66
  apply Ethereum.EVM.Xstep_X_X_halt_success
  exact truth_xstep_pc67

theorem truth_Xi_trace :
    Ethereum.EVM.Ξ truthInitialState.createdAccounts truthInitialState.genesisBlockHeader
      truthInitialState.blocks truthInitialState.accountMap truthInitialState.σ₀
      (⟨100000⟩ : Ethereum.UInt256) truthInitialState.substate truthExecutionEnv =
        .ok (.success
          (truthState93.createdAccounts, truthState93.accountMap,
            truthState93.machineState.gasAvailable, truthState93.substate)
          truthReturnData) := by
  unfold Ethereum.EVM.Ξ
  change
    (do
      let result ← Ethereum.EVM.X 100001 truthValidJumps truthInitialState
      match result with
      | Ethereum.ExecutionResult.success evmState' o =>
          .ok (Ethereum.ExecutionResult.success
            (evmState'.createdAccounts, evmState'.accountMap,
              evmState'.machineState.gasAvailable, evmState'.substate) o)
      | Ethereum.ExecutionResult.revert g' o => .ok (Ethereum.ExecutionResult.revert g' o)) =
      .ok (Ethereum.ExecutionResult.success
        (truthState93.createdAccounts, truthState93.accountMap,
          truthState93.machineState.gasAvailable, truthState93.substate)
        truthReturnData)
  rw [truth_X_trace]
  simp [bind, Except.bind]

theorem truth_nonpayable_X_trace :
    Ethereum.EVM.X 100001 truthValidJumps truthNonpayableInitialState =
      .ok (.revert truthNonpayableState11.machineState.gasAvailable truthNonpayableReturnData) := by
  truth_continue_step truth_nonpayable_xstep_pc0
  truth_continue_step truth_nonpayable_xstep_pc2
  truth_continue_step truth_nonpayable_xstep_pc4
  truth_continue_step truth_nonpayable_xstep_pc5
  truth_continue_step truth_nonpayable_xstep_pc6
  truth_continue_step truth_nonpayable_xstep_pc7
  truth_continue_step truth_nonpayable_xstep_pc8
  truth_continue_step truth_nonpayable_xstep_pc10
  truth_continue_step truth_nonpayable_xstep_pc11
  truth_continue_step truth_nonpayable_xstep_pc12
  apply Ethereum.EVM.Xstep_X_X_halt_revert
  exact truth_nonpayable_xstep_pc13

theorem truth_nonpayable_Xi_trace :
    Ethereum.EVM.Ξ truthNonpayableInitialState.createdAccounts
      truthNonpayableInitialState.genesisBlockHeader truthNonpayableInitialState.blocks
      truthNonpayableInitialState.accountMap truthNonpayableInitialState.σ₀
      (⟨100000⟩ : Ethereum.UInt256) truthNonpayableInitialState.substate
      truthNonpayableExecutionEnv =
        .ok (.revert truthNonpayableState11.machineState.gasAvailable
          truthNonpayableReturnData) := by
  unfold Ethereum.EVM.Ξ
  change
    (do
      let result ← Ethereum.EVM.X 100001 truthValidJumps truthNonpayableInitialState
      match result with
      | Ethereum.ExecutionResult.success evmState' o =>
          .ok (Ethereum.ExecutionResult.success
            (evmState'.createdAccounts, evmState'.accountMap,
              evmState'.machineState.gasAvailable, evmState'.substate) o)
      | Ethereum.ExecutionResult.revert g' o => .ok (Ethereum.ExecutionResult.revert g' o)) =
      .ok (Ethereum.ExecutionResult.revert
        truthNonpayableState11.machineState.gasAvailable truthNonpayableReturnData)
  rw [truth_nonpayable_X_trace]
  simp [bind, Except.bind]

theorem truth_short_X_trace :
    Ethereum.EVM.X 100001 truthValidJumps truthShortInitialState =
      .ok (.revert truthShortState19.machineState.gasAvailable truthShortReturnData) := by
  truth_continue_step truth_short_xstep_pc0
  truth_continue_step truth_short_xstep_pc2
  truth_continue_step truth_short_xstep_pc4
  truth_continue_step truth_short_xstep_pc5
  truth_continue_step truth_short_xstep_pc6
  truth_continue_step truth_short_xstep_pc7
  truth_continue_step truth_short_xstep_pc8
  truth_continue_step truth_short_xstep_pc10
  truth_continue_step truth_short_xstep_pc14
  truth_continue_step truth_short_xstep_pc15
  truth_continue_step truth_short_xstep_pc16
  truth_continue_step truth_short_xstep_pc18
  truth_continue_step truth_short_xstep_pc19
  truth_continue_step truth_short_xstep_pc20
  truth_continue_step truth_short_xstep_pc22
  apply truth_short_xstep_pc38_to_revert

theorem truth_short_Xi_trace :
    Ethereum.EVM.Ξ truthShortInitialState.createdAccounts truthShortInitialState.genesisBlockHeader
      truthShortInitialState.blocks truthShortInitialState.accountMap truthShortInitialState.σ₀
      (⟨100000⟩ : Ethereum.UInt256) truthShortInitialState.substate truthShortExecutionEnv =
        .ok (.revert truthShortState19.machineState.gasAvailable truthShortReturnData) := by
  unfold Ethereum.EVM.Ξ
  change
    (do
      let result ← Ethereum.EVM.X 100001 truthValidJumps truthShortInitialState
      match result with
      | Ethereum.ExecutionResult.success evmState' o =>
          .ok (Ethereum.ExecutionResult.success
            (evmState'.createdAccounts, evmState'.accountMap,
              evmState'.machineState.gasAvailable, evmState'.substate) o)
      | Ethereum.ExecutionResult.revert g' o => .ok (Ethereum.ExecutionResult.revert g' o)) =
      .ok (Ethereum.ExecutionResult.revert
        truthShortState19.machineState.gasAvailable truthShortReturnData)
  rw [truth_short_X_trace]
  simp [bind, Except.bind]

theorem truthTransition_signature :
    transitionSignature truthTransition = { name := "truth", paramTypes := [] } := by
  rfl

theorem truthTransition_sigStr :
    transitionSigStr truthTransition = "truth()" := by
  rfl

axiom truth_keccak_truth_signature :
    (ffi.KEC (String.toByteArray "truth()")).extract 0 4 = truthSelector

theorem truth_dispatch :
  dispatchMsg truthContract truthCallData = some truthTransition
:= by
  unfold dispatchMsg truthContract
  simp only [List.map_cons, List.map_nil, List.find?_cons, List.find?_nil]
  simp [truthTransition_sigStr, truth_keccak_truth_signature, truthCallData, Prod.map]
  native_decide

theorem truth_short_dispatch_none :
  dispatchMsg truthContract truthShortCallData = none
:= by
  unfold dispatchMsg truthContract
  simp only [List.map_cons, List.map_nil, List.find?_cons, List.find?_nil]
  simp [truthTransition_sigStr, truth_keccak_truth_signature, truthShortCallData, truthSelector,
    Prod.map]
  native_decide

theorem truth_mismatch_dispatch_none :
  dispatchMsg truthContract truthMismatchCallData = none
:= by
  unfold dispatchMsg truthContract
  simp only [List.map_cons, List.map_nil, List.find?_cons, List.find?_nil]
  simp [truthTransition_sigStr, truth_keccak_truth_signature, truthMismatchCallData, truthSelector,
    Prod.map]
  native_decide

theorem truth_byteArray_beq_false_of_ne (a b : ByteArray) (h : b ≠ a) :
    (a == b) = false := by
  cases a with
  | mk ad =>
      cases b with
      | mk bd =>
          change (ad == bd) = false
          by_cases hd : ad == bd
          · have hdata : ad = bd := by
              simpa using (beq_iff_eq.mp hd)
            exact False.elim (h (by cases hdata; rfl))
          · exact Bool.eq_false_iff.mpr hd

theorem truth_byteArray_eq_of_beq_true (a b : ByteArray) (h : (a == b) = true) :
    a = b := by
  cases a with
  | mk ad =>
      cases b with
      | mk bd =>
          apply ByteArray.ext
          change (ad == bd) = true at h
          exact beq_iff_eq.mp h

theorem truth_dispatch_of_selector (calldata : ByteArray)
    (h : calldata.extract 0 4 = truthSelector) :
    dispatchMsg truthContract calldata = some truthTransition := by
  unfold dispatchMsg truthContract
  simp only [List.map_cons, List.map_nil, List.find?_cons, List.find?_nil]
  simp [truthTransition_sigStr, truth_keccak_truth_signature, h, Prod.map]
  rfl

theorem truth_selector_of_dispatch (calldata : ByteArray)
    (h : dispatchMsg truthContract calldata = some truthTransition) :
    calldata.extract 0 4 = truthSelector := by
  unfold dispatchMsg truthContract at h
  simp only [List.map_cons, List.map_nil, List.find?_cons, List.find?_nil] at h
  simp [truthTransition_sigStr, truth_keccak_truth_signature, Prod.map] at h
  by_cases hb : (truthSelector == calldata.extract 0 4) = true
  · exact (truth_byteArray_eq_of_beq_true truthSelector (calldata.extract 0 4) hb).symm
  · simp [hb] at h

theorem truth_dispatch_none_of_selector_ne (calldata : ByteArray)
    (h : calldata.extract 0 4 ≠ truthSelector) :
    dispatchMsg truthContract calldata = none := by
  unfold dispatchMsg truthContract
  simp only [List.map_cons, List.map_nil, List.find?_cons, List.find?_nil]
  simp [truthTransition_sigStr, truth_keccak_truth_signature, Prod.map]
  rw [truth_byteArray_beq_false_of_ne truthSelector (calldata.extract 0 4) h]

theorem truth_calldata_decodes :
    decodeCalldata [] [] truthCallData = some (∅ : Store) := by
  have hlist : truthCallData.toList = [0x9e, 0x9f, 0x51, 0xd2] := by
    native_decide
  unfold decodeCalldata
  rw [hlist]
  simp [decodeCalldata.decodeArgs]

theorem truth_short_calldata_decode_fails :
    decodeCalldata [] [] truthShortCallData = none := by
  have hlist : truthShortCallData.toList = [] := by
    native_decide
  unfold decodeCalldata
  rw [hlist]
  simp

theorem truth_mismatch_calldata_decodes :
    decodeCalldata [] [] truthMismatchCallData = some (∅ : Store) := by
  have hlist : truthMismatchCallData.toList = [0xde, 0xad, 0xbe, 0xef] := by
    native_decide
  unfold decodeCalldata
  rw [hlist]
  simp [decodeCalldata.decodeArgs]

theorem truth_decode_no_args_of_calldata_length (calldata : ByteArray)
    (h : 4 ≤ calldata.toList.length) :
    decodeCalldata [] [] calldata = some (∅ : Store) := by
  unfold decodeCalldata
  simp [Nat.not_lt.mpr h, decodeCalldata.decodeArgs]

theorem truth_decode_no_args_fails_of_calldata_short (calldata : ByteArray)
    (h : calldata.toList.length < 4) :
    decodeCalldata [] [] calldata = none := by
  unfold decodeCalldata
  simp [h]

theorem truth_byteArray_toList_loop_length (bs : ByteArray) :
    ∀ n i r,
      bs.size - i = n →
      (ByteArray.toList.loop bs i r).length = r.length + n
  | 0, i, r, hn => by
      rw [ByteArray.toList.loop.eq_def]
      have hnot : ¬ i < bs.size := by omega
      simp [hnot]
  | n + 1, i, r, hn => by
      rw [ByteArray.toList.loop.eq_def]
      have hlt : i < bs.size := by omega
      simp [hlt]
      have hnstep : bs.size - (i + 1) = n := by omega
      rw [truth_byteArray_toList_loop_length bs n (i + 1) (bs.get! i :: r) hnstep]
      simp
      omega

theorem truth_byteArray_toList_length (bs : ByteArray) :
    bs.toList.length = bs.size := by
  unfold ByteArray.toList
  have h := truth_byteArray_toList_loop_length bs bs.size 0 [] (by omega)
  simpa using h

theorem truth_calldata_length_of_selector (calldata : ByteArray)
    (h : calldata.extract 0 4 = truthSelector) :
    4 ≤ calldata.toList.length := by
  have hsize : (calldata.extract 0 4).size = truthSelector.size :=
    congrArg ByteArray.size h
  have hselector_size : truthSelector.size = 4 := by
    rfl
  have hmin : min 4 calldata.size = 4 := by
    simpa [ByteArray.size_extract, hselector_size] using hsize
  have hle_size : 4 ≤ calldata.size := by
    omega
  rw [truth_byteArray_toList_length]
  exact hle_size

theorem truth_dispatch_cases (calldata : ByteArray) :
    dispatchMsg truthContract calldata = some truthTransition ∨
    dispatchMsg truthContract calldata = none := by
  by_cases h : calldata.extract 0 4 = truthSelector
  · exact Or.inl (truth_dispatch_of_selector calldata h)
  · exact Or.inr (truth_dispatch_none_of_selector_ne calldata h)

theorem truth_decode_no_args_cases (calldata : ByteArray) :
    decodeCalldata [] [] calldata = some (∅ : Store) ∨
    decodeCalldata [] [] calldata = none := by
  by_cases hshort : calldata.toList.length < 4
  · exact Or.inr (truth_decode_no_args_fails_of_calldata_short calldata hshort)
  · exact Or.inl (truth_decode_no_args_of_calldata_length calldata (Nat.le_of_not_gt hshort))

theorem truth_uint256_val_ne_zero_of_ne_zero (x : Ethereum.UInt256)
    (h : x ≠ (⟨0⟩ : Ethereum.UInt256)) :
    x.val ≠ 0 := by
  intro hval
  apply h
  cases x with
  | mk val =>
      apply congrArg Ethereum.UInt256.mk
      apply Fin.ext
      exact congrArg Fin.val hval

theorem truth_uint256_eq_zero_of_not_val_ne_zero (x : Ethereum.UInt256)
    (h : ¬ x.val ≠ 0) :
    x = (⟨0⟩ : Ethereum.UInt256) := by
  have hval : x.val = 0 := Classical.not_not.mp h
  cases x with
  | mk val =>
      change val = 0 at hval
      rw [hval]

theorem truth_uint256_beq_zero_false_of_val_ne_zero (x : Ethereum.UInt256)
    (h : x.val ≠ 0) :
    (x == (⟨0⟩ : Ethereum.UInt256)) = false := by
  cases x with
  | mk val =>
      change (val == (0 : Fin Ethereum.UInt256.size)) = false
      cases hb : (val == (0 : Fin Ethereum.UInt256.size))
      · rfl
      · exfalso
        apply h
        change val = 0
        exact beq_iff_eq.mp hb

theorem truth_uint256_isZero_of_val_ne_zero (x : Ethereum.UInt256)
    (h : x.val ≠ 0) :
    Ethereum.UInt256.isZero x = (⟨0⟩ : Ethereum.UInt256) := by
  change Ethereum.UInt256.isZero x = Ethereum.UInt256.ofNat 0
  simp [Ethereum.UInt256.isZero, Ethereum.UInt256.eq0,
    truth_uint256_beq_zero_false_of_val_ne_zero x h]

theorem truth_uint256_isZero_of_eq_zero (x : Ethereum.UInt256)
    (h : x = (⟨0⟩ : Ethereum.UInt256)) :
    Ethereum.UInt256.isZero x = (⟨1⟩ : Ethereum.UInt256) := by
  subst h
  native_decide

theorem truth_fresh_nonpayable_xstep_pc10
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode)
    (h_value : I.weiValue.val ≠ 0) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState7
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamState7
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Ghigh then .error .OutOfGass
      else .ok
        (truthParamNonpayableState8
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J
          (truthParamState7
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).executionEnv.code
          ⟨0⟩ := by
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7]
  rw [hvalid]
  rw [Ethereum.EVM.step_jumpi
    (truthParamState7
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))]
  · have hiszero := truth_uint256_isZero_of_val_ne_zero I.weiValue h_value
    have hzero : (((⟨0⟩ : Ethereum.UInt256) != (⟨0⟩ : Ethereum.UInt256)) = false) := by
      decide
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamNonpayableState8, hiszero, hzero]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      h_code, Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_nonpayable_xstep_pc11
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamNonpayableState8
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamNonpayableState8
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gbase then .error .OutOfGass
      else .ok
        (truthParamNonpayableState9
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J
          (truthParamNonpayableState8
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).executionEnv.code
          ⟨0⟩ := by
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamNonpayableState8]
  rw [hvalid]
  rw [Ethereum.EVM.step_push0
    (truthParamNonpayableState8
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamNonpayableState8, truthParamNonpayableState9]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamNonpayableState8, h_code, Ethereum.MachineState.M,
      Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_nonpayable_xstep_pc12
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamNonpayableState9
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamNonpayableState9
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gbase then .error .OutOfGass
      else .ok
        (truthParamNonpayableState10
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J
          (truthParamNonpayableState9
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).executionEnv.code
          ⟨0⟩ := by
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamNonpayableState8, truthParamNonpayableState9]
  rw [hvalid]
  rw [Ethereum.EVM.step_push0
    (truthParamNonpayableState9
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamNonpayableState8, truthParamNonpayableState9, truthParamNonpayableState10]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamNonpayableState8, truthParamNonpayableState9, h_code,
      Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_nonpayable_xstep_pc13
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamNonpayableState10
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      .ok
        (truthParamNonpayableState11
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I),
          .some (false, truthParamNonpayableReturnData
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamNonpayableState10 s).executionEnv.code ⟨0⟩ := by
    simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamNonpayableState8, truthParamNonpayableState9, truthParamNonpayableState10]
  rw [hvalid]
  rw [Ethereum.EVM.step_revert (truthParamNonpayableState10 s)]
  · simp only [truthParamNonpayableState10, truthParamNonpayableState11,
      truthParamNonpayableReturnData]
    change (if (truthParamNonpayableState10 s).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost (truthParamNonpayableState10 s) .REVERT then _
      else _) = _
    have hstack : (truthParamNonpayableState10 s).machineState.stack =
        (⟨0⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) ::
          [(truthParamNonpayableState10 s).executionEnv.weiValue] := by
      simp [truthParamNonpayableState10, truthParamNonpayableState9,
        truthParamNonpayableState8]
    have hmem : ¬ (truthParamNonpayableState10 s).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost (truthParamNonpayableState10 s) .REVERT := by
      rw [truth_revert_zero_memoryExpansionCost_top (truthParamNonpayableState10 s)
        [(truthParamNonpayableState10 s).executionEnv.weiValue] hstack]
      simp
    rw [if_neg hmem]
    have hoverflow :
        ¬ ((⟨0⟩ : Ethereum.UInt256) :: (truthParamNonpayableState9 s).machineState.stack).length -
          2 + 0 > 1024 := by
      simp [truthParamNonpayableState9, truthParamNonpayableState8]
    rw [if_neg hoverflow]
    simp [s, truthParamNonpayableState9, truthParamNonpayableState8,
      Ethereum.UInt256.toNat, Ethereum.MachineState.M]
    change Ethereum.UInt256.ofNat
        (Ethereum.UInt256.ofNat (truthParamNonpayableState9 s).machineState.activeWords.toNat).toNat =
      Ethereum.UInt256.ofNat (truthParamNonpayableState9 s).machineState.activeWords.toNat
    exact truth_uint256_ofNat_ofNat_toNat
      (truthParamNonpayableState9 s).machineState.activeWords.toNat
  · simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamNonpayableState8, truthParamNonpayableState9, truthParamNonpayableState10,
      h_code, Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_payable_xstep_pc10
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode)
    (h_value : I.weiValue = (⟨0⟩ : Ethereum.UInt256)) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState7
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamState7
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Ghigh then .error .OutOfGass
      else .ok
        (truthParamPayableState8
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J
          (truthParamState7
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).executionEnv.code
          ⟨0⟩ := by
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7]
  rw [hvalid]
  rw [Ethereum.EVM.step_jumpi
    (truthParamState7
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))]
  · have hiszero := truth_uint256_isZero_of_eq_zero I.weiValue h_value
    have hnonzero : (((⟨1⟩ : Ethereum.UInt256) != (⟨0⟩ : Ethereum.UInt256)) = true) := by
      decide
    have hcontains :
        (Ethereum.EVM.D_J I.code ⟨0⟩).contains (⟨0x0e⟩ : Ethereum.UInt256) = true := by
      rw [h_code]
      exact truth_valid_jumpdest_0e
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, hiszero, hnonzero, hcontains]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      h_code, Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_payable_xstep_pc14
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState8
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamPayableState8
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gjumpdest then .error .OutOfGass
      else .ok
        (truthParamPayableState9
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J
          (truthParamPayableState8
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).executionEnv.code
          ⟨0⟩ := by
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8]
  rw [hvalid]
  rw [Ethereum.EVM.step_jumpdest
    (truthParamPayableState8
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, h_code, Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_payable_xstep_pc15
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState9
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamPayableState9
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gbase then .error .OutOfGass
      else .ok
        (truthParamPayableState10
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J
          (truthParamPayableState9
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).executionEnv.code
          ⟨0⟩ := by
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9]
  rw [hvalid]
  rw [Ethereum.EVM.step_pop
    (truthParamPayableState9
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, h_code,
      Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_payable_xstep_pc16
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState10
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamPayableState10
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok
        (truthParamPayableState11
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J
          (truthParamPayableState10
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).executionEnv.code
          ⟨0⟩ := by
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10]
  rw [hvalid]
  rw [Ethereum.EVM.step_push1
    (truthParamPayableState10
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))
    (⟨0x04⟩ : Ethereum.UInt256)]
  · have hoverflow :
        ¬ (1024 <
          (truthParamPayableState10
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.stack.length -
            0 + 1) := by
      simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
        truthParamState4, truthParamState5, truthParamState6, truthParamState7,
        truthParamPayableState8, truthParamPayableState9, truthParamPayableState10]
    rw [if_neg hoverflow]
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      h_code, Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_payable_xstep_pc18
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState11
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamPayableState11
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gbase then .error .OutOfGass
      else .ok
        (truthParamPayableState12
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J
          (truthParamPayableState11
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).executionEnv.code
          ⟨0⟩ := by
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11]
  rw [hvalid]
  rw [Ethereum.EVM.step_calldatasize
    (truthParamPayableState11
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, h_code, Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_payable_xstep_pc19
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState12
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamPayableState12
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok
        (truthParamPayableState13
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J
          (truthParamPayableState12
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).executionEnv.code
          ⟨0⟩ := by
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12]
  rw [hvalid]
  rw [Ethereum.EVM.step_lt
    (truthParamPayableState12
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, h_code,
      Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_payable_xstep_pc20
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState13
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamPayableState13
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok
        (truthParamPayableState14
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J
          (truthParamPayableState13
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).executionEnv.code
          ⟨0⟩ := by
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13]
  rw [hvalid]
  rw [Ethereum.EVM.step_push1
    (truthParamPayableState13
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))
    (⟨0x26⟩ : Ethereum.UInt256)]
  · have hoverflow :
        ¬ (1024 <
          (truthParamPayableState13
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.stack.length -
            0 + 1) := by
      simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
        truthParamState4, truthParamState5, truthParamState6, truthParamState7,
        truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
        truthParamPayableState11, truthParamPayableState12, truthParamPayableState13]
    rw [if_neg hoverflow]
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      h_code, Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_short_xstep_pc22
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode)
    (h_lt :
      Ethereum.UInt256.lt
        (Ethereum.UInt256.ofNat I.calldata.size) (⟨0x04⟩ : Ethereum.UInt256) =
          (⟨1⟩ : Ethereum.UInt256)) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState14
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamPayableState14
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Ghigh then .error .OutOfGass
      else .ok
        (truthParamShortState15
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J
          (truthParamPayableState14
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).executionEnv.code
          ⟨0⟩ := by
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14]
  rw [hvalid]
  rw [Ethereum.EVM.step_jumpi
    (truthParamPayableState14
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))]
  · have hcontains :
        (Ethereum.EVM.D_J I.code ⟨0⟩).contains (⟨0x26⟩ : Ethereum.UInt256) = true := by
      rw [h_code]
      exact truth_valid_jumpdest_26
    have hnonzero : (((⟨1⟩ : Ethereum.UInt256) != (⟨0⟩ : Ethereum.UInt256)) = true) := by
      decide
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamShortState15, h_lt, hcontains, hnonzero]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, h_code, Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_short_xstep_pc38
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamShortState15
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamShortState15
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gjumpdest then .error .OutOfGass
      else .ok
        (truthParamShortState16
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J
          (truthParamShortState15
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).executionEnv.code
          ⟨0⟩ := by
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamShortState15]
  rw [hvalid]
  rw [Ethereum.EVM.step_jumpdest
    (truthParamShortState15
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamShortState15, truthParamShortState16]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamShortState15, h_code,
      Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_short_xstep_pc39
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamShortState16
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamShortState16
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gbase then .error .OutOfGass
      else .ok
        (truthParamShortState17
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J
          (truthParamShortState16
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).executionEnv.code
          ⟨0⟩ := by
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamShortState15, truthParamShortState16]
  rw [hvalid]
  rw [Ethereum.EVM.step_push0
    (truthParamShortState16
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamShortState15, truthParamShortState16,
      truthParamShortState17]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamShortState15, truthParamShortState16,
      h_code, Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_short_xstep_pc40
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamShortState17
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamShortState17
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gbase then .error .OutOfGass
      else .ok
        (truthParamShortState18
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J
          (truthParamShortState17
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).executionEnv.code
          ⟨0⟩ := by
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamShortState15, truthParamShortState16,
      truthParamShortState17]
  rw [hvalid]
  rw [Ethereum.EVM.step_push0
    (truthParamShortState17
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamShortState15, truthParamShortState16,
      truthParamShortState17, truthParamShortState18]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamShortState15, truthParamShortState16,
      truthParamShortState17, h_code, Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_short_xstep_pc41
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamShortState18
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      .ok
        (truthParamShortState19
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I),
          .some (false, truthParamShortReturnData
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamShortState18 s).executionEnv.code ⟨0⟩ := by
    simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamShortState15, truthParamShortState16,
      truthParamShortState17, truthParamShortState18]
  rw [hvalid]
  rw [Ethereum.EVM.step_revert (truthParamShortState18 s)]
  · simp only [truthParamShortState18, truthParamShortState19, truthParamShortReturnData]
    change (if (truthParamShortState18 s).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost (truthParamShortState18 s) .REVERT then _
      else _) = _
    have hstack : (truthParamShortState18 s).machineState.stack =
        [(⟨0⟩ : Ethereum.UInt256), (⟨0⟩ : Ethereum.UInt256)] := by
      simp [truthParamShortState18, truthParamShortState17, truthParamShortState16,
        truthParamShortState15]
    have hmem : ¬ (truthParamShortState18 s).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost (truthParamShortState18 s) .REVERT := by
      rw [truth_revert_zero_memoryExpansionCost (truthParamShortState18 s) hstack]
      simp
    rw [if_neg hmem]
    have hoverflow :
        ¬ ((⟨0⟩ : Ethereum.UInt256) :: (truthParamShortState17 s).machineState.stack).length -
          2 + 0 > 1024 := by
      simp [truthParamShortState17, truthParamShortState16, truthParamShortState15]
    rw [if_neg hoverflow]
    simp [s, truthParamShortState16, truthParamShortState15,
      Ethereum.UInt256.toNat, Ethereum.MachineState.M]
    change Ethereum.UInt256.ofNat
        (Ethereum.UInt256.ofNat (truthParamShortState17 s).machineState.activeWords.toNat).toNat =
      Ethereum.UInt256.ofNat (truthParamShortState17 s).machineState.activeWords.toNat
    exact truth_uint256_ofNat_ofNat_toNat
      (truthParamShortState17 s).machineState.activeWords.toNat
  · simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamShortState15, truthParamShortState16,
      truthParamShortState17, truthParamShortState18, h_code, Ethereum.MachineState.M,
      Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_mismatch_xstep_pc22
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode)
    (h_lt :
      Ethereum.UInt256.lt
        (Ethereum.UInt256.ofNat I.calldata.size) (⟨0x04⟩ : Ethereum.UInt256) =
          (⟨0⟩ : Ethereum.UInt256)) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState14
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamPayableState14
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Ghigh then .error .OutOfGass
      else .ok
        (truthParamMismatchState15
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J
          (truthParamPayableState14
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).executionEnv.code
          ⟨0⟩ := by
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14]
  rw [hvalid]
  rw [Ethereum.EVM.step_jumpi
    (truthParamPayableState14
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))]
  · have hzero : (((⟨0⟩ : Ethereum.UInt256) != (⟨0⟩ : Ethereum.UInt256)) = false) := by
      decide
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, h_lt, hzero]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, h_code, Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_mismatch_xstep_pc23
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState15
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamMismatchState15
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gbase then .error .OutOfGass
      else .ok
        (truthParamMismatchState16
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamMismatchState15 s).executionEnv.code ⟨0⟩ := by
    simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15]
  rw [hvalid]
  rw [Ethereum.EVM.step_push0 (truthParamMismatchState15 s)]
  · simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16]
  · simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, h_code,
      Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_mismatch_xstep_pc24
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState16
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamMismatchState16
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok
        (truthParamMismatchState17
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamMismatchState16 s).executionEnv.code ⟨0⟩ := by
    simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16]
  rw [hvalid]
  rw [Ethereum.EVM.step_calldataload (truthParamMismatchState16 s)]
  · simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchCalldataWord, Ethereum.UInt256.toNat]
  · simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      h_code, Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_mismatch_xstep_pc25
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState17
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamMismatchState17
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok
        (truthParamMismatchState18
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamMismatchState17 s).executionEnv.code ⟨0⟩ := by
    simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17]
  rw [hvalid]
  rw [Ethereum.EVM.step_push1 (truthParamMismatchState17 s) (⟨0xe0⟩ : Ethereum.UInt256)]
  · have hoverflow :
        ¬ (1024 < (truthParamMismatchState17 s).machineState.stack.length - 0 + 1) := by
      simp [truthParamMismatchState17]
    rw [if_neg hoverflow]
    simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18]
  · simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, h_code, Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_mismatch_xstep_pc27
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState18
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamMismatchState18
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok
        (truthParamMismatchState19
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamMismatchState18 s).executionEnv.code ⟨0⟩ := by
    simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18]
  rw [hvalid]
  rw [Ethereum.EVM.step_shr (truthParamMismatchState18 s)]
  · simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18, truthParamMismatchState19,
      truthParamMismatchSelectorWord]
  · simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18, h_code,
      Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_mismatch_xstep_pc28
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState19
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamMismatchState19
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok
        (truthParamMismatchState20
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamMismatchState19 s).executionEnv.code ⟨0⟩ := by
    simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18, truthParamMismatchState19]
  rw [hvalid]
  rw [Ethereum.EVM.step_dup1 (truthParamMismatchState19 s)]
  · simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18, truthParamMismatchState19,
      truthParamMismatchState20]
  · simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18, truthParamMismatchState19,
      h_code, Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_mismatch_xstep_pc29
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState20
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamMismatchState20
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok
        (truthParamMismatchState21
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamMismatchState20 s).executionEnv.code ⟨0⟩ := by
    simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18, truthParamMismatchState19,
      truthParamMismatchState20]
  rw [hvalid]
  rw [Ethereum.EVM.step_push4 (truthParamMismatchState20 s) truthExpectedSelectorWord]
  · have hoverflow :
        ¬ (1024 < (truthParamMismatchState20 s).machineState.stack.length - 0 + 1) := by
      simp [truthParamMismatchState20]
    rw [if_neg hoverflow]
    simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18, truthParamMismatchState19,
      truthParamMismatchState20, truthParamMismatchState21]
  · simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18, truthParamMismatchState19,
      truthParamMismatchState20, h_code, Ethereum.MachineState.M,
      Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_mismatch_xstep_pc34
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState21
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamMismatchState21
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok
        (truthParamMismatchState22
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamMismatchState21 s).executionEnv.code ⟨0⟩ := by
    simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18, truthParamMismatchState19,
      truthParamMismatchState20, truthParamMismatchState21]
  rw [hvalid]
  rw [Ethereum.EVM.step_eq (truthParamMismatchState21 s)]
  · simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18, truthParamMismatchState19,
      truthParamMismatchState20, truthParamMismatchState21, truthParamMismatchState22,
      truthParamMismatchSelectorEqWord]
  · simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18, truthParamMismatchState19,
      truthParamMismatchState20, truthParamMismatchState21, h_code,
      Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_mismatch_xstep_pc35
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState22
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamMismatchState22
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok
        (truthParamMismatchState23
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamMismatchState22 s).executionEnv.code ⟨0⟩ := by
    simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18, truthParamMismatchState19,
      truthParamMismatchState20, truthParamMismatchState21, truthParamMismatchState22]
  rw [hvalid]
  rw [Ethereum.EVM.step_push1 (truthParamMismatchState22 s) (⟨0x2a⟩ : Ethereum.UInt256)]
  · have hoverflow :
        ¬ (1024 < (truthParamMismatchState22 s).machineState.stack.length - 0 + 1) := by
      simp [truthParamMismatchState22]
    rw [if_neg hoverflow]
    simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18, truthParamMismatchState19,
      truthParamMismatchState20, truthParamMismatchState21, truthParamMismatchState22,
      truthParamMismatchState23]
  · simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18, truthParamMismatchState19,
      truthParamMismatchState20, truthParamMismatchState21, truthParamMismatchState22,
      h_code, Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_mismatch_xstep_pc38
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState24
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamMismatchState24
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gjumpdest then .error .OutOfGass
      else .ok
        (truthParamMismatchState25
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J
          (truthParamMismatchState24
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).executionEnv.code
          ⟨0⟩ := by
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18, truthParamMismatchState19,
      truthParamMismatchState20, truthParamMismatchState21, truthParamMismatchState22,
      truthParamMismatchState23, truthParamMismatchState24]
  rw [hvalid]
  rw [Ethereum.EVM.step_jumpdest
    (truthParamMismatchState24
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18, truthParamMismatchState19,
      truthParamMismatchState20, truthParamMismatchState21, truthParamMismatchState22,
      truthParamMismatchState23, truthParamMismatchState24, truthParamMismatchState25]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18, truthParamMismatchState19,
      truthParamMismatchState20, truthParamMismatchState21, truthParamMismatchState22,
      truthParamMismatchState23, truthParamMismatchState24, h_code,
      Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_mismatch_xstep_pc39
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState25
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamMismatchState25
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gbase then .error .OutOfGass
      else .ok
        (truthParamMismatchState26
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J
          (truthParamMismatchState25
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).executionEnv.code
          ⟨0⟩ := by
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18, truthParamMismatchState19,
      truthParamMismatchState20, truthParamMismatchState21, truthParamMismatchState22,
      truthParamMismatchState23, truthParamMismatchState24, truthParamMismatchState25]
  rw [hvalid]
  rw [Ethereum.EVM.step_push0
    (truthParamMismatchState25
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18, truthParamMismatchState19,
      truthParamMismatchState20, truthParamMismatchState21, truthParamMismatchState22,
      truthParamMismatchState23, truthParamMismatchState24, truthParamMismatchState25,
      truthParamMismatchState26]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18, truthParamMismatchState19,
      truthParamMismatchState20, truthParamMismatchState21, truthParamMismatchState22,
      truthParamMismatchState23, truthParamMismatchState24, truthParamMismatchState25,
      h_code, Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_mismatch_xstep_pc40
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState26
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamMismatchState26
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gbase then .error .OutOfGass
      else .ok
        (truthParamMismatchState27
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J
          (truthParamMismatchState26
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).executionEnv.code
          ⟨0⟩ := by
    simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18, truthParamMismatchState19,
      truthParamMismatchState20, truthParamMismatchState21, truthParamMismatchState22,
      truthParamMismatchState23, truthParamMismatchState24, truthParamMismatchState25,
      truthParamMismatchState26]
  rw [hvalid]
  rw [Ethereum.EVM.step_push0
    (truthParamMismatchState26
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18, truthParamMismatchState19,
      truthParamMismatchState20, truthParamMismatchState21, truthParamMismatchState22,
      truthParamMismatchState23, truthParamMismatchState24, truthParamMismatchState25,
      truthParamMismatchState26, truthParamMismatchState27]
  · simp [truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18, truthParamMismatchState19,
      truthParamMismatchState20, truthParamMismatchState21, truthParamMismatchState22,
      truthParamMismatchState23, truthParamMismatchState24, truthParamMismatchState25,
      truthParamMismatchState26, h_code, Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_mismatch_xstep_pc41
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState27
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      .ok
        (truthParamMismatchState28
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I),
          .some (false, truthParamMismatchReturnData
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamMismatchState27 s).executionEnv.code ⟨0⟩ := by
    simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18, truthParamMismatchState19,
      truthParamMismatchState20, truthParamMismatchState21, truthParamMismatchState22,
      truthParamMismatchState23, truthParamMismatchState24, truthParamMismatchState25,
      truthParamMismatchState26, truthParamMismatchState27]
  rw [hvalid]
  rw [Ethereum.EVM.step_revert (truthParamMismatchState27 s)]
  · simp only [truthParamMismatchState27, truthParamMismatchState28,
      truthParamMismatchReturnData]
    change (if (truthParamMismatchState27 s).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost (truthParamMismatchState27 s) .REVERT then _
      else _) = _
    have hstack : (truthParamMismatchState27 s).machineState.stack =
        (⟨0⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) ::
          [truthParamMismatchSelectorWord s] := by
      simp [truthParamMismatchState27, truthParamMismatchState26,
        truthParamMismatchState25, truthParamMismatchState24]
    have hmem : ¬ (truthParamMismatchState27 s).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost (truthParamMismatchState27 s) .REVERT := by
      rw [truth_revert_zero_memoryExpansionCost_top (truthParamMismatchState27 s)
        [truthParamMismatchSelectorWord s] hstack]
      simp
    rw [if_neg hmem]
    have hoverflow :
        ¬ ((⟨0⟩ : Ethereum.UInt256) :: (truthParamMismatchState26 s).machineState.stack).length -
          2 + 0 > 1024 := by
      simp [truthParamMismatchState26, truthParamMismatchState25,
        truthParamMismatchState24]
    rw [if_neg hoverflow]
    simp [s, truthParamMismatchState26, truthParamMismatchState25,
      truthParamMismatchState24, Ethereum.UInt256.toNat, Ethereum.MachineState.M]
    change Ethereum.UInt256.ofNat
        (Ethereum.UInt256.ofNat (truthParamMismatchState24 s).machineState.activeWords.toNat).toNat =
      Ethereum.UInt256.ofNat (truthParamMismatchState24 s).machineState.activeWords.toNat
    exact truth_uint256_ofNat_ofNat_toNat
      (truthParamMismatchState24 s).machineState.activeWords.toNat
  · simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18, truthParamMismatchState19,
      truthParamMismatchState20, truthParamMismatchState21, truthParamMismatchState22,
      truthParamMismatchState23, truthParamMismatchState24, truthParamMismatchState25,
      truthParamMismatchState26, truthParamMismatchState27, h_code,
      Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_mismatch_xstep_pc37
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode)
    (h_selector_eq :
      truthParamMismatchSelectorEqWord
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
          (⟨0⟩ : Ethereum.UInt256)) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState23
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamMismatchState23
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Ghigh then .error .OutOfGass
      else .ok
        (truthParamMismatchState24
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamMismatchState23 s).executionEnv.code ⟨0⟩ := by
    simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18, truthParamMismatchState19,
      truthParamMismatchState20, truthParamMismatchState21, truthParamMismatchState22,
      truthParamMismatchState23]
  rw [hvalid]
  rw [Ethereum.EVM.step_jumpi (truthParamMismatchState23 s)]
  · have hzero : (((⟨0⟩ : Ethereum.UInt256) != (⟨0⟩ : Ethereum.UInt256)) = false) := by
      decide
    simp [s, truthParamMismatchState23, truthParamMismatchState22,
      truthParamMismatchState24, h_selector_eq, hzero]
  · simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18, truthParamMismatchState19,
      truthParamMismatchState20, truthParamMismatchState21, truthParamMismatchState22,
      truthParamMismatchState23, h_code, Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_success_xstep_pc37
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode)
    (h_selector_eq :
      truthParamMismatchSelectorEqWord
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
          (⟨1⟩ : Ethereum.UInt256)) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState23
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamMismatchState23
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Ghigh then .error .OutOfGass
      else .ok
        (truthParamSuccessState24
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamMismatchState23 s).executionEnv.code ⟨0⟩ := by
    simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18, truthParamMismatchState19,
      truthParamMismatchState20, truthParamMismatchState21, truthParamMismatchState22,
      truthParamMismatchState23]
  rw [hvalid]
  rw [Ethereum.EVM.step_jumpi (truthParamMismatchState23 s)]
  · have hone : (((⟨1⟩ : Ethereum.UInt256) != (⟨0⟩ : Ethereum.UInt256)) = true) := by
      decide
    have hcontains :
        (Ethereum.EVM.D_J (truthParamMismatchState21 s).executionEnv.code ⟨0⟩).contains
          (⟨0x2a⟩ : Ethereum.UInt256) = true := by
      have hcode : (truthParamMismatchState21 s).executionEnv.code = truthRuntimeBytecode := by
        simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
          truthParamState4, truthParamState5, truthParamState6, truthParamState7,
          truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
          truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
          truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
          truthParamMismatchState17, truthParamMismatchState18, truthParamMismatchState19,
          truthParamMismatchState20, truthParamMismatchState21, h_code]
      rw [hcode]
      exact truth_valid_jumpdest_2a
    simp [s, truthParamMismatchState23, truthParamMismatchState22,
      truthParamSuccessState24, h_selector_eq, hone, hcontains]
  · simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16,
      truthParamMismatchState17, truthParamMismatchState18, truthParamMismatchState19,
      truthParamMismatchState20, truthParamMismatchState21, truthParamMismatchState22,
      truthParamMismatchState23, h_code, Ethereum.MachineState.M, Ethereum.UInt256.toNat]
    native_decide

theorem truth_fresh_success_xstep_pc42
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamSuccessState24
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamSuccessState24
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gjumpdest then .error .OutOfGass
      else .ok
        (truthParamSuccessState25
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamSuccessState24 s).executionEnv.code ⟨0⟩ := by
    rw [truthParamSuccessState24_code]
    simp [s, truthFreshState]
  rw [hvalid]
  rw [Ethereum.EVM.step_jumpdest (truthParamSuccessState24 s)]
  · simp [s, truthParamSuccessState25, truthParamSuccessState24]
  · rw [truthParamSuccessState24_code]
    simp [s, truthFreshState, h_code]
    exact truth_decode_pc42

theorem truth_fresh_success_xstep_pc43
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamSuccessState25
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamSuccessState25
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok
        (truthParamSuccessState26
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamSuccessState25 s).executionEnv.code ⟨0⟩ := by
    rw [truthParamSuccessState25_code]
    simp [s, truthFreshState]
  rw [hvalid]
  rw [Ethereum.EVM.step_push1 (truthParamSuccessState25 s) (⟨0x30⟩ : Ethereum.UInt256)]
  · have hoverflow :
        ¬ (1024 < (truthParamSuccessState25 s).machineState.stack.length - 0 + 1) := by
      simp [truthParamSuccessState25, truthParamSuccessState24]
    rw [if_neg hoverflow]
    simp [s, truthParamSuccessState26, truthParamSuccessState25]
  · rw [truthParamSuccessState25_code]
    simp [s, truthFreshState, h_code]
    exact truth_decode_pc43

theorem truth_fresh_success_xstep_pc45
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamSuccessState26
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamSuccessState26
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok
        (truthParamSuccessState27
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamSuccessState26 s).executionEnv.code ⟨0⟩ := by
    rw [truthParamSuccessState26_code]
    simp [s, truthFreshState]
  rw [hvalid]
  rw [Ethereum.EVM.step_push1 (truthParamSuccessState26 s) (⟨0x44⟩ : Ethereum.UInt256)]
  · have hoverflow :
        ¬ (1024 < (truthParamSuccessState26 s).machineState.stack.length - 0 + 1) := by
      simp [truthParamSuccessState26, truthParamSuccessState25, truthParamSuccessState24]
    rw [if_neg hoverflow]
    simp [s, truthParamSuccessState27, truthParamSuccessState26]
  · rw [truthParamSuccessState26_code]
    simp [s, truthFreshState, h_code]
    exact truth_decode_pc45

set_option maxHeartbeats 2000000 in
theorem truth_fresh_success_xstep_pc47
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamSuccessState27
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamSuccessState27
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gmid then .error .OutOfGass
      else .ok
        (truthParamSuccessState28
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamSuccessState27 s).executionEnv.code ⟨0⟩ := by
    rw [truthParamSuccessState27_code]
    simp [s, truthFreshState]
  rw [hvalid]
  rw [Ethereum.EVM.step_jump (truthParamSuccessState27 s)]
  · simp only [truthParamSuccessState27, truthParamSuccessState26]
    have hcontains :
        (Ethereum.EVM.D_J (truthParamSuccessState25 s).executionEnv.code ⟨0⟩).contains
          (⟨0x44⟩ : Ethereum.UInt256) = true := by
      rw [truthParamSuccessState25_code]
      simp [s, truthFreshState, h_code]
      exact truth_valid_jumpdest_44
    rw [hcontains]
    simp [s, truthParamSuccessState28, truthParamSuccessState27, truthParamSuccessState26,
      truthParamSuccessState25, truthParamSuccessState24]
  · rw [truthParamSuccessState27_code]
    simp [s, truthFreshState, h_code]
    exact truth_decode_pc47

theorem truth_fresh_success_xstep_pc68
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamSuccessState28
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamSuccessState28
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gjumpdest then .error .OutOfGass
      else .ok
        (truthParamSuccessState29
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamSuccessState28 s).executionEnv.code ⟨0⟩ := by
    rw [truthParamSuccessState28_code]
    simp [s, truthFreshState]
  rw [hvalid]
  rw [Ethereum.EVM.step_jumpdest (truthParamSuccessState28 s)]
  · simp [s, truthParamSuccessState29, truthParamSuccessState28]
  · rw [truthParamSuccessState28_code]
    simp [s, truthFreshState, h_code]
    exact truth_decode_pc68

theorem truth_fresh_success_xstep_pc69
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamSuccessState29
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamSuccessState29
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gbase then .error .OutOfGass
      else .ok
        (truthParamSuccessState30
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamSuccessState29 s).executionEnv.code ⟨0⟩ := by
    rw [truthParamSuccessState29_code]
    simp [s, truthFreshState]
  rw [hvalid]
  rw [Ethereum.EVM.step_push0 (truthParamSuccessState29 s)]
  · have hoverflow :
        ¬ (1024 < (truthParamSuccessState29 s).machineState.stack.length - 0 + 1) := by
      simp [truthParamSuccessState29, truthParamSuccessState28]
    rw [if_neg hoverflow]
    simp [s, truthParamSuccessState30, truthParamSuccessState29]
  · rw [truthParamSuccessState29_code]
    simp [s, truthFreshState, h_code]
    exact truth_decode_pc69

theorem truth_fresh_success_xstep_pc70
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamSuccessState30
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamSuccessState30
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok
        (truthParamSuccessState31
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamSuccessState30 s).executionEnv.code ⟨0⟩ := by
    rw [truthParamSuccessState30_code]
    simp [s, truthFreshState]
  rw [hvalid]
  rw [Ethereum.EVM.step_push1 (truthParamSuccessState30 s) (⟨1⟩ : Ethereum.UInt256)]
  · have hoverflow :
        ¬ (1024 < (truthParamSuccessState30 s).machineState.stack.length - 0 + 1) := by
      simp [truthParamSuccessState30, truthParamSuccessState29, truthParamSuccessState28]
    rw [if_neg hoverflow]
    simp [s, truthParamSuccessState31, truthParamSuccessState30]
  · rw [truthParamSuccessState30_code]
    simp [s, truthFreshState, h_code]
    exact truth_decode_pc70

set_option maxHeartbeats 2000000 in
theorem truth_fresh_success_xstep_pc72
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamSuccessState31
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamSuccessState31
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok
        (truthParamSuccessState32
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamSuccessState31 s).executionEnv.code ⟨0⟩ := by
    rw [truthParamSuccessState31_code]
    simp [s, truthFreshState]
  rw [hvalid]
  rw [Ethereum.EVM.step_swap1 (truthParamSuccessState31 s)]
  · simp [s, truthParamSuccessState32, truthParamSuccessState31, truthParamSuccessState30,
      truthParamSuccessState29, truthParamSuccessState28]
  · rw [truthParamSuccessState31_code]
    simp [s, truthFreshState, h_code]
    exact truth_decode_pc72

set_option maxHeartbeats 2000000 in
theorem truth_fresh_success_xstep_pc73
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamSuccessState32
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamSuccessState32
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gbase then .error .OutOfGass
      else .ok
        (truthParamSuccessState33
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamSuccessState32 s).executionEnv.code ⟨0⟩ := by
    rw [truthParamSuccessState32_code]
    simp [s, truthFreshState]
  rw [hvalid]
  rw [Ethereum.EVM.step_pop (truthParamSuccessState32 s)]
  · simp [s, truthParamSuccessState33, truthParamSuccessState32]
  · rw [truthParamSuccessState32_code]
    simp [s, truthFreshState, h_code]
    exact truth_decode_pc73

set_option maxHeartbeats 2000000 in
theorem truth_fresh_success_xstep_pc74
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamSuccessState33
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamSuccessState33
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gverylow then .error .OutOfGass
      else .ok
        (truthParamSuccessState34
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamSuccessState33 s).executionEnv.code ⟨0⟩ := by
    rw [truthParamSuccessState33_code]
    simp [s, truthFreshState]
  rw [hvalid]
  rw [Ethereum.EVM.step_swap1 (truthParamSuccessState33 s)]
  · simp [s, truthParamSuccessState34, truthParamSuccessState33]
  · rw [truthParamSuccessState33_code]
    simp [s, truthFreshState, h_code]
    exact truth_decode_pc74

set_option maxHeartbeats 2000000 in
theorem truth_fresh_success_xstep_pc75
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode) :
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamSuccessState34
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      if (truthParamSuccessState34
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
            GasConstants.Gmid then .error .OutOfGass
      else .ok
        (truthParamSuccessState35
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hvalid :
      Ethereum.EVM.D_J I.code ⟨0⟩ =
        Ethereum.EVM.D_J (truthParamSuccessState34 s).executionEnv.code ⟨0⟩ := by
    rw [truthParamSuccessState34_code]
    simp [s, truthFreshState]
  rw [hvalid]
  rw [Ethereum.EVM.step_jump (truthParamSuccessState34 s)]
  · simp only [truthParamSuccessState34, truthParamSuccessState33]
    have hcontains :
        (Ethereum.EVM.D_J (truthParamSuccessState32 s).executionEnv.code ⟨0⟩).contains
          (⟨0x30⟩ : Ethereum.UInt256) = true := by
      rw [truthParamSuccessState32_code]
      simp [s, truthFreshState, h_code]
      exact truth_valid_jumpdest_30
    rw [hcontains]
    simp [s, truthParamSuccessState35, truthParamSuccessState34, truthParamSuccessState33,
      truthParamSuccessState32]
  · rw [truthParamSuccessState34_code]
    simp [s, truthFreshState, h_code]
    exact truth_decode_pc75

theorem truth_uint256_lt_ofNat_four_of_lt_four (n : Nat) (h : n < 4) :
    Ethereum.UInt256.lt (Ethereum.UInt256.ofNat n) (⟨0x04⟩ : Ethereum.UInt256) =
      (⟨1⟩ : Ethereum.UInt256) := by
  rcases n with _ | n
  · native_decide
  rcases n with _ | n
  · native_decide
  rcases n with _ | n
  · native_decide
  rcases n with _ | n
  · native_decide
  · omega

theorem truth_calldata_size_lt_word_of_short (calldata : ByteArray)
    (h : calldata.toList.length < 4) :
    Ethereum.UInt256.lt (Ethereum.UInt256.ofNat calldata.size) (⟨0x04⟩ : Ethereum.UInt256) =
      (⟨1⟩ : Ethereum.UInt256) := by
  apply truth_uint256_lt_ofNat_four_of_lt_four
  rw [← truth_byteArray_toList_length]
  exact h

theorem truth_uint256_ofNat_toNat_of_lt_size (n : Nat)
    (h : n < Ethereum.UInt256.size) :
    (Ethereum.UInt256.ofNat n).toNat = n := by
  unfold Ethereum.UInt256.toNat Ethereum.UInt256.ofNat
  simp [Id.run, Nat.mod_eq_of_lt h]

theorem truth_uint256_lt_ofNat_four_of_not_lt_four_of_lt_size (n : Nat)
    (h4 : ¬ n < 4)
    (hsize : n < Ethereum.UInt256.size) :
    Ethereum.UInt256.lt (Ethereum.UInt256.ofNat n) (⟨0x04⟩ : Ethereum.UInt256) =
      (⟨0⟩ : Ethereum.UInt256) := by
  have hof := truth_uint256_ofNat_toNat_of_lt_size n hsize
  have hnot :
      ¬ Ethereum.UInt256.ofNat n < (⟨0x04⟩ : Ethereum.UInt256) := by
    intro hlt
    have hnat := Ethereum.EVM.UInt256_lt_to_Nat
      (Ethereum.UInt256.ofNat n) (⟨0x04⟩ : Ethereum.UInt256) hlt
    have hnat' : n < 4 := by
      rw [hof] at hnat
      norm_num [Ethereum.UInt256.toNat, Ethereum.UInt256.size] at hnat
      exact hnat
    exact h4 hnat'
  unfold Ethereum.UInt256.lt Ethereum.UInt256.fromBool
  simp [hnot, Bool.toUInt256_false, Ethereum.EVM.UInt256_ofNat_0]

theorem truth_calldata_size_word_of_not_short_of_uint256_bound
    (calldata : ByteArray)
    (h_len : 4 ≤ calldata.toList.length)
    (h_bound : calldata.size < Ethereum.UInt256.size) :
    Ethereum.UInt256.lt (Ethereum.UInt256.ofNat calldata.size) (⟨0x04⟩ : Ethereum.UInt256) =
      (⟨0⟩ : Ethereum.UInt256) := by
  apply truth_uint256_lt_ofNat_four_of_not_lt_four_of_lt_size
  · rw [← truth_byteArray_toList_length]
    exact Nat.not_lt.mpr h_len
  · exact h_bound

theorem truth_fresh_short_X_trace_of_xsteps
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (f : Nat)
    (h0 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
          .ok (truthParamState1
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h2 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState1
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h4 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState2
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState3
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h5 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState3
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState4
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h6 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState4
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState5
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h7 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState5
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState6
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h8 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState6
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState7
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h10 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState7
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState8
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h14 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState8
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState9
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h15 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState9
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState10
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h16 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState10
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState11
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h18 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState11
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState12
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h19 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState12
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState13
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h20 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState13
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState14
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h22 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState14
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamShortState15
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h38 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamShortState15
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamShortState16
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h39 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamShortState16
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamShortState17
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h40 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamShortState17
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamShortState18
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h41 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamShortState18
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok
            (truthParamShortState19
              (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I),
              .some (false, truthParamShortReturnData
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)))) :
    Ethereum.EVM.X (f + 19) (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
      .ok (.revert
        (truthParamShortState19
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable
        (truthParamShortReturnData
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))) := by
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h0
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h2
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h4
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h5
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h6
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h7
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h8
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h10
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h14
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h15
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h16
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h18
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h19
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h20
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h22
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h38
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h39
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h40
  apply Ethereum.EVM.Xstep_X_X_halt_revert
  exact h41

theorem truth_fresh_mismatch_revert_tail_X_trace_of_xsteps
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (f : Nat)
    (h38 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState24
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState25
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h39 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState25
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState26
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h40 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState26
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState27
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h41 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState27
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok
            (truthParamMismatchState28
              (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I),
              .some (false, truthParamMismatchReturnData
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)))) :
    Ethereum.EVM.X (f + 4) (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState24
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      .ok (.revert
        (truthParamMismatchState28
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable
        (truthParamMismatchReturnData
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))) := by
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h38
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h39
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h40
  apply Ethereum.EVM.Xstep_X_X_halt_revert
  exact h41

theorem truth_fresh_mismatch_X_trace_of_xsteps
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (f : Nat)
    (h0 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
          .ok (truthParamState1
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h2 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState1
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h4 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState2
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState3
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h5 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState3
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState4
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h6 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState4
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState5
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h7 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState5
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState6
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h8 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState6
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState7
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h10 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState7
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState8
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h14 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState8
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState9
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h15 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState9
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState10
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h16 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState10
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState11
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h18 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState11
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState12
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h19 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState12
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState13
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h20 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState13
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState14
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h22 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState14
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState15
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h23 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState15
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState16
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h24 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState16
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState17
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h25 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState17
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState18
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h27 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState18
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState19
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h28 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState19
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState20
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h29 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState20
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState21
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h34 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState21
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState22
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h35 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState22
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState23
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h37 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState23
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState24
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h38 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState24
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState25
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h39 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState25
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState26
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h40 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState26
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState27
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h41 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState27
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok
            (truthParamMismatchState28
              (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I),
              .some (false, truthParamMismatchReturnData
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)))) :
    Ethereum.EVM.X (f + 28) (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
      .ok (.revert
        (truthParamMismatchState28
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable
        (truthParamMismatchReturnData
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))) := by
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h0
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h2
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h4
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h5
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h6
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h7
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h8
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h10
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h14
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h15
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h16
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h18
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h19
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h20
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h22
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h23
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h24
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h25
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h27
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h28
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h29
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h34
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h35
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h37
  exact truth_fresh_mismatch_revert_tail_X_trace_of_xsteps createdAccounts
    genesisBlockHeader blocks σ σ₀ g A I f h38 h39 h40 h41

theorem truth_fresh_mismatch_Xi_revert_of_no_oog
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode)
    (h_value : I.weiValue = (⟨0⟩ : Ethereum.UInt256))
    (h_fuel : 27 ≤ g.toNat)
    (h_size_word :
      Ethereum.UInt256.lt
        (Ethereum.UInt256.ofNat I.calldata.size) (⟨0x04⟩ : Ethereum.UInt256) =
          (⟨0⟩ : Ethereum.UInt256))
    (h_selector_eq :
      truthParamMismatchSelectorEqWord
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
          (⟨0⟩ : Ethereum.UInt256))
    (h0 :
      ¬ g.toNat < GasConstants.Gverylow)
    (h2 :
      ¬ (truthParamState1
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h4mem :
      ¬ (truthParamState2
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost
          (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)
    (h4gas :
      ¬ ((truthParamState2
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
          Ethereum.UInt256.ofNat
            (Ethereum.EVM.memoryExpansionCost
              (truthParamState2
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)).toNat <
        GasConstants.Gverylow)
    (h5 :
      ¬ (truthParamState3
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase)
    (h6 :
      ¬ (truthParamState4
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h7 :
      ¬ (truthParamState5
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h8 :
      ¬ (truthParamState6
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h10 :
      ¬ (truthParamState7
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Ghigh)
    (h14 :
      ¬ (truthParamPayableState8
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gjumpdest)
    (h15 :
      ¬ (truthParamPayableState9
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase)
    (h16 :
      ¬ (truthParamPayableState10
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h18 :
      ¬ (truthParamPayableState11
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase)
    (h19 :
      ¬ (truthParamPayableState12
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h20 :
      ¬ (truthParamPayableState13
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h22 :
      ¬ (truthParamPayableState14
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Ghigh)
    (h23 :
      ¬ (truthParamMismatchState15
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase)
    (h24 :
      ¬ (truthParamMismatchState16
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h25 :
      ¬ (truthParamMismatchState17
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h27 :
      ¬ (truthParamMismatchState18
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h28 :
      ¬ (truthParamMismatchState19
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h29 :
      ¬ (truthParamMismatchState20
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h34 :
      ¬ (truthParamMismatchState21
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h35 :
      ¬ (truthParamMismatchState22
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h37 :
      ¬ (truthParamMismatchState23
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Ghigh)
    (h38 :
      ¬ (truthParamMismatchState24
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gjumpdest)
    (h39 :
      ¬ (truthParamMismatchState25
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase)
    (h40 :
      ¬ (truthParamMismatchState26
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert
        (truthParamMismatchState28
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable
        (truthParamMismatchReturnData
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))) := by
  apply truth_Xi_revert_of_X_fresh_revert
  have h0step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
          .ok (truthParamState1
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc0 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h0]
  have h2step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState1
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc2 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h2]
  have h4step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState2
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState3
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc4 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h4mem, if_neg h4gas]
  have h5step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState3
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState4
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc5 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h5]
  have h6step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState4
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState5
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc6 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h6]
  have h7step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState5
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState6
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc7 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h7]
  have h8step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState6
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState7
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc8 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h8]
  have h10step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState7
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState8
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_payable_xstep_pc10 createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      h_code h_value]
    rw [if_neg h10]
  have h14step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState8
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState9
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_payable_xstep_pc14 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h14]
  have h15step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState9
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState10
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_payable_xstep_pc15 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h15]
  have h16step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState10
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState11
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_payable_xstep_pc16 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h16]
  have h18step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState11
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState12
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_payable_xstep_pc18 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h18]
  have h19step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState12
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState13
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_payable_xstep_pc19 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h19]
  have h20step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState13
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState14
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_payable_xstep_pc20 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h20]
  have h22step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState14
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState15
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_mismatch_xstep_pc22 createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      h_code h_size_word]
    rw [if_neg h22]
  have h23step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState15
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState16
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_mismatch_xstep_pc23 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h23]
  have h24step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState16
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState17
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_mismatch_xstep_pc24 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h24]
  have h25step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState17
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState18
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_mismatch_xstep_pc25 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h25]
  have h27step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState18
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState19
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_mismatch_xstep_pc27 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h27]
  have h28step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState19
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState20
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_mismatch_xstep_pc28 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h28]
  have h29step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState20
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState21
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_mismatch_xstep_pc29 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h29]
  have h34step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState21
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState22
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_mismatch_xstep_pc34 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h34]
  have h35step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState22
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState23
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_mismatch_xstep_pc35 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h35]
  have h37step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState23
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState24
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_mismatch_xstep_pc37 createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      h_code h_selector_eq]
    rw [if_neg h37]
  have h38step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState24
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState25
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_mismatch_xstep_pc38 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h38]
  have h39step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState25
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState26
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_mismatch_xstep_pc39 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h39]
  have h40step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState26
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState27
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_mismatch_xstep_pc40 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h40]
  have h41step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState27
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok
            (truthParamMismatchState28
              (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I),
              .some (false, truthParamMismatchReturnData
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))) := by
    exact truth_fresh_mismatch_xstep_pc41 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code
  have hfuel :
      g.toNat + 1 = (g.toNat - 27) + 28 := by
    omega
  rw [hfuel]
  exact truth_fresh_mismatch_X_trace_of_xsteps createdAccounts genesisBlockHeader blocks
    σ σ₀ g A I (g.toNat - 27) h0step h2step h4step h5step h6step h7step
    h8step h10step h14step h15step h16step h18step h19step h20step h22step
    h23step h24step h25step h27step h28step h29step h34step h35step h37step
    h38step h39step h40step h41step

theorem truth_fresh_nonpayable_X_trace_of_xsteps
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (f : Nat)
    (h0 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
          .ok (truthParamState1
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h2 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState1
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h4 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState2
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState3
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h5 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState3
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState4
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h6 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState4
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState5
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h7 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState5
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState6
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h8 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState6
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState7
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h10 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState7
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamNonpayableState8
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h11 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamNonpayableState8
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamNonpayableState9
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h12 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamNonpayableState9
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamNonpayableState10
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none))
    (h13 :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamNonpayableState10
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok
            (truthParamNonpayableState11
              (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I),
              .some (false, truthParamNonpayableReturnData
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)))) :
    Ethereum.EVM.X (f + 11) (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
      .ok (.revert
        (truthParamNonpayableState11
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable
        (truthParamNonpayableReturnData
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))) := by
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h0
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h2
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h4
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h5
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h6
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h7
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h8
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h10
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h11
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h12
  apply Ethereum.EVM.Xstep_X_X_halt_revert
  exact h13

theorem truth_fresh_short_Xi_revert_of_no_oog
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode)
    (h_value : I.weiValue = (⟨0⟩ : Ethereum.UInt256))
    (h_short : I.calldata.toList.length < 4)
    (h_fuel : 18 ≤ g.toNat)
    (h0 :
      ¬ g.toNat < GasConstants.Gverylow)
    (h2 :
      ¬ (truthParamState1
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h4mem :
      ¬ (truthParamState2
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost
          (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)
    (h4gas :
      ¬ ((truthParamState2
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
          Ethereum.UInt256.ofNat
            (Ethereum.EVM.memoryExpansionCost
              (truthParamState2
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)).toNat <
        GasConstants.Gverylow)
    (h5 :
      ¬ (truthParamState3
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase)
    (h6 :
      ¬ (truthParamState4
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h7 :
      ¬ (truthParamState5
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h8 :
      ¬ (truthParamState6
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h10 :
      ¬ (truthParamState7
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Ghigh)
    (h14 :
      ¬ (truthParamPayableState8
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gjumpdest)
    (h15 :
      ¬ (truthParamPayableState9
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase)
    (h16 :
      ¬ (truthParamPayableState10
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h18 :
      ¬ (truthParamPayableState11
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase)
    (h19 :
      ¬ (truthParamPayableState12
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h20 :
      ¬ (truthParamPayableState13
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h22 :
      ¬ (truthParamPayableState14
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Ghigh)
    (h38 :
      ¬ (truthParamShortState15
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gjumpdest)
    (h39 :
      ¬ (truthParamShortState16
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase)
    (h40 :
      ¬ (truthParamShortState17
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert
        (truthParamShortState19
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable
        (truthParamShortReturnData
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))) := by
  apply truth_Xi_revert_of_X_fresh_revert
  have h0step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
          .ok (truthParamState1
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc0 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h0]
  have h2step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState1
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc2 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h2]
  have h4step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState2
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState3
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc4 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h4mem, if_neg h4gas]
  have h5step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState3
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState4
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc5 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h5]
  have h6step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState4
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState5
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc6 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h6]
  have h7step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState5
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState6
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc7 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h7]
  have h8step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState6
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState7
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc8 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h8]
  have h10step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState7
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState8
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_payable_xstep_pc10 createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      h_code h_value]
    rw [if_neg h10]
  have h14step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState8
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState9
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_payable_xstep_pc14 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h14]
  have h15step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState9
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState10
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_payable_xstep_pc15 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h15]
  have h16step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState10
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState11
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_payable_xstep_pc16 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h16]
  have h18step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState11
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState12
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_payable_xstep_pc18 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h18]
  have h19step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState12
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState13
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_payable_xstep_pc19 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h19]
  have h20step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState13
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState14
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_payable_xstep_pc20 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h20]
  have h22step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState14
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamShortState15
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_short_xstep_pc22 createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      h_code (truth_calldata_size_lt_word_of_short I.calldata h_short)]
    rw [if_neg h22]
  have h38step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamShortState15
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamShortState16
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_short_xstep_pc38 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h38]
  have h39step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamShortState16
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamShortState17
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_short_xstep_pc39 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h39]
  have h40step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamShortState17
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamShortState18
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_short_xstep_pc40 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h40]
  have h41step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamShortState18
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok
            (truthParamShortState19
              (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I),
              .some (false, truthParamShortReturnData
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))) := by
    exact truth_fresh_short_xstep_pc41 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code
  have hfuel :
      g.toNat + 1 = (g.toNat - 18) + 19 := by
    omega
  rw [hfuel]
  exact truth_fresh_short_X_trace_of_xsteps createdAccounts genesisBlockHeader blocks σ σ₀
    g A I (g.toNat - 18) h0step h2step h4step h5step h6step h7step h8step
    h10step h14step h15step h16step h18step h19step h20step h22step h38step
    h39step h40step h41step

theorem truth_fresh_nonpayable_Xi_revert_of_no_oog
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode)
    (h_value : I.weiValue.val ≠ 0)
    (h_fuel : 10 ≤ g.toNat)
    (h0 :
      ¬ g.toNat < GasConstants.Gverylow)
    (h2 :
      ¬ (truthParamState1
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h4mem :
      ¬ (truthParamState2
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost
          (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)
    (h4gas :
      ¬ ((truthParamState2
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
          Ethereum.UInt256.ofNat
            (Ethereum.EVM.memoryExpansionCost
              (truthParamState2
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)).toNat <
        GasConstants.Gverylow)
    (h5 :
      ¬ (truthParamState3
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase)
    (h6 :
      ¬ (truthParamState4
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h7 :
      ¬ (truthParamState5
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h8 :
      ¬ (truthParamState6
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h10 :
      ¬ (truthParamState7
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Ghigh)
    (h11 :
      ¬ (truthParamNonpayableState8
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase)
    (h12 :
      ¬ (truthParamNonpayableState9
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert
        (truthParamNonpayableState11
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable
        (truthParamNonpayableReturnData
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))) := by
  apply truth_Xi_revert_of_X_fresh_revert
  have h0step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
          .ok (truthParamState1
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc0 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h0]
  have h2step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState1
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc2 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h2]
  have h4step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState2
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState3
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc4 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h4mem, if_neg h4gas]
  have h5step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState3
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState4
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc5 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h5]
  have h6step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState4
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState5
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc6 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h6]
  have h7step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState5
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState6
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc7 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h7]
  have h8step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState6
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState7
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc8 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h8]
  have h10step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState7
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamNonpayableState8
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_nonpayable_xstep_pc10 createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      h_code h_value]
    rw [if_neg h10]
  have h11step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamNonpayableState8
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamNonpayableState9
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_nonpayable_xstep_pc11 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h11]
  have h12step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamNonpayableState9
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamNonpayableState10
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_nonpayable_xstep_pc12 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h12]
  have h13step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamNonpayableState10
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok
            (truthParamNonpayableState11
              (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I),
              .some (false, truthParamNonpayableReturnData
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))) := by
    exact truth_fresh_nonpayable_xstep_pc13 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code
  have hfuel :
      g.toNat + 1 = (g.toNat - 10) + 11 := by
    omega
  rw [hfuel]
  exact truth_fresh_nonpayable_X_trace_of_xsteps createdAccounts genesisBlockHeader blocks σ σ₀
    g A I (g.toNat - 10) h0step h2step h4step h5step h6step h7step h8step
    h10step h11step h12step h13step

theorem truth_fresh_nonpayable_Xi_outOfGas_at_pc0
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode)
    (h0 : g.toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass := by
  apply truth_Xi_outOfGas_of_fresh_Xstep_outOfGas
  rw [truth_fresh_xstep_pc0 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
  rw [if_pos h0]

theorem truth_fresh_nonpayable_Xi_outOfGas_at_pc2
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode)
    (h0 : ¬ g.toNat < GasConstants.Gverylow)
    (h2 :
      (truthParamState1
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass := by
  apply truth_Xi_outOfGas_of_X_fresh_outOfGas
  have h0step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
          .ok (truthParamState1
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc0 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h0]
  have h2step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState1
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .error .OutOfGass := by
    rw [truth_fresh_xstep_pc2 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_pos h2]
  have hfuel :
      g.toNat + 1 = (g.toNat - 1 + 1) + 1 := by
    have hg : 1 ≤ g.toNat := by
      omega
    omega
  rw [hfuel]
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h0step
  apply Ethereum.EVM.Xstep_X_X_except
  exact h2step

theorem truth_fresh_nonpayable_Xi_outOfGas_at_pc4_memory
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode)
    (h0 : ¬ g.toNat < GasConstants.Gverylow)
    (h2 :
      ¬ (truthParamState1
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h4mem :
      (truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost
          (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass := by
  apply truth_Xi_outOfGas_of_X_fresh_outOfGas
  have h0step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
          .ok (truthParamState1
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc0 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h0]
  have h2step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState1
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc2 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h2]
  have h4step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState2
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .error .OutOfGass := by
    rw [truth_fresh_xstep_pc4 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_pos h4mem]
  have hfuel :
      g.toNat + 1 = (g.toNat - 2 + 2) + 1 := by
    have hverylow : 2 ≤ GasConstants.Gverylow := by
      native_decide
    have hg : 2 ≤ g.toNat := by
      omega
    omega
  rw [hfuel]
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h0step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h2step
  apply Ethereum.EVM.Xstep_X_X_except
  exact h4step

theorem truth_fresh_nonpayable_Xi_outOfGas_at_pc4_gas
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode)
    (h0 : ¬ g.toNat < GasConstants.Gverylow)
    (h2 :
      ¬ (truthParamState1
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h4mem :
      ¬ (truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost
          (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)
    (h4gas :
      ((truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
          Ethereum.UInt256.ofNat
            (Ethereum.EVM.memoryExpansionCost
              (truthParamState2
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)).toNat <
        GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass := by
  apply truth_Xi_outOfGas_of_X_fresh_outOfGas
  have h0step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
          .ok (truthParamState1
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc0 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h0]
  have h2step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState1
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc2 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h2]
  have h4step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState2
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .error .OutOfGass := by
    rw [truth_fresh_xstep_pc4 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h4mem, if_pos h4gas]
  have hfuel :
      g.toNat + 1 = (g.toNat - 2 + 2) + 1 := by
    have hverylow : 2 ≤ GasConstants.Gverylow := by
      native_decide
    have hg : 2 ≤ g.toNat := by
      omega
    omega
  rw [hfuel]
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h0step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h2step
  apply Ethereum.EVM.Xstep_X_X_except
  exact h4step

theorem truth_fresh_nonpayable_Xi_outOfGas_at_pc5
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode)
    (h0 : ¬ g.toNat < GasConstants.Gverylow)
    (h2 :
      ¬ (truthParamState1
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h4mem :
      ¬ (truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost
          (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)
    (h4gas :
      ¬ ((truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
          Ethereum.UInt256.ofNat
            (Ethereum.EVM.memoryExpansionCost
              (truthParamState2
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)).toNat <
        GasConstants.Gverylow)
    (h5 :
      (truthParamState3
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass := by
  apply truth_Xi_outOfGas_of_X_fresh_outOfGas
  have h0step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
          .ok (truthParamState1
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc0 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h0]
  have h2step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState1
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc2 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h2]
  have h4step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState2
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState3
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc4 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h4mem, if_neg h4gas]
  have h5step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState3
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .error .OutOfGass := by
    rw [truth_fresh_xstep_pc5 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_pos h5]
  have hfuel :
      g.toNat + 1 = (g.toNat - 3 + 3) + 1 := by
    have hverylow : 3 ≤ GasConstants.Gverylow := by
      native_decide
    have hg : 3 ≤ g.toNat := by
      omega
    omega
  rw [hfuel]
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h0step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h2step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h4step
  apply Ethereum.EVM.Xstep_X_X_except
  exact h5step

theorem truth_fresh_nonpayable_Xi_outOfGas_at_pc6
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode)
    (h_fuel : 4 ≤ g.toNat)
    (h0 : ¬ g.toNat < GasConstants.Gverylow)
    (h2 :
      ¬ (truthParamState1
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h4mem :
      ¬ (truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost
          (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)
    (h4gas :
      ¬ ((truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
          Ethereum.UInt256.ofNat
            (Ethereum.EVM.memoryExpansionCost
              (truthParamState2
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)).toNat <
        GasConstants.Gverylow)
    (h5 :
      ¬ (truthParamState3
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase)
    (h6 :
      (truthParamState4
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass := by
  apply truth_Xi_outOfGas_of_X_fresh_outOfGas
  have h0step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
          .ok (truthParamState1
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc0 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h0]
  have h2step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState1
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc2 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h2]
  have h4step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState2
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState3
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc4 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h4mem, if_neg h4gas]
  have h5step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState3
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState4
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc5 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h5]
  have h6step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState4
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .error .OutOfGass := by
    rw [truth_fresh_xstep_pc6 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_pos h6]
  have hfuel :
      g.toNat + 1 = (g.toNat - 4 + 4) + 1 := by
    omega
  rw [hfuel]
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h0step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h2step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h4step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h5step
  apply Ethereum.EVM.Xstep_X_X_except
  exact h6step

theorem truth_fresh_nonpayable_Xi_outOfGas_at_pc7
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode)
    (h_fuel : 5 ≤ g.toNat)
    (h0 : ¬ g.toNat < GasConstants.Gverylow)
    (h2 :
      ¬ (truthParamState1
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h4mem :
      ¬ (truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost
          (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)
    (h4gas :
      ¬ ((truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
          Ethereum.UInt256.ofNat
            (Ethereum.EVM.memoryExpansionCost
              (truthParamState2
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)).toNat <
        GasConstants.Gverylow)
    (h5 :
      ¬ (truthParamState3
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase)
    (h6 :
      ¬ (truthParamState4
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h7 :
      (truthParamState5
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass := by
  apply truth_Xi_outOfGas_of_X_fresh_outOfGas
  have h0step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
          .ok (truthParamState1
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc0 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h0]
  have h2step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState1
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc2 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h2]
  have h4step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState2
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState3
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc4 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h4mem, if_neg h4gas]
  have h5step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState3
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState4
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc5 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h5]
  have h6step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState4
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState5
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc6 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h6]
  have h7step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState5
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .error .OutOfGass := by
    rw [truth_fresh_xstep_pc7 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_pos h7]
  have hfuel :
      g.toNat + 1 = (g.toNat - 5 + 5) + 1 := by
    omega
  rw [hfuel]
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h0step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h2step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h4step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h5step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h6step
  apply Ethereum.EVM.Xstep_X_X_except
  exact h7step

theorem truth_fresh_nonpayable_Xi_outOfGas_at_pc8
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode)
    (h_fuel : 6 ≤ g.toNat)
    (h0 : ¬ g.toNat < GasConstants.Gverylow)
    (h2 :
      ¬ (truthParamState1
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h4mem :
      ¬ (truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost
          (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)
    (h4gas :
      ¬ ((truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
          Ethereum.UInt256.ofNat
            (Ethereum.EVM.memoryExpansionCost
              (truthParamState2
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)).toNat <
        GasConstants.Gverylow)
    (h5 :
      ¬ (truthParamState3
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase)
    (h6 :
      ¬ (truthParamState4
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h7 :
      ¬ (truthParamState5
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h8 :
      (truthParamState6
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass := by
  apply truth_Xi_outOfGas_of_X_fresh_outOfGas
  have h0step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
          .ok (truthParamState1
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc0 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h0]
  have h2step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState1
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc2 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h2]
  have h4step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState2
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState3
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc4 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h4mem, if_neg h4gas]
  have h5step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState3
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState4
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc5 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h5]
  have h6step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState4
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState5
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc6 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h6]
  have h7step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState5
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState6
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc7 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h7]
  have h8step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState6
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .error .OutOfGass := by
    rw [truth_fresh_xstep_pc8 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_pos h8]
  have hfuel :
      g.toNat + 1 = (g.toNat - 6 + 6) + 1 := by
    omega
  rw [hfuel]
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h0step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h2step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h4step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h5step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h6step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h7step
  apply Ethereum.EVM.Xstep_X_X_except
  exact h8step

theorem truth_fresh_nonpayable_Xi_outOfGas_at_pc10
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode)
    (h_value : I.weiValue.val ≠ 0)
    (h_fuel : 7 ≤ g.toNat)
    (h0 : ¬ g.toNat < GasConstants.Gverylow)
    (h2 :
      ¬ (truthParamState1
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h4mem :
      ¬ (truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost
          (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)
    (h4gas :
      ¬ ((truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
          Ethereum.UInt256.ofNat
            (Ethereum.EVM.memoryExpansionCost
              (truthParamState2
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)).toNat <
        GasConstants.Gverylow)
    (h5 :
      ¬ (truthParamState3
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase)
    (h6 :
      ¬ (truthParamState4
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h7 :
      ¬ (truthParamState5
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h8 :
      ¬ (truthParamState6
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h10 :
      (truthParamState7
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Ghigh) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass := by
  apply truth_Xi_outOfGas_of_X_fresh_outOfGas
  have h0step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
          .ok (truthParamState1
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc0 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h0]
  have h2step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState1
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc2 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h2]
  have h4step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState2
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState3
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc4 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h4mem, if_neg h4gas]
  have h5step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState3
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState4
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc5 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h5]
  have h6step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState4
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState5
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc6 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h6]
  have h7step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState5
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState6
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc7 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h7]
  have h8step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState6
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState7
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc8 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h8]
  have h10step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState7
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .error .OutOfGass := by
    rw [truth_fresh_nonpayable_xstep_pc10 createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      h_code h_value]
    rw [if_pos h10]
  have hfuel :
      g.toNat + 1 = (g.toNat - 7 + 7) + 1 := by
    omega
  rw [hfuel]
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h0step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h2step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h4step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h5step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h6step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h7step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h8step
  apply Ethereum.EVM.Xstep_X_X_except
  exact h10step

theorem truth_fresh_nonpayable_Xi_outOfGas_at_pc11
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode)
    (h_value : I.weiValue.val ≠ 0)
    (h_fuel : 8 ≤ g.toNat)
    (h0 : ¬ g.toNat < GasConstants.Gverylow)
    (h2 :
      ¬ (truthParamState1
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h4mem :
      ¬ (truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost
          (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)
    (h4gas :
      ¬ ((truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
          Ethereum.UInt256.ofNat
            (Ethereum.EVM.memoryExpansionCost
              (truthParamState2
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)).toNat <
        GasConstants.Gverylow)
    (h5 :
      ¬ (truthParamState3
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase)
    (h6 :
      ¬ (truthParamState4
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h7 :
      ¬ (truthParamState5
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h8 :
      ¬ (truthParamState6
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h10 :
      ¬ (truthParamState7
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Ghigh)
    (h11 :
      (truthParamNonpayableState8
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass := by
  apply truth_Xi_outOfGas_of_X_fresh_outOfGas
  have h0step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
          .ok (truthParamState1
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc0 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h0]
  have h2step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState1
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc2 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h2]
  have h4step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState2
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState3
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc4 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h4mem, if_neg h4gas]
  have h5step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState3
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState4
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc5 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h5]
  have h6step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState4
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState5
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc6 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h6]
  have h7step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState5
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState6
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc7 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h7]
  have h8step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState6
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState7
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc8 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h8]
  have h10step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState7
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamNonpayableState8
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_nonpayable_xstep_pc10 createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      h_code h_value]
    rw [if_neg h10]
  have h11step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamNonpayableState8
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .error .OutOfGass := by
    rw [truth_fresh_nonpayable_xstep_pc11 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_pos h11]
  have hfuel :
      g.toNat + 1 = (g.toNat - 8 + 8) + 1 := by
    omega
  rw [hfuel]
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h0step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h2step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h4step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h5step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h6step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h7step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h8step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h10step
  apply Ethereum.EVM.Xstep_X_X_except
  exact h11step

theorem truth_fresh_nonpayable_Xi_outOfGas_at_pc12
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode)
    (h_value : I.weiValue.val ≠ 0)
    (h_fuel : 9 ≤ g.toNat)
    (h0 : ¬ g.toNat < GasConstants.Gverylow)
    (h2 :
      ¬ (truthParamState1
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h4mem :
      ¬ (truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost
          (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)
    (h4gas :
      ¬ ((truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
          Ethereum.UInt256.ofNat
            (Ethereum.EVM.memoryExpansionCost
              (truthParamState2
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)).toNat <
        GasConstants.Gverylow)
    (h5 :
      ¬ (truthParamState3
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase)
    (h6 :
      ¬ (truthParamState4
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h7 :
      ¬ (truthParamState5
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h8 :
      ¬ (truthParamState6
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow)
    (h10 :
      ¬ (truthParamState7
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Ghigh)
    (h11 :
      ¬ (truthParamNonpayableState8
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase)
    (h12 :
      (truthParamNonpayableState9
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass := by
  apply truth_Xi_outOfGas_of_X_fresh_outOfGas
  have h0step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
          .ok (truthParamState1
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc0 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h0]
  have h2step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState1
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc2 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h2]
  have h4step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState2
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState3
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc4 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h4mem, if_neg h4gas]
  have h5step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState3
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState4
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc5 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h5]
  have h6step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState4
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState5
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc6 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h6]
  have h7step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState5
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState6
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc7 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h7]
  have h8step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState6
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState7
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc8 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h8]
  have h10step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState7
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamNonpayableState8
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_nonpayable_xstep_pc10 createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      h_code h_value]
    rw [if_neg h10]
  have h11step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamNonpayableState8
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamNonpayableState9
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_nonpayable_xstep_pc11 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h11]
  have h12step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamNonpayableState9
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .error .OutOfGass := by
    rw [truth_fresh_nonpayable_xstep_pc12 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_pos h12]
  have hfuel :
      g.toNat + 1 = (g.toNat - 9 + 9) + 1 := by
    omega
  rw [hfuel]
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h0step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h2step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h4step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h5step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h6step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h7step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h8step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h10step
  apply Ethereum.EVM.Xstep_X_X_continue
  · exact h11step
  apply Ethereum.EVM.Xstep_X_X_except
  exact h12step

theorem truth_act_exec (evm : EVM.State)
    (h_value : evm.executionEnv.weiValue = (⟨0⟩ : Ethereum.UInt256)) :
    ExecContractBody truthConfig truthContract evm (∅ : Store) truthTransition.body
      (.returned { contract := truthContract, locals := ∅ } evm (some (.bool true))) := by
  apply Act.ExecFuncBody.execBlockRet
  apply Act.ExecBlock.consNormal
  · apply Act.ExecStmt.requireTrue
    simp only [evalExpr?]
    change evalBinaryOp? BinaryOp.eq (envValue evm EnvVar.callvalue) (Value.int 0) =
      some (Value.bool true)
    simp [envValue, evalBinaryOp?, h_value]
  · apply Act.ExecBlock.consReturn
    apply Act.ExecStmt.return
    simp [evalExpr?]

theorem truth_act_revert_nonpayable (evm : EVM.State)
    (h_value : evm.executionEnv.weiValue.val ≠ 0) :
    ExecContractBody truthConfig truthContract evm (∅ : Store) truthTransition.body .reverted := by
  apply Act.ExecFuncBody.execBlockRevert
  apply Act.ExecBlock.consRevert
  apply Act.ExecStmt.requireFalse
  simp only [evalExpr?]
  change evalBinaryOp? BinaryOp.eq (envValue evm EnvVar.callvalue) (Value.int 0) =
    some (Value.bool false)
  simp [envValue, evalBinaryOp?, h_value]

theorem truth_return_encoding :
    encodeReturnValue? (.elem .bool) (.bool true) = some truthReturnData := by
  native_decide

theorem truth_success_execResultsEquiv
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (σ : Ethereum.AccountMap)
    (g' : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (evmState : EVM.State)
    (h_createdAccounts : createdAccounts = evmState.createdAccounts)
    (h_accountMap : σ = evmState.accountMap)
    (h_substate : A = evmState.substate) :
    execResultsEquiv
      (.ok (.success (createdAccounts, σ, g', A) truthReturnData))
      (.returned { contract := truthContract, locals := ∅ } evmState (some (.bool true)))
      (some (.elem .bool)) := by
  apply execResultsEquiv.success
  · rfl
  · rfl
  · exact h_createdAccounts
  · exact h_accountMap
  · exact h_substate
  · apply returnEquiv.returned
    · rfl
    · rfl
    · exact truth_return_encoding

theorem truth_success_runtimeEquivalenceFor
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (g' : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode)
    (h_value : I.weiValue = (⟨0⟩ : Ethereum.UInt256))
    (h_dispatch : dispatchMsg truthContract I.calldata = some truthTransition)
    (h_decode : decodeCalldata [] [] I.calldata = some (∅ : Store))
    (h_evm :
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .ok (.success (createdAccounts, σ, g', A) truthReturnData)) :
    runtimeEquivalenceFor truthConfig truthRuntimeBytecode truthContract
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I := by
  let evmState : EVM.State :=
    { (default : EVM.State) with
        accountMap := σ
        σ₀ := σ₀
        executionEnv := I
        substate := A
        createdAccounts := createdAccounts
        machineState.gasAvailable := g
        blocks := blocks
        genesisBlockHeader := genesisBlockHeader }
  apply runtimeEquivalenceFor.execution
    (transition := truthTransition)
    (transitionSig := transitionSignature truthTransition)
    (callargs := (∅ : Store))
    (Ξ_res := .ok (.success (createdAccounts, σ, g', A) truthReturnData))
    (evmState := evmState)
    (actRes := .returned { contract := truthContract, locals := ∅ } evmState (some (.bool true)))
  · exact h_code
  · exact h_dispatch
  · rfl
  · simpa [truthTransition] using h_decode
  · exact h_evm
  · rfl
  · exact truth_act_exec evmState h_value
  · exact truth_success_execResultsEquiv createdAccounts σ g' A evmState rfl rfl rfl

theorem truth_concrete_runtimeEquivalenceFor :
    runtimeEquivalenceFor truthConfig truthRuntimeBytecode truthContract
      truthInitialState.createdAccounts truthInitialState.genesisBlockHeader truthInitialState.blocks
      truthInitialState.accountMap truthInitialState.σ₀ (⟨100000⟩ : Ethereum.UInt256)
      truthInitialState.substate truthExecutionEnv := by
  apply truth_success_runtimeEquivalenceFor
    (g' := truthState93.machineState.gasAvailable)
  · rfl
  · rfl
  · exact truth_dispatch
  · exact truth_calldata_decodes
  · exact truth_Xi_trace

theorem truth_noDispatch_runtimeEquivalenceFor
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g g' : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (o : ByteArray)
    (h_code : I.code = truthRuntimeBytecode)
    (h_dispatch : dispatchMsg truthContract I.calldata = none)
    (h_evm :
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .ok (.revert g' o)) :
    runtimeEquivalenceFor truthConfig truthRuntimeBytecode truthContract
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I := by
  exact runtimeEquivalenceFor.noDispatch h_code h_dispatch h_evm

theorem truth_decodingFailed_runtimeEquivalenceFor
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g g' : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (o : ByteArray)
    (transition : TransitionDecl)
    (transitionSig : Signature)
    (h_code : I.code = truthRuntimeBytecode)
    (h_dispatch : dispatchMsg truthContract I.calldata = some transition)
    (h_sig : transitionSig = transitionSignature transition)
    (h_decode :
      decodeCalldata (transition.params.map Param.name) transitionSig.paramTypes I.calldata = none)
    (h_evm :
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .ok (.revert g' o)) :
    runtimeEquivalenceFor truthConfig truthRuntimeBytecode truthContract
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I := by
  exact runtimeEquivalenceFor.decodingFailed h_code h_dispatch h_sig h_decode h_evm

theorem truth_nonPayable_runtimeEquivalenceFor
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g g' : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (o : ByteArray)
    (h_code : I.code = truthRuntimeBytecode)
    (h_value : I.weiValue.val ≠ 0)
    (h_dispatch : dispatchMsg truthContract I.calldata = some truthTransition)
    (h_decode : decodeCalldata [] [] I.calldata = some (∅ : Store))
    (h_evm :
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .ok (.revert g' o)) :
    runtimeEquivalenceFor truthConfig truthRuntimeBytecode truthContract
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I := by
  let evmState : EVM.State :=
    { (default : EVM.State) with
        accountMap := σ
        σ₀ := σ₀
        executionEnv := I
        substate := A
        createdAccounts := createdAccounts
        machineState.gasAvailable := g
        blocks := blocks
        genesisBlockHeader := genesisBlockHeader }
  apply runtimeEquivalenceFor.execution
    (transition := truthTransition)
    (transitionSig := transitionSignature truthTransition)
    (callargs := (∅ : Store))
    (Ξ_res := .ok (.revert g' o))
    (evmState := evmState)
    (actRes := .reverted)
  · exact h_code
  · exact h_dispatch
  · rfl
  · simpa [truthTransition] using h_decode
  · exact h_evm
  · rfl
  · exact truth_act_revert_nonpayable evmState h_value
  · apply execResultsEquiv.revert
    · rfl
    · rfl

theorem truth_nonpayable_concrete_runtimeEquivalenceFor :
    runtimeEquivalenceFor truthConfig truthRuntimeBytecode truthContract
      truthNonpayableInitialState.createdAccounts truthNonpayableInitialState.genesisBlockHeader
      truthNonpayableInitialState.blocks truthNonpayableInitialState.accountMap
      truthNonpayableInitialState.σ₀ (⟨100000⟩ : Ethereum.UInt256)
      truthNonpayableInitialState.substate truthNonpayableExecutionEnv := by
  apply truth_nonPayable_runtimeEquivalenceFor
    (g' := truthNonpayableState11.machineState.gasAvailable)
    (o := truthNonpayableReturnData)
  · rfl
  · native_decide
  · exact truth_dispatch
  · exact truth_calldata_decodes
  · exact truth_nonpayable_Xi_trace

theorem truth_short_concrete_runtimeEquivalenceFor :
    runtimeEquivalenceFor truthConfig truthRuntimeBytecode truthContract
      truthShortInitialState.createdAccounts truthShortInitialState.genesisBlockHeader
      truthShortInitialState.blocks truthShortInitialState.accountMap truthShortInitialState.σ₀
      (⟨100000⟩ : Ethereum.UInt256) truthShortInitialState.substate truthShortExecutionEnv := by
  exact truth_noDispatch_runtimeEquivalenceFor
    truthShortInitialState.createdAccounts truthShortInitialState.genesisBlockHeader
    truthShortInitialState.blocks truthShortInitialState.accountMap truthShortInitialState.σ₀
    (⟨100000⟩ : Ethereum.UInt256) truthShortState19.machineState.gasAvailable
    truthShortInitialState.substate truthShortExecutionEnv truthShortReturnData
    rfl truth_short_dispatch_none truth_short_Xi_trace

theorem truth_mismatch_X_trace :
    Ethereum.EVM.X 100001 truthValidJumps truthMismatchInitialState =
      .ok (.revert truthMismatchState28.machineState.gasAvailable truthMismatchReturnData) := by
  truth_continue_step truth_mismatch_xstep_pc0
  truth_continue_step truth_mismatch_xstep_pc2
  truth_continue_step truth_mismatch_xstep_pc4
  truth_continue_step truth_mismatch_xstep_pc5
  truth_continue_step truth_mismatch_xstep_pc6
  truth_continue_step truth_mismatch_xstep_pc7
  truth_continue_step truth_mismatch_xstep_pc8
  truth_continue_step truth_mismatch_xstep_pc10
  truth_continue_step truth_mismatch_xstep_pc14
  truth_continue_step truth_mismatch_xstep_pc15
  truth_continue_step truth_mismatch_xstep_pc16
  truth_continue_step truth_mismatch_xstep_pc18
  truth_continue_step truth_mismatch_xstep_pc19
  truth_continue_step truth_mismatch_xstep_pc20
  truth_continue_step truth_mismatch_xstep_pc22
  truth_continue_step truth_mismatch_xstep_pc23
  truth_continue_step truth_mismatch_xstep_pc24
  truth_continue_step truth_mismatch_xstep_pc25
  truth_continue_step truth_mismatch_xstep_pc27
  truth_continue_step truth_mismatch_xstep_pc28
  truth_continue_step truth_mismatch_xstep_pc29
  truth_continue_step truth_mismatch_xstep_pc34
  truth_continue_step truth_mismatch_xstep_pc35
  truth_continue_step truth_mismatch_xstep_pc37
  truth_continue_step truth_mismatch_xstep_pc38
  truth_continue_step truth_mismatch_xstep_pc39
  truth_continue_step truth_mismatch_xstep_pc40
  apply Ethereum.EVM.Xstep_X_X_halt_revert
  exact truth_mismatch_xstep_pc41

theorem truth_mismatch_X_reverts :
  ∃ (g' : Ethereum.UInt256) (o : ByteArray),
    Ethereum.EVM.X 100001 truthValidJumps truthMismatchInitialState = .ok (.revert g' o) := by
  exact ⟨truthMismatchState28.machineState.gasAvailable, truthMismatchReturnData,
    truth_mismatch_X_trace⟩

theorem truth_mismatch_Xi_reverts :
    ∃ (g' : Ethereum.UInt256) (o : ByteArray),
      Ethereum.EVM.Ξ truthMismatchInitialState.createdAccounts truthMismatchInitialState.genesisBlockHeader
        truthMismatchInitialState.blocks truthMismatchInitialState.accountMap truthMismatchInitialState.σ₀
        (⟨100000⟩ : Ethereum.UInt256) truthMismatchInitialState.substate truthMismatchExecutionEnv =
          .ok (.revert g' o) := by
  rcases truth_mismatch_X_reverts with ⟨g', o, hX⟩
  refine ⟨g', o, ?_⟩
  unfold Ethereum.EVM.Ξ
  change
    (do
      let result ← Ethereum.EVM.X 100001 truthValidJumps truthMismatchInitialState
      match result with
      | Ethereum.ExecutionResult.success evmState' o =>
          .ok (Ethereum.ExecutionResult.success
            (evmState'.createdAccounts, evmState'.accountMap,
              evmState'.machineState.gasAvailable, evmState'.substate) o)
      | Ethereum.ExecutionResult.revert g' o => .ok (Ethereum.ExecutionResult.revert g' o)) =
      .ok (Ethereum.ExecutionResult.revert g' o)
  rw [hX]
  simp [bind, Except.bind]

theorem truth_mismatch_concrete_runtimeEquivalenceFor :
    runtimeEquivalenceFor truthConfig truthRuntimeBytecode truthContract
      truthMismatchInitialState.createdAccounts truthMismatchInitialState.genesisBlockHeader
      truthMismatchInitialState.blocks truthMismatchInitialState.accountMap truthMismatchInitialState.σ₀
      (⟨100000⟩ : Ethereum.UInt256) truthMismatchInitialState.substate truthMismatchExecutionEnv := by
  rcases truth_mismatch_Xi_reverts with ⟨g', o, h_evm⟩
  exact truth_noDispatch_runtimeEquivalenceFor
    truthMismatchInitialState.createdAccounts truthMismatchInitialState.genesisBlockHeader
    truthMismatchInitialState.blocks truthMismatchInitialState.accountMap truthMismatchInitialState.σ₀
    (⟨100000⟩ : Ethereum.UInt256) g' truthMismatchInitialState.substate
    truthMismatchExecutionEnv o rfl truth_mismatch_dispatch_none h_evm

theorem truth_outOfGas_runtimeEquivalenceFor
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode)
    (h_evm :
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .error .OutOfGass) :
    runtimeEquivalenceFor truthConfig truthRuntimeBytecode truthContract
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I := by
  exact runtimeEquivalenceFor.outOfGas h_code h_evm

inductive truthRuntimeCase
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) : Prop where
  | success
      (g' : Ethereum.UInt256)
      (h_value : I.weiValue = (⟨0⟩ : Ethereum.UInt256))
      (h_dispatch : dispatchMsg truthContract I.calldata = some truthTransition)
      (h_decode : decodeCalldata [] [] I.calldata = some (∅ : Store))
      (h_evm :
        Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
          .ok (.success (createdAccounts, σ, g', A) truthReturnData)) :
      truthRuntimeCase createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  | nonpayable
      (g' : Ethereum.UInt256)
      (o : ByteArray)
      (h_value : I.weiValue.val ≠ 0)
      (h_dispatch : dispatchMsg truthContract I.calldata = some truthTransition)
      (h_decode : decodeCalldata [] [] I.calldata = some (∅ : Store))
      (h_evm :
        Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
          .ok (.revert g' o)) :
      truthRuntimeCase createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  | noDispatch
      (g' : Ethereum.UInt256)
      (o : ByteArray)
      (h_dispatch : dispatchMsg truthContract I.calldata = none)
      (h_evm :
        Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
          .ok (.revert g' o)) :
      truthRuntimeCase createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  | decodingFailed
      (g' : Ethereum.UInt256)
      (o : ByteArray)
      (transition : TransitionDecl)
      (transitionSig : Signature)
      (h_dispatch : dispatchMsg truthContract I.calldata = some transition)
      (h_sig : transitionSig = transitionSignature transition)
      (h_decode :
        decodeCalldata (transition.params.map Param.name) transitionSig.paramTypes I.calldata = none)
      (h_evm :
        Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
          .ok (.revert g' o)) :
      truthRuntimeCase createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  | outOfGas
      (h_evm :
        Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
          .error .OutOfGass) :
      truthRuntimeCase createdAccounts genesisBlockHeader blocks σ σ₀ g A I

theorem truthRuntimeCase.runtimeEquivalenceFor
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode)
    (h_case : truthRuntimeCase createdAccounts genesisBlockHeader blocks σ σ₀ g A I) :
    runtimeEquivalenceFor truthConfig truthRuntimeBytecode truthContract
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I := by
  cases h_case with
  | success g' h_value h_dispatch h_decode h_evm =>
      exact truth_success_runtimeEquivalenceFor createdAccounts genesisBlockHeader blocks
        σ σ₀ g g' A I h_code h_value h_dispatch h_decode h_evm
  | nonpayable g' o h_value h_dispatch h_decode h_evm =>
      exact truth_nonPayable_runtimeEquivalenceFor createdAccounts genesisBlockHeader blocks
        σ σ₀ g g' A I o h_code h_value h_dispatch h_decode h_evm
  | noDispatch g' o h_dispatch h_evm =>
      exact truth_noDispatch_runtimeEquivalenceFor createdAccounts genesisBlockHeader blocks
        σ σ₀ g g' A I o h_code h_dispatch h_evm
  | decodingFailed g' o transition transitionSig h_dispatch h_sig h_decode h_evm =>
      exact truth_decodingFailed_runtimeEquivalenceFor createdAccounts genesisBlockHeader blocks
        σ σ₀ g g' A I o transition transitionSig h_code h_dispatch h_sig h_decode h_evm
  | outOfGas h_evm =>
      exact truth_outOfGas_runtimeEquivalenceFor createdAccounts genesisBlockHeader blocks
        σ σ₀ g A I h_code h_evm

def truthBytecodeCoversRuntimeCases : Prop :=
  ∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv),
    I.code = truthRuntimeBytecode →
    I.calldata.size < Ethereum.UInt256.size →
    truthRuntimeCase createdAccounts genesisBlockHeader blocks σ σ₀ g A I

def truthBytecodeSemanticSpec : Prop :=
  ∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv),
    I.code = truthRuntimeBytecode →
    I.calldata.size < Ethereum.UInt256.size →
      (∃ g',
        I.weiValue = (⟨0⟩ : Ethereum.UInt256) ∧
        dispatchMsg truthContract I.calldata = some truthTransition ∧
        decodeCalldata [] [] I.calldata = some (∅ : Store) ∧
        Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
          .ok (.success (createdAccounts, σ, g', A) truthReturnData)) ∨
      (∃ g' o,
        I.weiValue.val ≠ 0 ∧
        dispatchMsg truthContract I.calldata = some truthTransition ∧
        decodeCalldata [] [] I.calldata = some (∅ : Store) ∧
        Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
          .ok (.revert g' o)) ∨
      (∃ g' o,
        dispatchMsg truthContract I.calldata = none ∧
        Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
          .ok (.revert g' o)) ∨
      (∃ g' o transition transitionSig,
        dispatchMsg truthContract I.calldata = some transition ∧
        transitionSig = transitionSignature transition ∧
        decodeCalldata (transition.params.map Param.name) transitionSig.paramTypes I.calldata = none ∧
        Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
          .ok (.revert g' o)) ∨
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .error .OutOfGass

def truthBytecodeSuccessBranchSpec : Prop :=
  ∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv),
    I.code = truthRuntimeBytecode →
    I.calldata.size < Ethereum.UInt256.size →
    I.weiValue = (⟨0⟩ : Ethereum.UInt256) →
    dispatchMsg truthContract I.calldata = some truthTransition →
    decodeCalldata [] [] I.calldata = some (∅ : Store) →
      (∃ g',
        Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
          .ok (.success (createdAccounts, σ, g', A) truthReturnData)) ∨
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .error .OutOfGass

def truthBytecodeNonpayableBranchSpec : Prop :=
  ∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv),
    I.code = truthRuntimeBytecode →
    I.calldata.size < Ethereum.UInt256.size →
    I.weiValue.val ≠ 0 →
    dispatchMsg truthContract I.calldata = some truthTransition →
    decodeCalldata [] [] I.calldata = some (∅ : Store) →
      (∃ g' o,
        Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
          .ok (.revert g' o)) ∨
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .error .OutOfGass

def truthBytecodeNoDispatchBranchSpec : Prop :=
  ∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv),
    I.code = truthRuntimeBytecode →
    I.calldata.size < Ethereum.UInt256.size →
    dispatchMsg truthContract I.calldata = none →
      (∃ g' o,
        Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
          .ok (.revert g' o)) ∨
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .error .OutOfGass

def truthBytecodeDecodingFailedBranchSpec : Prop :=
  ∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv),
    I.code = truthRuntimeBytecode →
    I.calldata.size < Ethereum.UInt256.size →
    dispatchMsg truthContract I.calldata = some truthTransition →
    decodeCalldata [] [] I.calldata = none →
      (∃ g' o,
        Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
          .ok (.revert g' o)) ∨
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .error .OutOfGass

def truthBytecodeSuccessTraceSpec : Prop :=
  ∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv),
    I.code = truthRuntimeBytecode →
    I.calldata.size < Ethereum.UInt256.size →
    I.weiValue = (⟨0⟩ : Ethereum.UInt256) →
    I.calldata.extract 0 4 = truthSelector →
    4 ≤ I.calldata.toList.length →
      (∃ g',
        Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
          .ok (.success (createdAccounts, σ, g', A) truthReturnData)) ∨
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .error .OutOfGass

def truthBytecodeNonpayableTraceSpec : Prop :=
  ∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv),
    I.code = truthRuntimeBytecode →
    I.calldata.size < Ethereum.UInt256.size →
    I.weiValue.val ≠ 0 →
      (∃ g' o,
        Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
          .ok (.revert g' o)) ∨
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .error .OutOfGass

def truthNonpayableNoOOGConditions
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) : Prop :=
  10 ≤ g.toNat ∧
  ¬ g.toNat < GasConstants.Gverylow ∧
  ¬ (truthParamState1
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamState2
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    Ethereum.EVM.memoryExpansionCost
      (truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE ∧
  ¬ ((truthParamState2
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
      Ethereum.UInt256.ofNat
        (Ethereum.EVM.memoryExpansionCost
          (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)).toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamState3
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gbase ∧
  ¬ (truthParamState4
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamState5
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamState6
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamState7
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Ghigh ∧
  ¬ (truthParamNonpayableState8
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gbase ∧
  ¬ (truthParamNonpayableState9
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gbase

inductive truthNonpayableGuardCase
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) : Prop where
  | noOOG :
      truthNonpayableNoOOGConditions createdAccounts genesisBlockHeader blocks σ σ₀ g A I →
      truthNonpayableGuardCase createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  | pc0 :
      g.toNat < GasConstants.Gverylow →
      truthNonpayableGuardCase createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  | pc2 :
      ¬ g.toNat < GasConstants.Gverylow →
      (truthParamState1
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow →
      truthNonpayableGuardCase createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  | pc4_memory :
      ¬ g.toNat < GasConstants.Gverylow →
      ¬ (truthParamState1
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow →
      (truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost
          (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE →
      truthNonpayableGuardCase createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  | pc4_gas :
      ¬ g.toNat < GasConstants.Gverylow →
      ¬ (truthParamState1
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow →
      ¬ (truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost
          (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE →
      ((truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
          Ethereum.UInt256.ofNat
            (Ethereum.EVM.memoryExpansionCost
              (truthParamState2
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)).toNat <
        GasConstants.Gverylow →
      truthNonpayableGuardCase createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  | pc5 :
      ¬ g.toNat < GasConstants.Gverylow →
      ¬ (truthParamState1
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow →
      ¬ (truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost
          (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE →
      ¬ ((truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
          Ethereum.UInt256.ofNat
            (Ethereum.EVM.memoryExpansionCost
              (truthParamState2
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)).toNat <
        GasConstants.Gverylow →
      (truthParamState3
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase →
      truthNonpayableGuardCase createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  | pc6 :
      4 ≤ g.toNat →
      ¬ g.toNat < GasConstants.Gverylow →
      ¬ (truthParamState1
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow →
      ¬ (truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost
          (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE →
      ¬ ((truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
          Ethereum.UInt256.ofNat
            (Ethereum.EVM.memoryExpansionCost
              (truthParamState2
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)).toNat <
        GasConstants.Gverylow →
      ¬ (truthParamState3
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase →
      (truthParamState4
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow →
      truthNonpayableGuardCase createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  | pc7 :
      5 ≤ g.toNat →
      ¬ g.toNat < GasConstants.Gverylow →
      ¬ (truthParamState1
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow →
      ¬ (truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost
          (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE →
      ¬ ((truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
          Ethereum.UInt256.ofNat
            (Ethereum.EVM.memoryExpansionCost
              (truthParamState2
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)).toNat <
        GasConstants.Gverylow →
      ¬ (truthParamState3
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase →
      ¬ (truthParamState4
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow →
      (truthParamState5
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow →
      truthNonpayableGuardCase createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  | pc8 :
      6 ≤ g.toNat →
      ¬ g.toNat < GasConstants.Gverylow →
      ¬ (truthParamState1
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow →
      ¬ (truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost
          (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE →
      ¬ ((truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
          Ethereum.UInt256.ofNat
            (Ethereum.EVM.memoryExpansionCost
              (truthParamState2
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)).toNat <
        GasConstants.Gverylow →
      ¬ (truthParamState3
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase →
      ¬ (truthParamState4
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow →
      ¬ (truthParamState5
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow →
      (truthParamState6
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow →
      truthNonpayableGuardCase createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  | pc10 :
      7 ≤ g.toNat →
      ¬ g.toNat < GasConstants.Gverylow →
      ¬ (truthParamState1
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow →
      ¬ (truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost
          (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE →
      ¬ ((truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
          Ethereum.UInt256.ofNat
            (Ethereum.EVM.memoryExpansionCost
              (truthParamState2
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)).toNat <
        GasConstants.Gverylow →
      ¬ (truthParamState3
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase →
      ¬ (truthParamState4
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow →
      ¬ (truthParamState5
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow →
      ¬ (truthParamState6
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow →
      (truthParamState7
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Ghigh →
      truthNonpayableGuardCase createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  | pc11 :
      8 ≤ g.toNat →
      ¬ g.toNat < GasConstants.Gverylow →
      ¬ (truthParamState1
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow →
      ¬ (truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost
          (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE →
      ¬ ((truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
          Ethereum.UInt256.ofNat
            (Ethereum.EVM.memoryExpansionCost
              (truthParamState2
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)).toNat <
        GasConstants.Gverylow →
      ¬ (truthParamState3
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase →
      ¬ (truthParamState4
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow →
      ¬ (truthParamState5
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow →
      ¬ (truthParamState6
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow →
      ¬ (truthParamState7
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Ghigh →
      (truthParamNonpayableState8
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase →
      truthNonpayableGuardCase createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  | pc12 :
      9 ≤ g.toNat →
      ¬ g.toNat < GasConstants.Gverylow →
      ¬ (truthParamState1
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow →
      ¬ (truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost
          (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE →
      ¬ ((truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
          Ethereum.UInt256.ofNat
            (Ethereum.EVM.memoryExpansionCost
              (truthParamState2
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)).toNat <
        GasConstants.Gverylow →
      ¬ (truthParamState3
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase →
      ¬ (truthParamState4
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow →
      ¬ (truthParamState5
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow →
      ¬ (truthParamState6
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow →
      ¬ (truthParamState7
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Ghigh →
      ¬ (truthParamNonpayableState8
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase →
      (truthParamNonpayableState9
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase →
      truthNonpayableGuardCase createdAccounts genesisBlockHeader blocks σ σ₀ g A I

def truthNonpayableGuardCoverage : Prop :=
  ∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv),
    I.code = truthRuntimeBytecode →
    I.weiValue.val ≠ 0 →
      truthNonpayableGuardCase createdAccounts genesisBlockHeader blocks σ σ₀ g A I

def truthNonpayableLowFuelGuardCoverage : Prop :=
  ∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv),
    I.code = truthRuntimeBytecode →
    I.weiValue.val ≠ 0 →
    g.toNat < 10 →
      truthNonpayableGuardCase createdAccounts genesisBlockHeader blocks σ σ₀ g A I

def truthNonpayableLowFuelGuardCoverageOfNoOutOfFuel : Prop :=
  ∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv),
    I.code = truthRuntimeBytecode →
    I.weiValue.val ≠ 0 →
    g.toNat < 10 →
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I ≠
      .error .OutOfFuel →
      truthNonpayableGuardCase createdAccounts genesisBlockHeader blocks σ σ₀ g A I

theorem truth_nonpayable_guard_coverage_of_enough_fuel
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_fuel : 10 ≤ g.toNat) :
    truthNonpayableGuardCase createdAccounts genesisBlockHeader blocks σ σ₀ g A I := by
  by_cases h0 : g.toNat < GasConstants.Gverylow
  · exact truthNonpayableGuardCase.pc0 h0
  by_cases h2 :
      (truthParamState1
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow
  · exact truthNonpayableGuardCase.pc2 h0 h2
  by_cases h4mem :
      (truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost
          (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE
  · exact truthNonpayableGuardCase.pc4_memory h0 h2 h4mem
  by_cases h4gas :
      ((truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
          Ethereum.UInt256.ofNat
            (Ethereum.EVM.memoryExpansionCost
              (truthParamState2
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)).toNat <
        GasConstants.Gverylow
  · exact truthNonpayableGuardCase.pc4_gas h0 h2 h4mem h4gas
  by_cases h5 :
      (truthParamState3
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase
  · exact truthNonpayableGuardCase.pc5 h0 h2 h4mem h4gas h5
  by_cases h6 :
      (truthParamState4
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow
  · have h_fuel6 : 4 ≤ g.toNat := by omega
    exact truthNonpayableGuardCase.pc6 h_fuel6 h0 h2 h4mem h4gas h5 h6
  by_cases h7 :
      (truthParamState5
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow
  · have h_fuel7 : 5 ≤ g.toNat := by omega
    exact truthNonpayableGuardCase.pc7 h_fuel7 h0 h2 h4mem h4gas h5 h6 h7
  by_cases h8 :
      (truthParamState6
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gverylow
  · have h_fuel8 : 6 ≤ g.toNat := by omega
    exact truthNonpayableGuardCase.pc8 h_fuel8 h0 h2 h4mem h4gas h5 h6 h7 h8
  by_cases h10 :
      (truthParamState7
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Ghigh
  · have h_fuel10 : 7 ≤ g.toNat := by omega
    exact truthNonpayableGuardCase.pc10 h_fuel10 h0 h2 h4mem h4gas h5 h6 h7 h8 h10
  by_cases h11 :
      (truthParamNonpayableState8
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase
  · have h_fuel11 : 8 ≤ g.toNat := by omega
    exact truthNonpayableGuardCase.pc11 h_fuel11 h0 h2 h4mem h4gas h5 h6 h7 h8 h10 h11
  by_cases h12 :
      (truthParamNonpayableState9
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        GasConstants.Gbase
  · have h_fuel12 : 9 ≤ g.toNat := by omega
    exact truthNonpayableGuardCase.pc12 h_fuel12 h0 h2 h4mem h4gas h5 h6 h7 h8 h10 h11 h12
  exact truthNonpayableGuardCase.noOOG
    ⟨h_fuel, h0, h2, h4mem, h4gas, h5, h6, h7, h8, h10, h11, h12⟩

def truthNonpayableGasCoverage : Prop :=
  ∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv),
    I.code = truthRuntimeBytecode →
    I.weiValue.val ≠ 0 →
      truthNonpayableNoOOGConditions createdAccounts genesisBlockHeader blocks σ σ₀ g A I ∨
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .error .OutOfGass

def truthShortNoOOGConditions
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) : Prop :=
  18 ≤ g.toNat ∧
  ¬ g.toNat < GasConstants.Gverylow ∧
  ¬ (truthParamState1
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamState2
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    Ethereum.EVM.memoryExpansionCost
      (truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE ∧
  ¬ ((truthParamState2
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
      Ethereum.UInt256.ofNat
        (Ethereum.EVM.memoryExpansionCost
          (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)).toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamState3
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gbase ∧
  ¬ (truthParamState4
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamState5
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamState6
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamState7
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Ghigh ∧
  ¬ (truthParamPayableState8
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gjumpdest ∧
  ¬ (truthParamPayableState9
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gbase ∧
  ¬ (truthParamPayableState10
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamPayableState11
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gbase ∧
  ¬ (truthParamPayableState12
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamPayableState13
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamPayableState14
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Ghigh ∧
  ¬ (truthParamShortState15
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gjumpdest ∧
  ¬ (truthParamShortState16
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gbase ∧
  ¬ (truthParamShortState17
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gbase

def truthShortGasCoverage : Prop :=
  ∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv),
    I.code = truthRuntimeBytecode →
    I.calldata.size < Ethereum.UInt256.size →
    I.weiValue = (⟨0⟩ : Ethereum.UInt256) →
    I.calldata.toList.length < 4 →
      truthShortNoOOGConditions createdAccounts genesisBlockHeader blocks σ σ₀ g A I ∨
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .error .OutOfGass

def truthSuccessPrefixNoOOGGuards
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) : Prop :=
  ¬ g.toNat < GasConstants.Gverylow ∧
  ¬ (truthParamState1
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamState2
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    Ethereum.EVM.memoryExpansionCost
      (truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE ∧
  ¬ ((truthParamState2
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
      Ethereum.UInt256.ofNat
        (Ethereum.EVM.memoryExpansionCost
          (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)).toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamState3
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gbase ∧
  ¬ (truthParamState4
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamState5
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamState6
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamState7
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Ghigh ∧
  ¬ (truthParamPayableState8
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gjumpdest ∧
  ¬ (truthParamPayableState9
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gbase ∧
  ¬ (truthParamPayableState10
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamPayableState11
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gbase ∧
  ¬ (truthParamPayableState12
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamPayableState13
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamPayableState14
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Ghigh ∧
  ¬ (truthParamMismatchState15
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gbase ∧
  ¬ (truthParamMismatchState16
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamMismatchState17
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamMismatchState18
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamMismatchState19
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamMismatchState20
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamMismatchState21
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamMismatchState22
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamMismatchState23
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Ghigh

def truthSuccessNoOOGConditions
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) : Prop :=
  92 ≤ g.toNat ∧
  truthSuccessPrefixNoOOGGuards createdAccounts genesisBlockHeader blocks σ σ₀ g A I

def truthSuccessGasCoverage : Prop :=
  ∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv),
    I.code = truthRuntimeBytecode →
    I.calldata.size < Ethereum.UInt256.size →
    I.weiValue = (⟨0⟩ : Ethereum.UInt256) →
    I.calldata.extract 0 4 = truthSelector →
    4 ≤ I.calldata.toList.length →
      truthSuccessNoOOGConditions createdAccounts genesisBlockHeader blocks σ σ₀ g A I ∨
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .error .OutOfGass

def truthSuccessNoOOGTraceSemantics : Prop :=
  ∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv),
    I.code = truthRuntimeBytecode →
    I.calldata.size < Ethereum.UInt256.size →
    I.weiValue = (⟨0⟩ : Ethereum.UInt256) →
    I.calldata.extract 0 4 = truthSelector →
    4 ≤ I.calldata.toList.length →
    truthSuccessNoOOGConditions createdAccounts genesisBlockHeader blocks σ σ₀ g A I →
      ∃ g',
        Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
          .ok (.success (createdAccounts, σ, g', A) truthReturnData)

def truthMismatchNoOOGConditions
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) : Prop :=
  27 ≤ g.toNat ∧
  ¬ g.toNat < GasConstants.Gverylow ∧
  ¬ (truthParamState1
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamState2
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    Ethereum.EVM.memoryExpansionCost
      (truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE ∧
  ¬ ((truthParamState2
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
      Ethereum.UInt256.ofNat
        (Ethereum.EVM.memoryExpansionCost
          (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)).toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamState3
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gbase ∧
  ¬ (truthParamState4
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamState5
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamState6
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamState7
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Ghigh ∧
  ¬ (truthParamPayableState8
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gjumpdest ∧
  ¬ (truthParamPayableState9
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gbase ∧
  ¬ (truthParamPayableState10
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamPayableState11
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gbase ∧
  ¬ (truthParamPayableState12
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamPayableState13
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamPayableState14
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Ghigh ∧
  ¬ (truthParamMismatchState15
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gbase ∧
  ¬ (truthParamMismatchState16
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamMismatchState17
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamMismatchState18
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamMismatchState19
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamMismatchState20
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamMismatchState21
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamMismatchState22
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamMismatchState23
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Ghigh ∧
  ¬ (truthParamMismatchState24
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gjumpdest ∧
  ¬ (truthParamMismatchState25
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gbase ∧
  ¬ (truthParamMismatchState26
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gbase

def truthMismatchGasCoverage : Prop :=
  ∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv),
    I.code = truthRuntimeBytecode →
    I.calldata.size < Ethereum.UInt256.size →
    I.weiValue = (⟨0⟩ : Ethereum.UInt256) →
    4 ≤ I.calldata.toList.length →
    I.calldata.extract 0 4 ≠ truthSelector →
      truthMismatchNoOOGConditions createdAccounts genesisBlockHeader blocks σ σ₀ g A I ∨
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .error .OutOfGass

def truthMismatchNoOOGTraceSemantics : Prop :=
  ∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv),
    I.code = truthRuntimeBytecode →
    I.calldata.size < Ethereum.UInt256.size →
    I.weiValue = (⟨0⟩ : Ethereum.UInt256) →
    4 ≤ I.calldata.toList.length →
    I.calldata.extract 0 4 ≠ truthSelector →
    truthMismatchNoOOGConditions createdAccounts genesisBlockHeader blocks σ σ₀ g A I →
      ∃ g' o,
        Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
          .ok (.revert g' o)

def truthBytecodeShortNoDispatchTraceSpec : Prop :=
  ∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv),
    I.code = truthRuntimeBytecode →
    I.calldata.size < Ethereum.UInt256.size →
    I.weiValue = (⟨0⟩ : Ethereum.UInt256) →
    I.calldata.toList.length < 4 →
      (∃ g' o,
        Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
          .ok (.revert g' o)) ∨
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .error .OutOfGass

def truthBytecodeSelectorMismatchTraceSpec : Prop :=
  ∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv),
    I.code = truthRuntimeBytecode →
    I.calldata.size < Ethereum.UInt256.size →
    I.weiValue = (⟨0⟩ : Ethereum.UInt256) →
    4 ≤ I.calldata.toList.length →
    I.calldata.extract 0 4 ≠ truthSelector →
      (∃ g' o,
        Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
          .ok (.revert g' o)) ∨
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .error .OutOfGass

def truthBytecodeTraceSpecs : Prop :=
  truthBytecodeSuccessTraceSpec ∧
  truthBytecodeNonpayableTraceSpec ∧
  truthBytecodeShortNoDispatchTraceSpec ∧
  truthBytecodeSelectorMismatchTraceSpec

def truthBytecodePendingTraceSpecs : Prop :=
  truthBytecodeSuccessTraceSpec ∧
  truthBytecodeShortNoDispatchTraceSpec ∧
  truthBytecodeSelectorMismatchTraceSpec

def truthBytecodeSuccessPathTraceSpec : Prop :=
  truthBytecodeSuccessTraceSpec

def truthBytecodeShortPathTraceSpec : Prop :=
  truthBytecodeShortNoDispatchTraceSpec

def truthBytecodeMismatchPathTraceSpec : Prop :=
  truthBytecodeSelectorMismatchTraceSpec

def truthBytecodeBranchSpecs : Prop :=
  truthBytecodeSuccessBranchSpec ∧
  truthBytecodeNonpayableBranchSpec ∧
  truthBytecodeNoDispatchBranchSpec ∧
  truthBytecodeDecodingFailedBranchSpec

axiom truth_short_gas_coverage :
    truthShortGasCoverage

axiom truth_success_gas_coverage :
    truthSuccessGasCoverage

theorem truth_fromBytes_append (xs ys : List UInt8) :
    Ethereum.fromBytes' (xs ++ ys) =
      Ethereum.fromBytes' xs + 2 ^ (8 * xs.length) * Ethereum.fromBytes' ys := by
  induction xs with
  | nil =>
      simp [Ethereum.fromBytes']
  | cons x xs ih =>
      simp only [List.cons_append, Ethereum.fromBytes', List.length_cons]
      rw [ih]
      ring_nf

theorem truth_selector_suffix_shiftRight (lo : List UInt8)
    (hlen : lo.length = 28) :
    (Ethereum.fromBytes' (lo ++ [0xd2, 0x51, 0x9f, 0x9e])) >>> 224 =
      2661241298 := by
  have hlo : Ethereum.fromBytes' lo < 2 ^ (8 * lo.length) := Ethereum.fromBytes'_le
  rw [hlen] at hlo
  norm_num at hlo
  rw [Nat.shiftRight_eq_div_pow]
  rw [truth_fromBytes_append]
  rw [hlen]
  norm_num [Ethereum.fromBytes']
  rw [show
      71746923462498742608690100707965704885390728604055333567275252212109691322368 =
        2661241298 *
          26959946667150639794667015087019630673637144422540572481103610249216 by
    norm_num]
  rw [Nat.add_mul_div_right _ _ (by norm_num)]
  rw [Nat.div_eq_of_lt hlo]

theorem truth_selector_prefix_of_extract (calldata : ByteArray)
    (h_selector : calldata.extract 0 4 = truthSelector) :
    calldata.data.toList.take 4 = [0x9e, 0x9f, 0x51, 0xd2] := by
  have hdata := congrArg ByteArray.data h_selector
  simp [truthSelector] at hdata
  simpa [Array.toList_extract] using congrArg Array.toList hdata

theorem truth_copySlice_0_32_size (calldata : ByteArray) :
    (calldata.copySlice 0 ByteArray.empty 0 32).size = min 32 calldata.size := by
  change (calldata.copySlice 0 ByteArray.empty 0 32).data.size =
    min 32 calldata.data.size
  simp only [ByteArray.data_copySlice, Array.size_append, Array.size_extract,
    Nat.zero_add, Nat.sub_zero]
  norm_num

theorem truth_readBytes_0_32_padding_size (calldata : ByteArray) :
    (OfNat.ofNat 32 -
        OfNat.ofNat (calldata.copySlice 0 ByteArray.empty 0 32).size : USize).toNat =
      32 - min 32 calldata.size := by
  have hcopy := truth_copySlice_0_32_size calldata
  rw [hcopy]
  have hmin : min 32 calldata.size ≤ 32 := Nat.min_le_left _ _
  have h32 : 32 < USize.size := by
    rcases System.Platform.numBits_eq with h | h <;> rw [USize.size, h] <;> norm_num
  have h32' : (OfNat.ofNat 32 : USize).toNat = 32 := by
    exact USize.toNat_ofNat_of_le_of_lt (n := 32) (i := 32) h32 le_rfl
  have hmin' :
      (OfNat.ofNat (min 32 calldata.size) : USize).toNat = min 32 calldata.size := by
    exact USize.toNat_ofNat_of_le_of_lt (n := 32) (i := min 32 calldata.size)
      h32 hmin
  rw [USize.toNat_sub_of_le]
  · rw [h32', hmin']
  · rw [USize.le_iff_toNat_le, h32', hmin']
    exact hmin

theorem truth_readBytes_0_32_toList (calldata : ByteArray) :
    (calldata.readBytes 0 32).data.toList =
      calldata.data.toList.take 32 ++ List.replicate (32 - min 32 calldata.size) 0 := by
  unfold ByteArray.readBytes
  simp [truth_byteArray_zeroes_eq, Array.toList_extract, truth_readBytes_0_32_padding_size]

theorem truth_take32_of_selector_prefix (xs : List UInt8)
    (htake4 : xs.take 4 = [0x9e, 0x9f, 0x51, 0xd2]) :
    xs.take 32 = [0x9e, 0x9f, 0x51, 0xd2] ++ (xs.drop 4).take 28 := by
  rw [← List.take_append_drop 4 xs, htake4]
  simp

theorem truth_selector_low_bytes_len (calldata : ByteArray)
    (hge4 : 4 ≤ calldata.size) :
    (List.replicate (32 - min 32 calldata.size) 0 ++
      ((calldata.data.toList.drop 4).take 28).reverse).length = 28 := by
  have hsize : calldata.data.toList.length = calldata.size := by
    rw [Array.length_toList]
    rfl
  simp only [List.length_append, List.length_replicate, List.length_reverse,
    List.length_take, List.length_drop]
  rw [hsize]
  omega

theorem truth_readBytes_0_32_selector_shape
    (calldata : ByteArray)
    (h_selector : calldata.extract 0 4 = truthSelector) :
    ∃ lo : List UInt8, lo.length = 28 ∧
      (calldata.readBytes 0 32).data.toList.reverse = lo ++ [0xd2, 0x51, 0x9f, 0x9e] := by
  have htake4 := truth_selector_prefix_of_extract calldata h_selector
  have hlen_take4 := congrArg List.length htake4
  simp only [List.length_take, List.length_cons, List.length_nil, Nat.reduceAdd] at hlen_take4
  have hsize : calldata.data.toList.length = calldata.size := by
    rw [Array.length_toList]
    rfl
  rw [hsize] at hlen_take4
  have hge4 : 4 ≤ calldata.size := by
    omega
  let lo := List.replicate (32 - min 32 calldata.size) 0 ++
    ((calldata.data.toList.drop 4).take 28).reverse
  refine ⟨lo, truth_selector_low_bytes_len calldata hge4, ?_⟩
  rw [truth_readBytes_0_32_toList, truth_take32_of_selector_prefix calldata.data.toList htake4]
  simp [lo, List.reverse_append, List.append_assoc]

theorem truth_selector_word_of_extract
    (calldata : ByteArray)
    (h_selector : calldata.extract 0 4 = truthSelector) :
    Ethereum.UInt256.shiftRight
        (Ethereum.uInt256OfByteArray (calldata.readBytes 0 32))
        (⟨0xe0⟩ : Ethereum.UInt256) =
      truthExpectedSelectorWord := by
  rcases truth_readBytes_0_32_selector_shape calldata h_selector with ⟨lo, hlen, hshape⟩
  let bs : List UInt8 := lo ++ [0xd2, 0x51, 0x9f, 0x9e]
  let n : Nat := Ethereum.fromBytes' bs
  have hbs : bs = lo ++ [0xd2, 0x51, 0x9f, 0x9e] := rfl
  have hn : n = Ethereum.fromBytes' bs := rfl
  have hlen32 : bs.length = 32 := by
    simp [bs, hlen]
  have hlt : n < Ethereum.UInt256.size := by
    have h := Ethereum.fromBytes'_le (bs := bs)
    rw [hlen32] at h
    simpa [n, Ethereum.UInt256.size] using h
  have hsuffix : n >>> 224 = 2661241298 := by
    rw [hn, hbs]
    exact truth_selector_suffix_shiftRight lo hlen
  unfold Ethereum.uInt256OfByteArray Ethereum.UInt256.shiftRight truthExpectedSelectorWord
    Ethereum.UInt256.ofNat
  simp only [hshape, Id.run, ← hbs, ← hn]
  have hshift : ¬ ((OfNat.ofNat 224 : Fin Ethereum.UInt256.size) ≥
      (OfNat.ofNat 256 : Fin Ethereum.UInt256.size)) := by
    native_decide
  rw [if_neg hshift]
  congr
  apply Fin.ext
  have hval :
      Fin.val ((Fin.ofNat Ethereum.UInt256.size n : Fin Ethereum.UInt256.size) >>>
        (OfNat.ofNat 224 : Fin Ethereum.UInt256.size)) =
      (Nat.shiftRight (n % Ethereum.UInt256.size) ((224 : Nat) % Ethereum.UInt256.size)) %
        Ethereum.UInt256.size := rfl
  rw [hval]
  rw [Nat.mod_eq_of_lt hlt]
  rw [show (224 % Ethereum.UInt256.size) = 224 by norm_num [Ethereum.UInt256.size]]
  change (n >>> 224) % Ethereum.UInt256.size = (2661241298 : Nat)
  rw [hsuffix]
  norm_num [Ethereum.UInt256.size]

theorem truth_selector_eq_word_one_of_selector
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_selector : I.calldata.extract 0 4 = truthSelector) :
    truthParamMismatchSelectorEqWord
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
      (⟨1⟩ : Ethereum.UInt256) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hcalldata :
      (truthParamMismatchState16 s).executionEnv.calldata = I.calldata := by
    simp [s, truthFreshState, truthParamState1, truthParamState2, truthParamState3,
      truthParamState4, truthParamState5, truthParamState6, truthParamState7,
      truthParamPayableState8, truthParamPayableState9, truthParamPayableState10,
      truthParamPayableState11, truthParamPayableState12, truthParamPayableState13,
      truthParamPayableState14, truthParamMismatchState15, truthParamMismatchState16]
  have hword :
      truthParamMismatchSelectorWord s = truthExpectedSelectorWord := by
    unfold truthParamMismatchSelectorWord truthParamMismatchCalldataWord
    rw [hcalldata]
    exact truth_selector_word_of_extract I.calldata h_selector
  unfold truthParamMismatchSelectorEqWord
  rw [hword]
  simp [Ethereum.UInt256.eq, Ethereum.UInt256.ofNat, Id.run]
  native_decide

theorem truth_success_prefix_guards_of_no_oog
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_no_oog :
      truthSuccessNoOOGConditions createdAccounts genesisBlockHeader blocks σ σ₀ g A I) :
  ¬ g.toNat < GasConstants.Gverylow ∧
  ¬ (truthParamState1
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamState2
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    Ethereum.EVM.memoryExpansionCost
      (truthParamState2
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE ∧
  ¬ ((truthParamState2
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
      Ethereum.UInt256.ofNat
        (Ethereum.EVM.memoryExpansionCost
          (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)).toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamState3
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gbase ∧
  ¬ (truthParamState4
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamState5
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamState6
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamState7
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Ghigh ∧
  ¬ (truthParamPayableState8
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gjumpdest ∧
  ¬ (truthParamPayableState9
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gbase ∧
  ¬ (truthParamPayableState10
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamPayableState11
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gbase ∧
  ¬ (truthParamPayableState12
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamPayableState13
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamPayableState14
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Ghigh ∧
  ¬ (truthParamMismatchState15
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gbase ∧
  ¬ (truthParamMismatchState16
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamMismatchState17
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamMismatchState18
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamMismatchState19
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamMismatchState20
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamMismatchState21
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamMismatchState22
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Gverylow ∧
  ¬ (truthParamMismatchState23
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
    GasConstants.Ghigh := by
  simpa [truthSuccessNoOOGConditions, truthSuccessPrefixNoOOGGuards] using h_no_oog.2

axiom truth_success_body_X_trace_of_no_oog
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode)
    (h_bound : I.calldata.size < Ethereum.UInt256.size)
    (h_no_oog :
      truthSuccessNoOOGConditions createdAccounts genesisBlockHeader blocks σ σ₀ g A I) :
    ∃ s',
      s'.createdAccounts = createdAccounts ∧
      s'.accountMap = σ ∧
      s'.substate = A ∧
      Ethereum.EVM.X (g.toNat - 23) (Ethereum.EVM.D_J I.code ⟨0⟩)
          (truthParamSuccessState24
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
        .ok (.success s' truthReturnData)

axiom truth_mismatch_gas_coverage :
    truthMismatchGasCoverage

axiom truth_selector_eq_word_zero_of_selector_ne
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_selector_ne : I.calldata.extract 0 4 ≠ truthSelector) :
    truthParamMismatchSelectorEqWord
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
      (⟨0⟩ : Ethereum.UInt256)

theorem truth_success_no_oog_trace_semantics_from_body_trace
    (h_body_trace :
      ∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
        (genesisBlockHeader : Ethereum.BlockHeader)
        (blocks : Ethereum.ProcessedBlocks)
        (σ σ₀ : Ethereum.AccountMap)
        (g : Ethereum.UInt256)
        (A : Ethereum.Substate)
        (I : Ethereum.ExecutionEnv),
        I.code = truthRuntimeBytecode →
        I.calldata.size < Ethereum.UInt256.size →
        truthSuccessNoOOGConditions createdAccounts genesisBlockHeader blocks σ σ₀ g A I →
          ∃ s',
            s'.createdAccounts = createdAccounts ∧
            s'.accountMap = σ ∧
            s'.substate = A ∧
            Ethereum.EVM.X (g.toNat - 23) (Ethereum.EVM.D_J I.code ⟨0⟩)
                (truthParamSuccessState24
                  (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
              .ok (.success s' truthReturnData)) :
    truthSuccessNoOOGTraceSemantics := by
  intro createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code h_bound h_value h_selector
    h_len h_no_oog
  rcases truth_success_prefix_guards_of_no_oog createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I h_no_oog with
    ⟨h0, h2, h4mem, h4gas, h5, h6, h7, h8, h10, h14, h15, h16,
      h18, h19, h20, h22, h23, h24, h25, h27, h28, h29, h34, h35, h37⟩
  rcases h_body_trace createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I h_code h_bound h_no_oog with
    ⟨s', h_createdAccounts, h_accountMap, h_substate, h_body⟩
  refine ⟨s'.machineState.gasAvailable, ?_⟩
  apply truth_Xi_success_of_X_fresh_success createdAccounts genesisBlockHeader blocks
    σ σ₀ g A I s' truthReturnData h_createdAccounts h_accountMap h_substate
  have h0step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
          .ok (truthParamState1
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc0 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h0]
  have h2step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState1
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState2
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc2 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h2]
  have h4step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState2
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState3
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc4 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h4mem, if_neg h4gas]
  have h5step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState3
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState4
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc5 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h5]
  have h6step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState4
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState5
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc6 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h6]
  have h7step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState5
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState6
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc7 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h7]
  have h8step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState6
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamState7
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_xstep_pc8 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h8]
  have h10step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamState7
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState8
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_payable_xstep_pc10 createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      h_code h_value]
    rw [if_neg h10]
  have h14step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState8
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState9
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_payable_xstep_pc14 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h14]
  have h15step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState9
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState10
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_payable_xstep_pc15 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h15]
  have h16step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState10
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState11
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_payable_xstep_pc16 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h16]
  have h18step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState11
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState12
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_payable_xstep_pc18 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h18]
  have h19step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState12
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState13
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_payable_xstep_pc19 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h19]
  have h20step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState13
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamPayableState14
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_payable_xstep_pc20 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h20]
  have h22step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamPayableState14
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState15
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_mismatch_xstep_pc22 createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      h_code (truth_calldata_size_word_of_not_short_of_uint256_bound I.calldata h_len h_bound)]
    rw [if_neg h22]
  have h23step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState15
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState16
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_mismatch_xstep_pc23 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h23]
  have h24step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState16
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState17
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_mismatch_xstep_pc24 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h24]
  have h25step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState17
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState18
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_mismatch_xstep_pc25 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h25]
  have h27step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState18
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState19
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_mismatch_xstep_pc27 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h27]
  have h28step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState19
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState20
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_mismatch_xstep_pc28 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h28]
  have h29step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState20
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState21
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_mismatch_xstep_pc29 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h29]
  have h34step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState21
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState22
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_mismatch_xstep_pc34 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h34]
  have h35step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState22
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamMismatchState23
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_mismatch_xstep_pc35 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg h35]
  have h37step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamMismatchState23
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
          .ok (truthParamSuccessState24
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_success_xstep_pc37 createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      h_code (truth_selector_eq_word_one_of_selector createdAccounts genesisBlockHeader blocks
        σ σ₀ g A I h_selector)]
    rw [if_neg h37]
  have hfuel : g.toNat + 1 = (g.toNat - 23) + 24 := by
    have h_fuel : 92 ≤ g.toNat := h_no_oog.1
    omega
  rw [hfuel]
  truth_continue_step h0step
  truth_continue_step h2step
  truth_continue_step h4step
  truth_continue_step h5step
  truth_continue_step h6step
  truth_continue_step h7step
  truth_continue_step h8step
  truth_continue_step h10step
  truth_continue_step h14step
  truth_continue_step h15step
  truth_continue_step h16step
  truth_continue_step h18step
  truth_continue_step h19step
  truth_continue_step h20step
  truth_continue_step h22step
  truth_continue_step h23step
  truth_continue_step h24step
  truth_continue_step h25step
  truth_continue_step h27step
  truth_continue_step h28step
  truth_continue_step h29step
  truth_continue_step h34step
  truth_continue_step h35step
  truth_continue_step h37step
  exact h_body

theorem truth_success_no_oog_trace_semantics :
    truthSuccessNoOOGTraceSemantics :=
  truth_success_no_oog_trace_semantics_from_body_trace
    truth_success_body_X_trace_of_no_oog

theorem truth_mismatch_no_oog_trace_semantics :
    truthMismatchNoOOGTraceSemantics := by
  intro createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code h_bound h_value h_len
    h_selector_ne h_no_oog
  rcases h_no_oog with
    ⟨h_fuel, h0, h2, h4mem, h4gas, h5, h6, h7, h8, h10, h14, h15, h16,
      h18, h19, h20, h22, h23, h24, h25, h27, h28, h29, h34, h35, h37,
      h38, h39, h40⟩
  refine ⟨(truthParamMismatchState28
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable,
    truthParamMismatchReturnData
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), ?_⟩
  exact truth_fresh_mismatch_Xi_revert_of_no_oog createdAccounts genesisBlockHeader blocks
    σ σ₀ g A I h_code h_value h_fuel
    (truth_calldata_size_word_of_not_short_of_uint256_bound I.calldata h_len h_bound)
    (truth_selector_eq_word_zero_of_selector_ne createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I h_selector_ne)
    h0 h2 h4mem h4gas h5 h6 h7 h8 h10 h14 h15 h16 h18 h19 h20 h22
    h23 h24 h25 h27 h28 h29 h34 h35 h37 h38 h39 h40

theorem truth_bytecode_success_path_trace_spec :
    truthBytecodeSuccessPathTraceSpec := by
  intro createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code h_bound h_value h_selector h_len
  rcases truth_success_gas_coverage createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      h_code h_bound h_value h_selector h_len with h_no_oog | h_oog
  · left
    exact truth_success_no_oog_trace_semantics createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I h_code h_bound h_value h_selector h_len h_no_oog
  · right
    exact h_oog

theorem truth_bytecode_short_path_trace_spec :
    truthBytecodeShortPathTraceSpec := by
  intro createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code h_bound h_value h_short
  rcases truth_short_gas_coverage createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      h_code h_bound h_value h_short with h_no_oog | h_oog
  · left
    rcases h_no_oog with
      ⟨h_fuel, h0, h2, h4mem, h4gas, h5, h6, h7, h8, h10, h14, h15, h16,
        h18, h19, h20, h22, h38, h39, h40⟩
    refine ⟨(truthParamShortState19
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable,
      truthParamShortReturnData
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), ?_⟩
    exact truth_fresh_short_Xi_revert_of_no_oog createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I h_code h_value h_short h_fuel h0 h2 h4mem h4gas h5 h6 h7 h8 h10
      h14 h15 h16 h18 h19 h20 h22 h38 h39 h40
  · right
    exact h_oog

theorem truth_bytecode_mismatch_path_trace_spec :
    truthBytecodeMismatchPathTraceSpec := by
  intro createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code h_bound h_value h_len h_selector_ne
  rcases truth_mismatch_gas_coverage createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      h_code h_bound h_value h_len h_selector_ne with h_no_oog | h_oog
  · left
    exact truth_mismatch_no_oog_trace_semantics createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I h_code h_bound h_value h_len h_selector_ne h_no_oog
  · right
    exact h_oog

theorem truth_bytecode_pending_trace_specs :
    truthBytecodePendingTraceSpecs :=
  ⟨truth_bytecode_success_path_trace_spec,
    truth_bytecode_short_path_trace_spec,
    truth_bytecode_mismatch_path_trace_spec⟩

theorem truth_bytecode_success_trace_spec :
    truthBytecodeSuccessTraceSpec :=
  truth_bytecode_pending_trace_specs.1

axiom truth_Xi_never_outOfFuel
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I ≠
      .error .OutOfFuel

axiom truth_nonpayable_low_fuel_guard_coverage_of_no_outOfFuel :
    truthNonpayableLowFuelGuardCoverageOfNoOutOfFuel

theorem truth_nonpayable_low_fuel_guard_coverage :
    truthNonpayableLowFuelGuardCoverage := by
  intro createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code h_value h_low_fuel
  exact truth_nonpayable_low_fuel_guard_coverage_of_no_outOfFuel createdAccounts
    genesisBlockHeader blocks σ σ₀ g A I h_code h_value h_low_fuel
    (truth_Xi_never_outOfFuel createdAccounts genesisBlockHeader blocks σ σ₀ g A I)

theorem truth_nonpayable_guard_coverage :
    truthNonpayableGuardCoverage := by
  intro createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code h_value
  by_cases h_fuel : 10 ≤ g.toNat
  · exact truth_nonpayable_guard_coverage_of_enough_fuel createdAccounts genesisBlockHeader
      blocks σ σ₀ g A I h_fuel
  · have h_low_fuel : g.toNat < 10 := Nat.lt_of_not_ge h_fuel
    exact truth_nonpayable_low_fuel_guard_coverage createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I h_code h_value h_low_fuel

theorem truth_nonpayable_gas_coverage :
    truthNonpayableGasCoverage := by
  intro createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code h_value
  cases truth_nonpayable_guard_coverage createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      h_code h_value with
  | noOOG h_no_oog =>
      exact Or.inl h_no_oog
  | pc0 h0 =>
      exact Or.inr (truth_fresh_nonpayable_Xi_outOfGas_at_pc0 createdAccounts
        genesisBlockHeader blocks σ σ₀ g A I h_code h0)
  | pc2 h0 h2 =>
      exact Or.inr (truth_fresh_nonpayable_Xi_outOfGas_at_pc2 createdAccounts
        genesisBlockHeader blocks σ σ₀ g A I h_code h0 h2)
  | pc4_memory h0 h2 h4mem =>
      exact Or.inr (truth_fresh_nonpayable_Xi_outOfGas_at_pc4_memory createdAccounts
        genesisBlockHeader blocks σ σ₀ g A I h_code h0 h2 h4mem)
  | pc4_gas h0 h2 h4mem h4gas =>
      exact Or.inr (truth_fresh_nonpayable_Xi_outOfGas_at_pc4_gas createdAccounts
        genesisBlockHeader blocks σ σ₀ g A I h_code h0 h2 h4mem h4gas)
  | pc5 h0 h2 h4mem h4gas h5 =>
      exact Or.inr (truth_fresh_nonpayable_Xi_outOfGas_at_pc5 createdAccounts
        genesisBlockHeader blocks σ σ₀ g A I h_code h0 h2 h4mem h4gas h5)
  | pc6 h_fuel h0 h2 h4mem h4gas h5 h6 =>
      exact Or.inr (truth_fresh_nonpayable_Xi_outOfGas_at_pc6 createdAccounts
        genesisBlockHeader blocks σ σ₀ g A I h_code h_fuel h0 h2 h4mem h4gas h5 h6)
  | pc7 h_fuel h0 h2 h4mem h4gas h5 h6 h7 =>
      exact Or.inr (truth_fresh_nonpayable_Xi_outOfGas_at_pc7 createdAccounts
        genesisBlockHeader blocks σ σ₀ g A I h_code h_fuel h0 h2 h4mem h4gas h5 h6 h7)
  | pc8 h_fuel h0 h2 h4mem h4gas h5 h6 h7 h8 =>
      exact Or.inr (truth_fresh_nonpayable_Xi_outOfGas_at_pc8 createdAccounts
        genesisBlockHeader blocks σ σ₀ g A I h_code h_fuel h0 h2 h4mem h4gas h5 h6 h7 h8)
  | pc10 h_fuel h0 h2 h4mem h4gas h5 h6 h7 h8 h10 =>
      exact Or.inr (truth_fresh_nonpayable_Xi_outOfGas_at_pc10 createdAccounts
        genesisBlockHeader blocks σ σ₀ g A I h_code h_value h_fuel h0 h2 h4mem h4gas h5 h6 h7 h8 h10)
  | pc11 h_fuel h0 h2 h4mem h4gas h5 h6 h7 h8 h10 h11 =>
      exact Or.inr (truth_fresh_nonpayable_Xi_outOfGas_at_pc11 createdAccounts
        genesisBlockHeader blocks σ σ₀ g A I h_code h_value h_fuel h0 h2 h4mem h4gas h5 h6 h7 h8 h10 h11)
  | pc12 h_fuel h0 h2 h4mem h4gas h5 h6 h7 h8 h10 h11 h12 =>
      exact Or.inr (truth_fresh_nonpayable_Xi_outOfGas_at_pc12 createdAccounts
        genesisBlockHeader blocks σ σ₀ g A I h_code h_value h_fuel h0 h2 h4mem h4gas h5 h6 h7 h8 h10 h11 h12)

theorem truth_bytecode_nonpayable_trace_spec :
    truthBytecodeNonpayableTraceSpec := by
  intro createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code h_bound h_value
  rcases truth_nonpayable_gas_coverage createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      h_code h_value with h_no_oog | h_oog
  · left
    rcases h_no_oog with
      ⟨h_fuel, h0, h2, h4mem, h4gas, h5, h6, h7, h8, h10, h11, h12⟩
    refine ⟨(truthParamNonpayableState11
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable,
      truthParamNonpayableReturnData
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), ?_⟩
    exact truth_fresh_nonpayable_Xi_revert_of_no_oog createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I h_code h_value h_fuel h0 h2 h4mem h4gas h5 h6 h7 h8 h10 h11 h12
  · right
    exact h_oog

theorem truth_bytecode_short_no_dispatch_trace_spec :
    truthBytecodeShortNoDispatchTraceSpec :=
  truth_bytecode_pending_trace_specs.2.1

theorem truth_bytecode_selector_mismatch_trace_spec :
    truthBytecodeSelectorMismatchTraceSpec :=
  truth_bytecode_pending_trace_specs.2.2

theorem truth_bytecode_trace_specs :
    truthBytecodeTraceSpecs :=
  ⟨truth_bytecode_success_trace_spec,
    truth_bytecode_nonpayable_trace_spec,
    truth_bytecode_short_no_dispatch_trace_spec,
    truth_bytecode_selector_mismatch_trace_spec⟩

theorem truth_bytecode_success_branch_spec_from_trace_spec
    (h_trace : truthBytecodeSuccessTraceSpec) :
    truthBytecodeSuccessBranchSpec := by
  intro createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code h_bound h_value h_dispatch h_decode
  have h_selector : I.calldata.extract 0 4 = truthSelector :=
    truth_selector_of_dispatch I.calldata h_dispatch
  have h_len : 4 ≤ I.calldata.toList.length :=
    truth_calldata_length_of_selector I.calldata h_selector
  exact h_trace createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code h_bound h_value h_selector h_len

theorem truth_bytecode_nonpayable_branch_spec_from_trace_spec
    (h_trace : truthBytecodeNonpayableTraceSpec) :
    truthBytecodeNonpayableBranchSpec := by
  intro createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code h_bound h_value h_dispatch h_decode
  exact h_trace createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code h_bound h_value

theorem truth_bytecode_no_dispatch_branch_spec_from_trace_specs
    (h_nonpayable : truthBytecodeNonpayableTraceSpec)
    (h_short : truthBytecodeShortNoDispatchTraceSpec)
    (h_mismatch : truthBytecodeSelectorMismatchTraceSpec) :
    truthBytecodeNoDispatchBranchSpec := by
  intro createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code h_bound h_dispatch
  by_cases h_value_ne : I.weiValue.val ≠ 0
  · exact h_nonpayable createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code h_bound h_value_ne
  · have h_value : I.weiValue = (⟨0⟩ : Ethereum.UInt256) :=
      truth_uint256_eq_zero_of_not_val_ne_zero I.weiValue h_value_ne
    by_cases hshort : I.calldata.toList.length < 4
    · exact h_short createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code h_bound h_value hshort
    · have h_len : 4 ≤ I.calldata.toList.length := Nat.le_of_not_gt hshort
      have h_selector_ne : I.calldata.extract 0 4 ≠ truthSelector := by
        intro h_selector
        have h_dispatch_some :
            dispatchMsg truthContract I.calldata = some truthTransition :=
          truth_dispatch_of_selector I.calldata h_selector
        rw [h_dispatch_some] at h_dispatch
        cases h_dispatch
      exact h_mismatch createdAccounts genesisBlockHeader blocks σ σ₀ g A I
        h_code h_bound h_value h_len h_selector_ne

theorem truth_bytecode_decoding_failed_branch_spec :
    truthBytecodeDecodingFailedBranchSpec := by
  intro createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code h_bound h_dispatch h_decode
  have h_selector : I.calldata.extract 0 4 = truthSelector :=
    truth_selector_of_dispatch I.calldata h_dispatch
  have h_len : 4 ≤ I.calldata.toList.length :=
    truth_calldata_length_of_selector I.calldata h_selector
  have h_decode_some : decodeCalldata [] [] I.calldata = some (∅ : Store) :=
    truth_decode_no_args_of_calldata_length I.calldata h_len
  rw [h_decode_some] at h_decode
  cases h_decode

theorem truth_bytecode_branch_specs_from_trace_specs
    (h_specs : truthBytecodeTraceSpecs) :
    truthBytecodeBranchSpecs := by
  rcases h_specs with ⟨h_success, h_nonpayable, h_short, h_mismatch⟩
  exact
    ⟨truth_bytecode_success_branch_spec_from_trace_spec h_success,
      truth_bytecode_nonpayable_branch_spec_from_trace_spec h_nonpayable,
      truth_bytecode_no_dispatch_branch_spec_from_trace_specs h_nonpayable h_short h_mismatch,
      truth_bytecode_decoding_failed_branch_spec⟩

theorem truth_bytecode_branch_specs :
    truthBytecodeBranchSpecs :=
  truth_bytecode_branch_specs_from_trace_specs truth_bytecode_trace_specs

theorem truth_bytecode_semantic_spec_from_branch_specs
    (h_specs : truthBytecodeBranchSpecs) :
    truthBytecodeSemanticSpec
:= by
  intro createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code h_bound
  rcases h_specs with ⟨h_success, h_nonpayable, h_noDispatch, h_decodingFailed⟩
  rcases truth_dispatch_cases I.calldata with h_dispatch | h_dispatch
  · rcases truth_decode_no_args_cases I.calldata with h_decode | h_decode
    · by_cases h_value : I.weiValue = (⟨0⟩ : Ethereum.UInt256)
      · rcases h_success createdAccounts genesisBlockHeader blocks σ σ₀ g A I
            h_code h_bound h_value h_dispatch h_decode with ⟨g', h_evm⟩ | h_evm
        · exact Or.inl ⟨g', h_value, h_dispatch, h_decode, h_evm⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr h_evm)))
      · have h_value_val : I.weiValue.val ≠ 0 :=
          truth_uint256_val_ne_zero_of_ne_zero I.weiValue h_value
        rcases h_nonpayable createdAccounts genesisBlockHeader blocks σ σ₀ g A I
            h_code h_bound h_value_val h_dispatch h_decode with ⟨g', o, h_evm⟩ | h_evm
        · exact Or.inr (Or.inl ⟨g', o, h_value_val, h_dispatch, h_decode, h_evm⟩)
        · exact Or.inr (Or.inr (Or.inr (Or.inr h_evm)))
    · rcases h_decodingFailed createdAccounts genesisBlockHeader blocks σ σ₀ g A I
          h_code h_bound h_dispatch h_decode with ⟨g', o, h_evm⟩ | h_evm
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨g', o, truthTransition, transitionSignature truthTransition, h_dispatch, rfl,
            h_decode, h_evm⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h_evm)))
  · rcases h_noDispatch createdAccounts genesisBlockHeader blocks σ σ₀ g A I
        h_code h_bound h_dispatch with ⟨g', o, h_evm⟩ | h_evm
    · exact Or.inr (Or.inr (Or.inl ⟨g', o, h_dispatch, h_evm⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h_evm)))

theorem truth_bytecode_semantic_spec :
    truthBytecodeSemanticSpec :=
  truth_bytecode_semantic_spec_from_branch_specs truth_bytecode_branch_specs

theorem truth_bytecode_covers_runtime_cases_from_semantic_spec
    (h_spec : truthBytecodeSemanticSpec) :
    truthBytecodeCoversRuntimeCases := by
  intro createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code h_bound
  rcases h_spec createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code h_bound with
      ⟨g', h_value, h_dispatch, h_decode, h_evm⟩
    | ⟨g', o, h_value, h_dispatch, h_decode, h_evm⟩
    | ⟨g', o, h_dispatch, h_evm⟩
    | ⟨g', o, transition, transitionSig, h_dispatch, h_sig, h_decode, h_evm⟩
    | h_evm
  · exact truthRuntimeCase.success g' h_value h_dispatch h_decode h_evm
  · exact truthRuntimeCase.nonpayable g' o h_value h_dispatch h_decode h_evm
  · exact truthRuntimeCase.noDispatch g' o h_dispatch h_evm
  · exact truthRuntimeCase.decodingFailed g' o transition transitionSig h_dispatch h_sig h_decode
      h_evm
  · exact truthRuntimeCase.outOfGas h_evm

theorem truth_bytecode_covers_runtime_cases :
    truthBytecodeCoversRuntimeCases :=
  truth_bytecode_covers_runtime_cases_from_semantic_spec truth_bytecode_semantic_spec

theorem truth_runtimeEquivalence_from_bytecode_coverage
    (h_coverage : truthBytecodeCoversRuntimeCases) :
    runtimeEquivalence!?! truthConfig truthRuntimeBytecode truthContract := by
  apply runtimeEquivalence!?!.intro
  intro createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code h_bound
  exact truthRuntimeCase.runtimeEquivalenceFor
    createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code
    (h_coverage createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code h_bound)

theorem truth_all_traces_cases
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (h_code : I.code = truthRuntimeBytecode)
    (h_bound : I.calldata.size < Ethereum.UInt256.size) :
    truthRuntimeCase createdAccounts genesisBlockHeader blocks σ σ₀ g A I :=
  truth_bytecode_covers_runtime_cases createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    h_code h_bound

theorem truth_runtimeEquivalence_from_base_trace_axiom :
    runtimeEquivalence!?! truthConfig truthRuntimeBytecode truthContract :=
  truth_runtimeEquivalence_from_bytecode_coverage truth_bytecode_covers_runtime_cases

end Truth
end Examples
end Act
