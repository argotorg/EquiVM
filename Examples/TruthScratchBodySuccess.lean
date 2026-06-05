import Examples.TruthScratchTailSuccess

set_option maxRecDepth 100000

namespace Act
namespace Examples
namespace Truth

theorem truth_success_dispatch_tail_X_state24_to_state35_of_gas_guards
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (f : Nat)
    (xres : Except Ethereum.EVM.ExecutionException (Ethereum.ExecutionResult EVM.State))
    (h_code : I.code = truthRuntimeBytecode)
    (hgas42 :
      ¬ (truthParamSuccessState24
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gjumpdest)
    (hgas43 :
      ¬ (truthParamSuccessState25
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas45 :
      ¬ (truthParamSuccessState26
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas47 :
      ¬ (truthParamSuccessState27
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gmid)
    (hgas68 :
      ¬ (truthParamSuccessState28
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gjumpdest)
    (hgas69 :
      ¬ (truthParamSuccessState29
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gbase)
    (hgas70 :
      ¬ (truthParamSuccessState30
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas72 :
      ¬ (truthParamSuccessState31
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas73 :
      ¬ (truthParamSuccessState32
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gbase)
    (hgas74 :
      ¬ (truthParamSuccessState33
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas75 :
      ¬ (truthParamSuccessState34
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gmid)
    (htail :
      Ethereum.EVM.X f (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamSuccessState35
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) = xres) :
    Ethereum.EVM.X (f + 11) (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamSuccessState24
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) = xres := by
  have h42step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
          (truthParamSuccessState24
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
        .ok (truthParamSuccessState25
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_success_xstep_pc42 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg hgas42]
  have h43step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
          (truthParamSuccessState25
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
        .ok (truthParamSuccessState26
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_success_xstep_pc43 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg hgas43]
  have h45step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
          (truthParamSuccessState26
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
        .ok (truthParamSuccessState27
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_success_xstep_pc45 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg hgas45]
  have h47step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
          (truthParamSuccessState27
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
        .ok (truthParamSuccessState28
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_success_xstep_pc47 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg hgas47]
  have h68step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
          (truthParamSuccessState28
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
        .ok (truthParamSuccessState29
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_success_xstep_pc68 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg hgas68]
  have h69step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
          (truthParamSuccessState29
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
        .ok (truthParamSuccessState30
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_success_xstep_pc69 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg hgas69]
  have h70step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
          (truthParamSuccessState30
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
        .ok (truthParamSuccessState31
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_success_xstep_pc70 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg hgas70]
  have h72step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
          (truthParamSuccessState31
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
        .ok (truthParamSuccessState32
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_success_xstep_pc72 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg hgas72]
  have h73step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
          (truthParamSuccessState32
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
        .ok (truthParamSuccessState33
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_success_xstep_pc73 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg hgas73]
  have h74step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
          (truthParamSuccessState33
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
        .ok (truthParamSuccessState34
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_success_xstep_pc74 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg hgas74]
  have h75step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
          (truthParamSuccessState34
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
        .ok (truthParamSuccessState35
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I), .none) := by
    rw [truth_fresh_success_xstep_pc75 createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code]
    rw [if_neg hgas75]
  have hf :
      f + 11 = (((((((((((f + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) := by
    omega
  rw [hf]
  truth_continue_step h42step
  truth_continue_step h43step
  truth_continue_step h45step
  truth_continue_step h47step
  truth_continue_step h68step
  truth_continue_step h69step
  truth_continue_step h70step
  truth_continue_step h72step
  truth_continue_step h73step
  truth_continue_step h74step
  truth_continue_step h75step
  exact htail

theorem truth_success_body_X_state35_to_success_of_gas_guards
    (s : EVM.State)
    (f : Nat)
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
    Ethereum.EVM.X (f + 58) (Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩)
        (truthParamSuccessState35 s) =
      .ok (.success (truthParamSuccessState93 s) (truthParamSuccessFinalReturnData s)) := by
  have h73 :
      Ethereum.EVM.X (f + 20) (Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩)
          (truthParamSuccessState73 s) =
        .ok (.success (truthParamSuccessState93 s) (truthParamSuccessFinalReturnData s)) :=
    truth_success_return_tail_X_of_gas_guards s f h_code
      hgas94 hgas95 hmem96 hgas96 hgas97 hgas98 hgas99
      hgas117 hgas118 hgas119 hgas120 hgas121 hgas122
      hgas59 hgas60 hmem62 hgas62 hgas63 hgas64 hgas65 hgas66 hmem67
  have h62 :
      Ethereum.EVM.X ((f + 20) + 11) (Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩)
          (truthParamSuccessState62 s) =
        .ok (.success (truthParamSuccessState93 s) (truthParamSuccessFinalReturnData s)) :=
    truth_success_tail_X_pc76_to_pc86_of_gas_guards s (f + 20)
      (.ok (.success (truthParamSuccessState93 s) (truthParamSuccessFinalReturnData s)))
      h_code hgas76 hgas77 hgas78 hgas79 hgas80 hgas81 hgas82 hgas83 hgas84 hgas85 hgas86 h73
  have h57 :
      Ethereum.EVM.X (((f + 20) + 11) + 5) (Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩)
          (truthParamSuccessState57 s) =
        .ok (.success (truthParamSuccessState93 s) (truthParamSuccessFinalReturnData s)) :=
    truth_success_tail_X_pc87_to_pc93_of_gas_guards s ((f + 20) + 11)
      (.ok (.success (truthParamSuccessState93 s) (truthParamSuccessFinalReturnData s)))
      h_code hgas87 hgas88 hgas90 hgas91 hgas93 h62
  have h50 :
      Ethereum.EVM.X ((((f + 20) + 11) + 5) + 7)
          (Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩)
          (truthParamSuccessState50 s) =
        .ok (.success (truthParamSuccessState93 s) (truthParamSuccessFinalReturnData s)) :=
    truth_success_tail_X_pc108_to_pc116_of_gas_guards s (((f + 20) + 11) + 5)
      (.ok (.success (truthParamSuccessState93 s) (truthParamSuccessFinalReturnData s)))
      h_code hgas108 hgas110 hgas111 hgas112 hgas113 hgas114 hgas116 h57
  have h43 :
      Ethereum.EVM.X (((((f + 20) + 11) + 5) + 7) + 7)
          (Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩)
          (truthParamSuccessState43 s) =
        .ok (.success (truthParamSuccessState93 s) (truthParamSuccessFinalReturnData s)) :=
    truth_success_tail_X_pc100_to_pc107_of_gas_guards s ((((f + 20) + 11) + 5) + 7)
      (.ok (.success (truthParamSuccessState93 s) (truthParamSuccessFinalReturnData s)))
      h_code hgas100 hgas101 hgas102 hgas104 hgas105 hgas106 hgas107 h50
  have h35 :
      Ethereum.EVM.X ((((((f + 20) + 11) + 5) + 7) + 7) + 8)
          (Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩)
          (truthParamSuccessState35 s) =
        .ok (.success (truthParamSuccessState93 s) (truthParamSuccessFinalReturnData s)) :=
    truth_success_X_pc48_to_pc58_of_gas_guards s (((((f + 20) + 11) + 5) + 7) + 7)
      (.ok (.success (truthParamSuccessState93 s) (truthParamSuccessFinalReturnData s)))
      h_code hgas48 hgas49 hgas51_mem hgas51_op hgas52 hgas54 hgas55 hgas56 hgas58 h43
  have hf : f + 58 = ((((((f + 20) + 11) + 5) + 7) + 7) + 8) := by
    omega
  rw [hf]
  exact h35

theorem truth_success_body_X_state24_to_success_of_gas_guards
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (f : Nat)
    (h24_35 :
      ∀ (xres : Except Ethereum.EVM.ExecutionException (Ethereum.ExecutionResult EVM.State)),
        Ethereum.EVM.X (f + 58) (Ethereum.EVM.D_J I.code ⟨0⟩)
            (truthParamSuccessState35
              (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) = xres →
        Ethereum.EVM.X ((f + 58) + 11) (Ethereum.EVM.D_J I.code ⟨0⟩)
            (truthParamSuccessState24
              (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) = xres)
    (h35_success :
      Ethereum.EVM.X (f + 58) (Ethereum.EVM.D_J I.code ⟨0⟩)
          (truthParamSuccessState35
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
        .ok (.success
          (truthParamSuccessState93
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))
          (truthParamSuccessFinalReturnData
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)))) :
    Ethereum.EVM.X (f + 69) (Ethereum.EVM.D_J I.code ⟨0⟩)
        (truthParamSuccessState24
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
      .ok (.success
        (truthParamSuccessState93
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))
        (truthParamSuccessFinalReturnData
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))) := by
  have htail := h24_35
    (.ok (.success
      (truthParamSuccessState93
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))
      (truthParamSuccessFinalReturnData
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))))
    h35_success
  have hf : f + 69 = (f + 58) + 11 := by
    omega
  rw [hf]
  exact htail

theorem truth_param_success_state93_fresh_createdAccounts
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) :
    (truthParamSuccessState93
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).createdAccounts =
      createdAccounts := by
  simp [truthParamSuccessState93, truthParamSuccessState92, truthParamSuccessState91,
    truthParamSuccessState90, truthParamSuccessState89, truthParamSuccessState88,
    truthParamSuccessState87, truthParamSuccessState86, truthParamSuccessState85,
    truthParamSuccessState84, truthParamSuccessState83, truthParamSuccessState82,
    truthParamSuccessState81, truthParamSuccessState80, truthParamSuccessState79,
    truthParamSuccessState78, truthParamSuccessState77, truthParamSuccessState76,
    truthParamSuccessState75, truthParamSuccessState74, truthParamSuccessState73,
    truthParamSuccessState72, truthParamSuccessState71, truthParamSuccessState70,
    truthParamSuccessState69, truthParamSuccessState68, truthParamSuccessState67,
    truthParamSuccessState66, truthParamSuccessState65, truthParamSuccessState64,
    truthParamSuccessState63, truthParamSuccessState62, truthParamSuccessState61,
    truthParamSuccessState60, truthParamSuccessState59, truthParamSuccessState58,
    truthParamSuccessState57, truthParamSuccessState56, truthParamSuccessState55,
    truthParamSuccessState54, truthParamSuccessState53, truthParamSuccessState52,
    truthParamSuccessState51, truthParamSuccessState50, truthParamSuccessState49,
    truthParamSuccessState48, truthParamSuccessState47, truthParamSuccessState46,
    truthParamSuccessState45, truthParamSuccessState44, truthParamSuccessState43,
    truthParamSuccessState42, truthParamSuccessState41, truthParamSuccessState40,
    truthParamSuccessState39, truthParamSuccessState38, truthParamSuccessState37,
    truthParamSuccessState36, truthParamSuccessState35, truthParamSuccessState34,
    truthParamSuccessState33, truthParamSuccessState32, truthParamSuccessState31,
    truthParamSuccessState30, truthParamSuccessState29, truthParamSuccessState28,
    truthParamSuccessState27, truthParamSuccessState26, truthParamSuccessState25,
    truthParamSuccessState24, truthParamMismatchState23, truthParamMismatchState22,
    truthParamMismatchState21, truthParamMismatchState20, truthParamMismatchState19,
    truthParamMismatchState18, truthParamMismatchState17, truthParamMismatchState16,
    truthParamMismatchState15, truthParamPayableState14, truthParamPayableState13,
    truthParamPayableState12, truthParamPayableState11, truthParamPayableState10,
    truthParamPayableState9, truthParamPayableState8, truthParamState7, truthParamState6,
    truthParamState5, truthParamState4, truthParamState3, truthParamState2,
    truthParamState1, truthFreshState]

theorem truth_param_success_state93_fresh_accountMap
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) :
    (truthParamSuccessState93
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).accountMap =
      σ := by
  simp [truthParamSuccessState93, truthParamSuccessState92, truthParamSuccessState91,
    truthParamSuccessState90, truthParamSuccessState89, truthParamSuccessState88,
    truthParamSuccessState87, truthParamSuccessState86, truthParamSuccessState85,
    truthParamSuccessState84, truthParamSuccessState83, truthParamSuccessState82,
    truthParamSuccessState81, truthParamSuccessState80, truthParamSuccessState79,
    truthParamSuccessState78, truthParamSuccessState77, truthParamSuccessState76,
    truthParamSuccessState75, truthParamSuccessState74, truthParamSuccessState73,
    truthParamSuccessState72, truthParamSuccessState71, truthParamSuccessState70,
    truthParamSuccessState69, truthParamSuccessState68, truthParamSuccessState67,
    truthParamSuccessState66, truthParamSuccessState65, truthParamSuccessState64,
    truthParamSuccessState63, truthParamSuccessState62, truthParamSuccessState61,
    truthParamSuccessState60, truthParamSuccessState59, truthParamSuccessState58,
    truthParamSuccessState57, truthParamSuccessState56, truthParamSuccessState55,
    truthParamSuccessState54, truthParamSuccessState53, truthParamSuccessState52,
    truthParamSuccessState51, truthParamSuccessState50, truthParamSuccessState49,
    truthParamSuccessState48, truthParamSuccessState47, truthParamSuccessState46,
    truthParamSuccessState45, truthParamSuccessState44, truthParamSuccessState43,
    truthParamSuccessState42, truthParamSuccessState41, truthParamSuccessState40,
    truthParamSuccessState39, truthParamSuccessState38, truthParamSuccessState37,
    truthParamSuccessState36, truthParamSuccessState35, truthParamSuccessState34,
    truthParamSuccessState33, truthParamSuccessState32, truthParamSuccessState31,
    truthParamSuccessState30, truthParamSuccessState29, truthParamSuccessState28,
    truthParamSuccessState27, truthParamSuccessState26, truthParamSuccessState25,
    truthParamSuccessState24, truthParamMismatchState23, truthParamMismatchState22,
    truthParamMismatchState21, truthParamMismatchState20, truthParamMismatchState19,
    truthParamMismatchState18, truthParamMismatchState17, truthParamMismatchState16,
    truthParamMismatchState15, truthParamPayableState14, truthParamPayableState13,
    truthParamPayableState12, truthParamPayableState11, truthParamPayableState10,
    truthParamPayableState9, truthParamPayableState8, truthParamState7, truthParamState6,
    truthParamState5, truthParamState4, truthParamState3, truthParamState2,
    truthParamState1, truthFreshState]

theorem truth_param_success_state93_fresh_substate
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) :
    (truthParamSuccessState93
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).substate =
      A := by
  simp [truthParamSuccessState93, truthParamSuccessState92, truthParamSuccessState91,
    truthParamSuccessState90, truthParamSuccessState89, truthParamSuccessState88,
    truthParamSuccessState87, truthParamSuccessState86, truthParamSuccessState85,
    truthParamSuccessState84, truthParamSuccessState83, truthParamSuccessState82,
    truthParamSuccessState81, truthParamSuccessState80, truthParamSuccessState79,
    truthParamSuccessState78, truthParamSuccessState77, truthParamSuccessState76,
    truthParamSuccessState75, truthParamSuccessState74, truthParamSuccessState73,
    truthParamSuccessState72, truthParamSuccessState71, truthParamSuccessState70,
    truthParamSuccessState69, truthParamSuccessState68, truthParamSuccessState67,
    truthParamSuccessState66, truthParamSuccessState65, truthParamSuccessState64,
    truthParamSuccessState63, truthParamSuccessState62, truthParamSuccessState61,
    truthParamSuccessState60, truthParamSuccessState59, truthParamSuccessState58,
    truthParamSuccessState57, truthParamSuccessState56, truthParamSuccessState55,
    truthParamSuccessState54, truthParamSuccessState53, truthParamSuccessState52,
    truthParamSuccessState51, truthParamSuccessState50, truthParamSuccessState49,
    truthParamSuccessState48, truthParamSuccessState47, truthParamSuccessState46,
    truthParamSuccessState45, truthParamSuccessState44, truthParamSuccessState43,
    truthParamSuccessState42, truthParamSuccessState41, truthParamSuccessState40,
    truthParamSuccessState39, truthParamSuccessState38, truthParamSuccessState37,
    truthParamSuccessState36, truthParamSuccessState35, truthParamSuccessState34,
    truthParamSuccessState33, truthParamSuccessState32, truthParamSuccessState31,
    truthParamSuccessState30, truthParamSuccessState29, truthParamSuccessState28,
    truthParamSuccessState27, truthParamSuccessState26, truthParamSuccessState25,
    truthParamSuccessState24, truthParamMismatchState23, truthParamMismatchState22,
    truthParamMismatchState21, truthParamMismatchState20, truthParamMismatchState19,
    truthParamMismatchState18, truthParamMismatchState17, truthParamMismatchState16,
    truthParamMismatchState15, truthParamPayableState14, truthParamPayableState13,
    truthParamPayableState12, truthParamPayableState11, truthParamPayableState10,
    truthParamPayableState9, truthParamPayableState8, truthParamState7, truthParamState6,
    truthParamState5, truthParamState4, truthParamState3, truthParamState2,
    truthParamState1, truthFreshState]

theorem truth_param_state3_fresh_memory_eq
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) :
    (truthParamState3
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.memory =
      truthMemoryAfterFreePtrStore := by
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    simp [truthParamState3, truthParamState2, truthParamState1, truthFreshState,
      truthMemoryAfterFreePtrStore, Ethereum.UInt256.toByteArray, BE,
      Ethereum.toBytesBigEndian, Ethereum.toBytes', Ethereum.UInt256.toNat, UInt8.size,
      Ethereum.UInt256.size, truth_byteArray_zeroes_eq, USize.toNat, hbits, ByteArray.write]
  all_goals rfl

theorem truth_param_state3_fresh_activeWords_eq
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) :
    (truthParamState3
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.activeWords =
      (⟨3⟩ : Ethereum.UInt256) := by
  simp [truthParamState3, truthParamState2, truthParamState1, truthFreshState,
    Ethereum.MachineState.M, Ethereum.UInt256.toNat, Ethereum.UInt256.size]
  rfl

theorem truth_param_success_state37_memory_eq_state3
    (s : EVM.State) :
    (truthParamSuccessState37 s).machineState.memory =
      (truthParamState3 s).machineState.memory := by
  rfl

theorem truth_param_success_state37_activeWords_eq_state3
    (s : EVM.State) :
    (truthParamSuccessState37 s).machineState.activeWords =
      (truthParamState3 s).machineState.activeWords := by
  rfl

theorem truth_param_success_free_mem_ptr_fresh_eq
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) :
    truthParamSuccessFreeMemPtr
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
      (⟨0x80⟩ : Ethereum.UInt256) := by
  unfold truthParamSuccessFreeMemPtr
  rw [truth_param_success_state37_memory_eq_state3]
  rw [truth_param_state3_fresh_memory_eq]
  rw [truth_param_success_state37_activeWords_eq_state3]
  rw [truth_param_state3_fresh_activeWords_eq]
  rw [show (⟨0x40⟩ : Ethereum.UInt256).toNat = 64 by rfl]
  rw [truth_read_free_ptr_word, truth_from_word128]
  simp [truthMemoryAfterFreePtrStore]
  rfl

theorem truth_param_success_state75_memory_eq_state3
    (s : EVM.State) :
    (truthParamSuccessState75 s).machineState.memory =
      (truthParamState3 s).machineState.memory := by
  rfl

theorem truth_param_success_encoded_memory_fresh_eq
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) :
    truthParamSuccessEncodedMemory
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
      truthMemoryAfterReturnStore := by
  unfold truthParamSuccessEncodedMemory
  rw [truth_param_success_free_mem_ptr_fresh_eq]
  rw [truth_param_success_state75_memory_eq_state3]
  rw [truth_param_state3_fresh_memory_eq]
  rw [← truth_encoded_memory_eq]
  unfold truthEncodedMemory
  rw [truth_free_mem_ptr_eq]
  rw [show truthState75.machineState.memory = truthState3.machineState.memory by rfl]
  rw [truth_state3_memory_eq]

theorem truth_param_success_state87_memory_eq_encoded
    (s : EVM.State) :
    (truthParamSuccessState87 s).machineState.memory =
      truthParamSuccessEncodedMemory s := by
  rfl

theorem truth_param_success_state87_memory_fresh_eq
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) :
    (truthParamSuccessState87
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.memory =
      truthMemoryAfterReturnStore := by
  rw [truth_param_success_state87_memory_eq_encoded]
  exact truth_param_success_encoded_memory_fresh_eq createdAccounts genesisBlockHeader blocks σ σ₀ g A I

theorem truth_param_success_state75_fresh_activeWords_eq
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) :
    (truthParamSuccessState75
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.activeWords =
      (⟨3⟩ : Ethereum.UInt256) := by
  simp [truthParamSuccessState75, truthParamSuccessState74, truthParamSuccessState73,
    truthParamSuccessState72, truthParamSuccessState71, truthParamSuccessState70,
    truthParamSuccessState69, truthParamSuccessState68, truthParamSuccessState67,
    truthParamSuccessState66, truthParamSuccessState65, truthParamSuccessState64,
    truthParamSuccessState63, truthParamSuccessState62, truthParamSuccessState61,
    truthParamSuccessState60, truthParamSuccessState59, truthParamSuccessState58,
    truthParamSuccessState57, truthParamSuccessState56, truthParamSuccessState55,
    truthParamSuccessState54, truthParamSuccessState53, truthParamSuccessState52,
    truthParamSuccessState51, truthParamSuccessState50, truthParamSuccessState49,
    truthParamSuccessState48, truthParamSuccessState47, truthParamSuccessState46,
    truthParamSuccessState45, truthParamSuccessState44, truthParamSuccessState43,
    truthParamSuccessState42, truthParamSuccessState41, truthParamSuccessState40,
    truthParamSuccessState39, truthParamSuccessState38, truthParamSuccessState37,
    truthParamSuccessState36, truthParamSuccessState35, truthParamSuccessState34,
    truthParamSuccessState33, truthParamSuccessState32, truthParamSuccessState31,
    truthParamSuccessState30, truthParamSuccessState29, truthParamSuccessState28,
    truthParamSuccessState27, truthParamSuccessState26, truthParamSuccessState25,
    truthParamSuccessState24, truthParamMismatchState23, truthParamMismatchState22,
    truthParamMismatchState21, truthParamMismatchState20, truthParamMismatchState19,
    truthParamMismatchState18, truthParamMismatchState17, truthParamMismatchState16,
    truthParamMismatchState15, truthParamPayableState14, truthParamPayableState13,
    truthParamPayableState12, truthParamPayableState11, truthParamPayableState10,
    truthParamPayableState9, truthParamPayableState8, truthParamState7, truthParamState6,
    truthParamState5, truthParamState4]
  rw [truth_param_state3_fresh_activeWords_eq]
  simp [Ethereum.MachineState.M, Ethereum.UInt256.toNat, Ethereum.UInt256.size]
  rfl

theorem truth_param_success_state87_activeWords_fresh_eq
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) :
    (truthParamSuccessState87
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.activeWords =
      (⟨5⟩ : Ethereum.UInt256) := by
  rw [show
      (truthParamSuccessState87
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.activeWords =
        (truthParamSuccessState76
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.activeWords by
      rfl]
  unfold truthParamSuccessState76
  rw [truth_param_success_free_mem_ptr_fresh_eq]
  rw [truth_param_success_state75_fresh_activeWords_eq]
  simp [Ethereum.MachineState.M, Ethereum.UInt256.toNat, Ethereum.UInt256.size]
  rfl

theorem truth_param_success_final_free_mem_ptr_fresh_eq
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) :
    truthParamSuccessFinalFreeMemPtr
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
      (⟨0x80⟩ : Ethereum.UInt256) := by
  unfold truthParamSuccessFinalFreeMemPtr
  rw [truth_param_success_state87_memory_fresh_eq]
  rw [truth_param_success_state87_activeWords_fresh_eq]
  rw [show (⟨0x40⟩ : Ethereum.UInt256).toNat = 64 by rfl]
  rw [truth_read_final_free_ptr_word, truth_from_word128]
  simp [truthMemoryAfterReturnStore]
  rfl

theorem truth_param_success_return_length_fresh_eq
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) :
    truthParamSuccessReturnLength
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
      (⟨0x20⟩ : Ethereum.UInt256) := by
  unfold truthParamSuccessReturnLength truthParamSuccessAbiEnd
  rw [truth_param_success_free_mem_ptr_fresh_eq]
  rw [truth_param_success_final_free_mem_ptr_fresh_eq]
  rfl

theorem truth_param_success_state92_memory_eq_state87
    (s : EVM.State) :
    (truthParamSuccessState92 s).machineState.memory =
      (truthParamSuccessState87 s).machineState.memory := by
  rfl

theorem truth_param_success_final_return_data_fresh_eq
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) :
    truthParamSuccessFinalReturnData
        (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
      truthReturnData := by
  unfold truthParamSuccessFinalReturnData
  rw [truth_param_success_state92_memory_eq_state87]
  rw [truth_param_success_state87_memory_fresh_eq]
  rw [truth_param_success_final_free_mem_ptr_fresh_eq]
  rw [truth_param_success_return_length_fresh_eq]
  rw [← truth_final_return_data_eq]
  unfold truthFinalReturnData
  rw [show truthState92.machineState.memory = truthState87.machineState.memory by rfl]
  rw [truth_state87_memory_eq, truth_final_free_mem_ptr_eq, truth_return_length_eq]

theorem truth_success_body_X_trace_exists_of_success_body
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (f : Nat)
    (hfuel : g.toNat - 23 = f + 69)
    (hX :
      Ethereum.EVM.X (f + 69) (Ethereum.EVM.D_J I.code ⟨0⟩)
          (truthParamSuccessState24
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
        .ok (.success
          (truthParamSuccessState93
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I))
          (truthParamSuccessFinalReturnData
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)))) :
    ∃ s',
      s'.createdAccounts = createdAccounts ∧
      s'.accountMap = σ ∧
      s'.substate = A ∧
      Ethereum.EVM.X (g.toNat - 23) (Ethereum.EVM.D_J I.code ⟨0⟩)
          (truthParamSuccessState24
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
        .ok (.success s' truthReturnData) := by
  let s' :=
    truthParamSuccessState93
      (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
  refine ⟨s', ?_, ?_, ?_, ?_⟩
  · exact truth_param_success_state93_fresh_createdAccounts
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  · exact truth_param_success_state93_fresh_accountMap
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  · exact truth_param_success_state93_fresh_substate
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  · rw [hfuel]
    simpa [s', truth_param_success_final_return_data_fresh_eq
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I] using hX

theorem truth_success_body_X_trace_exists_of_gas_guards
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (f : Nat)
    (h_code : I.code = truthRuntimeBytecode)
    (hfuel : g.toNat - 23 = f + 69)
    (hgas42 :
      ¬ (truthParamSuccessState24
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gjumpdest)
    (hgas43 :
      ¬ (truthParamSuccessState25
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas45 :
      ¬ (truthParamSuccessState26
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas47 :
      ¬ (truthParamSuccessState27
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gmid)
    (hgas68 :
      ¬ (truthParamSuccessState28
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gjumpdest)
    (hgas69 :
      ¬ (truthParamSuccessState29
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gbase)
    (hgas70 :
      ¬ (truthParamSuccessState30
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas72 :
      ¬ (truthParamSuccessState31
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas73 :
      ¬ (truthParamSuccessState32
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gbase)
    (hgas74 :
      ¬ (truthParamSuccessState33
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas75 :
      ¬ (truthParamSuccessState34
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gmid)
    (hgas48 :
      ¬ (truthParamSuccessState35
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gjumpdest)
    (hgas49 :
      ¬ (truthParamSuccessState36
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas51_mem :
      ¬ (truthParamSuccessState37
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          Ethereum.EVM.memoryExpansionCost
            (truthParamSuccessState37
              (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MLOAD)
    (hgas51_op :
      ¬ ((truthParamSuccessState37
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
            Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost
              (truthParamSuccessState37
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MLOAD)).toNat <
          GasConstants.Gverylow)
    (hgas52 :
      ¬ (truthParamSuccessState38
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas54 :
      ¬ (truthParamSuccessState39
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas55 :
      ¬ (truthParamSuccessState40
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas56 :
      ¬ (truthParamSuccessState41
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas58 :
      ¬ (truthParamSuccessState42
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gmid)
    (hgas100 :
      ¬ (truthParamSuccessState43
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gjumpdest)
    (hgas101 :
      ¬ (truthParamSuccessState44
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gbase)
    (hgas102 :
      ¬ (truthParamSuccessState45
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas104 :
      ¬ (truthParamSuccessState46
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas105 :
      ¬ (truthParamSuccessState47
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas106 :
      ¬ (truthParamSuccessState48
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas107 :
      ¬ (truthParamSuccessState49
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gbase)
    (hgas108 :
      ¬ (truthParamSuccessState50
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas110 :
      ¬ (truthParamSuccessState51
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gbase)
    (hgas111 :
      ¬ (truthParamSuccessState52
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas112 :
      ¬ (truthParamSuccessState53
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas113 :
      ¬ (truthParamSuccessState54
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas114 :
      ¬ (truthParamSuccessState55
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas116 :
      ¬ (truthParamSuccessState56
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gmid)
    (hgas87 :
      ¬ (truthParamSuccessState57
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gjumpdest)
    (hgas88 :
      ¬ (truthParamSuccessState58
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas90 :
      ¬ (truthParamSuccessState59
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas91 :
      ¬ (truthParamSuccessState60
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas93 :
      ¬ (truthParamSuccessState61
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gmid)
    (hgas76 :
      ¬ (truthParamSuccessState62
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gjumpdest)
    (hgas77 :
      ¬ (truthParamSuccessState63
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gbase)
    (hgas78 :
      ¬ (truthParamSuccessState64
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas79 :
      ¬ (truthParamSuccessState65
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas80 :
      ¬ (truthParamSuccessState66
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas81 :
      ¬ (truthParamSuccessState67
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas82 :
      ¬ (truthParamSuccessState68
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gbase)
    (hgas83 :
      ¬ (truthParamSuccessState69
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas84 :
      ¬ (truthParamSuccessState70
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas85 :
      ¬ (truthParamSuccessState71
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gbase)
    (hgas86 :
      ¬ (truthParamSuccessState72
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gmid)
    (hgas94 :
      ¬ (truthParamSuccessState73
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gjumpdest)
    (hgas95 :
      ¬ (truthParamSuccessState74
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hmem96 :
      ¬ (truthParamSuccessState75
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost
          (truthParamSuccessState75
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)
    (hgas96 :
      ¬ ((truthParamSuccessState75
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
          Ethereum.UInt256.ofNat
            (Ethereum.EVM.memoryExpansionCost
              (truthParamSuccessState75
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MSTORE)).toNat <
        GasConstants.Gverylow)
    (hgas97 :
      ¬ (truthParamSuccessState76
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gbase)
    (hgas98 :
      ¬ (truthParamSuccessState77
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gbase)
    (hgas99 :
      ¬ (truthParamSuccessState78
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gmid)
    (hgas117 :
      ¬ (truthParamSuccessState79
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gjumpdest)
    (hgas118 :
      ¬ (truthParamSuccessState80
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas119 :
      ¬ (truthParamSuccessState81
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas120 :
      ¬ (truthParamSuccessState82
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gbase)
    (hgas121 :
      ¬ (truthParamSuccessState83
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gbase)
    (hgas122 :
      ¬ (truthParamSuccessState84
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gmid)
    (hgas59 :
      ¬ (truthParamSuccessState85
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gjumpdest)
    (hgas60 :
      ¬ (truthParamSuccessState86
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hmem62 :
      ¬ (truthParamSuccessState87
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost
          (truthParamSuccessState87
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MLOAD)
    (hgas62 :
      ¬ ((truthParamSuccessState87
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable -
          Ethereum.UInt256.ofNat
            (Ethereum.EVM.memoryExpansionCost
              (truthParamSuccessState87
                (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .MLOAD)).toNat <
        GasConstants.Gverylow)
    (hgas63 :
      ¬ (truthParamSuccessState88
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas64 :
      ¬ (truthParamSuccessState89
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas65 :
      ¬ (truthParamSuccessState90
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hgas66 :
      ¬ (truthParamSuccessState91
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
          GasConstants.Gverylow)
    (hmem67 :
      ¬ (truthParamSuccessState92
          (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)).machineState.gasAvailable.toNat <
        Ethereum.EVM.memoryExpansionCost
          (truthParamSuccessState92
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) .RETURN) :
    ∃ s',
      s'.createdAccounts = createdAccounts ∧
      s'.accountMap = σ ∧
      s'.substate = A ∧
      Ethereum.EVM.X (g.toNat - 23) (Ethereum.EVM.D_J I.code ⟨0⟩)
          (truthParamSuccessState24
            (truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) =
        .ok (.success s' truthReturnData) := by
  let s := truthFreshState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have h_code_s : s.executionEnv.code = truthRuntimeBytecode := by
    simp [s, truthFreshState, h_code]
  have h35_success :
      Ethereum.EVM.X (f + 58) (Ethereum.EVM.D_J I.code ⟨0⟩)
          (truthParamSuccessState35 s) =
        .ok (.success
          (truthParamSuccessState93 s)
          (truthParamSuccessFinalReturnData s)) := by
    have hraw :=
      truth_success_body_X_state35_to_success_of_gas_guards s f h_code_s
        hgas48 hgas49 hgas51_mem hgas51_op hgas52 hgas54 hgas55 hgas56 hgas58
        hgas100 hgas101 hgas102 hgas104 hgas105 hgas106 hgas107
        hgas108 hgas110 hgas111 hgas112 hgas113 hgas114 hgas116
        hgas87 hgas88 hgas90 hgas91 hgas93
        hgas76 hgas77 hgas78 hgas79 hgas80 hgas81 hgas82 hgas83 hgas84 hgas85 hgas86
        hgas94 hgas95 hmem96 hgas96 hgas97 hgas98 hgas99
        hgas117 hgas118 hgas119 hgas120 hgas121 hgas122
        hgas59 hgas60 hmem62 hgas62 hgas63 hgas64 hgas65 hgas66 hmem67
    simpa [s, truthFreshState] using hraw
  have h24_35 :
      ∀ (xres : Except Ethereum.EVM.ExecutionException (Ethereum.ExecutionResult EVM.State)),
        Ethereum.EVM.X (f + 58) (Ethereum.EVM.D_J I.code ⟨0⟩)
            (truthParamSuccessState35 s) = xres →
        Ethereum.EVM.X ((f + 58) + 11) (Ethereum.EVM.D_J I.code ⟨0⟩)
            (truthParamSuccessState24 s) = xres := by
    intro xres htail
    simpa [s] using
      truth_success_dispatch_tail_X_state24_to_state35_of_gas_guards
        createdAccounts genesisBlockHeader blocks σ σ₀ g A I (f + 58) xres h_code
        hgas42 hgas43 hgas45 hgas47 hgas68 hgas69 hgas70 hgas72 hgas73 hgas74 hgas75
        (by simpa [s] using htail)
  have h24_success :
      Ethereum.EVM.X (f + 69) (Ethereum.EVM.D_J I.code ⟨0⟩)
          (truthParamSuccessState24 s) =
        .ok (.success
          (truthParamSuccessState93 s)
          (truthParamSuccessFinalReturnData s)) := by
    simpa [s] using
      truth_success_body_X_state24_to_success_of_gas_guards
        createdAccounts genesisBlockHeader blocks σ σ₀ g A I f
        (by
          intro xres htail
          exact h24_35 xres (by simpa [s] using htail))
        (by simpa [s] using h35_success)
  exact truth_success_body_X_trace_exists_of_success_body
    createdAccounts genesisBlockHeader blocks σ σ₀ g A I f hfuel
    (by simpa [s] using h24_success)

end Truth
end Examples
end Act
