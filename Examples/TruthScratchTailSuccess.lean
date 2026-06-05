import Examples.TruthScratchTail6

set_option maxRecDepth 100000

namespace Act
namespace Examples
namespace Truth

theorem truth_success_return_tail_X_of_gas_guards
    (s : EVM.State)
    (f : Nat)
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
    Ethereum.EVM.X (f + 20) (Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩)
        (truthParamSuccessState73 s) =
      .ok (.success (truthParamSuccessState93 s) (truthParamSuccessFinalReturnData s)) := by
  have h59tail :
      Ethereum.EVM.X (f + 8) (Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩)
          (truthParamSuccessState85 s) =
        .ok (.success (truthParamSuccessState93 s) (truthParamSuccessFinalReturnData s)) :=
    truth_success_tail_X_pc59_to_pc67_of_gas_guards s f h_code hgas59 hgas60 hmem62
      hgas62 hgas63 hgas64 hgas65 hgas66 hmem67
  have h117tail :
      Ethereum.EVM.X ((f + 8) + 6) (Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩)
          (truthParamSuccessState79 s) =
        .ok (.success (truthParamSuccessState93 s) (truthParamSuccessFinalReturnData s)) :=
    truth_success_tail_X_pc117_to_pc122_of_gas_guards s (f + 8)
      (.ok (.success (truthParamSuccessState93 s) (truthParamSuccessFinalReturnData s)))
      h_code hgas117 hgas118 hgas119 hgas120 hgas121 hgas122 h59tail
  have h94tail :
      Ethereum.EVM.X (((f + 8) + 6) + 6) (Ethereum.EVM.D_J s.executionEnv.code ⟨0⟩)
          (truthParamSuccessState73 s) =
        .ok (.success (truthParamSuccessState93 s) (truthParamSuccessFinalReturnData s)) :=
    truth_success_tail_X_pc94_to_pc99_of_gas_guards s ((f + 8) + 6)
      (.ok (.success (truthParamSuccessState93 s) (truthParamSuccessFinalReturnData s)))
      h_code hgas94 hgas95 hmem96 hgas96 hgas97 hgas98 hgas99 h117tail
  have hf : f + 20 = ((f + 8) + 6) + 6 := by
    omega
  rw [hf]
  exact h94tail

end Truth
end Examples
end Act
