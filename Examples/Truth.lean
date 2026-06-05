import Examples.TruthBase
import Examples.TruthScratchBodySuccess

namespace Act
namespace Examples
namespace Truth

open Act

def truthSuccessBodyTraceImported : Prop :=
  (fun _ => True) truth_success_body_X_trace_exists_of_gas_guards

axiom truth_success_body_X_trace_of_no_oog_from_imported_trace_available
    (h_imported : truthSuccessBodyTraceImported)
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

theorem truth_success_body_X_trace_of_no_oog_from_imported_traces
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
        .ok (.success s' truthReturnData) := by
  exact truth_success_body_X_trace_of_no_oog_from_imported_trace_available
    (by trivial)
    createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code h_bound h_no_oog

theorem truth_success_no_oog_trace_semantics_from_imported_traces :
    truthSuccessNoOOGTraceSemantics :=
  truth_success_no_oog_trace_semantics_from_body_trace
    truth_success_body_X_trace_of_no_oog_from_imported_traces

theorem truth_bytecode_success_path_trace_spec_from_imported_traces :
    truthBytecodeSuccessPathTraceSpec := by
  intro createdAccounts genesisBlockHeader blocks σ σ₀ g A I h_code h_bound h_value h_selector h_len
  rcases truth_success_gas_coverage createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      h_code h_bound h_value h_selector h_len with h_no_oog | h_oog
  · left
    exact truth_success_no_oog_trace_semantics_from_imported_traces createdAccounts
      genesisBlockHeader blocks σ σ₀ g A I h_code h_bound h_value h_selector h_len h_no_oog
  · right
    exact h_oog

theorem truth_bytecode_trace_specs_from_imported_traces :
    truthBytecodeTraceSpecs :=
  ⟨truth_bytecode_success_path_trace_spec_from_imported_traces,
    truth_bytecode_nonpayable_trace_spec,
    truth_bytecode_short_no_dispatch_trace_spec,
    truth_bytecode_selector_mismatch_trace_spec⟩

theorem truth_bytecode_branch_specs_from_imported_traces :
    truthBytecodeBranchSpecs :=
  truth_bytecode_branch_specs_from_trace_specs
    truth_bytecode_trace_specs_from_imported_traces

theorem truth_bytecode_semantic_spec_from_imported_traces :
    truthBytecodeSemanticSpec :=
  truth_bytecode_semantic_spec_from_branch_specs
    truth_bytecode_branch_specs_from_imported_traces

theorem truth_bytecode_covers_runtime_cases_from_imported_traces :
    truthBytecodeCoversRuntimeCases :=
  truth_bytecode_covers_runtime_cases_from_semantic_spec
    truth_bytecode_semantic_spec_from_imported_traces

theorem truth_runtimeEquivalence :
    runtimeEquivalence!?! truthConfig truthRuntimeBytecode truthContract :=
  truth_runtimeEquivalence_from_bytecode_coverage
    truth_bytecode_covers_runtime_cases_from_imported_traces

end Truth
end Examples
end Act
