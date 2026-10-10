import Benchmarks.UniswapV4PoolManager.Common

/-! Solm selector routing for PoolManager. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager

set_option maxRecDepth 2000000

/-! ## Solm dispatch: which transition a selector reaches -/

theorem poolManagerDispatch_balanceOf {I : ExecutionEnv} 
    (hsel : selIs I (poolManagerSelBytes 0)) :
    dispatchMsg contract I.calldata = some balanceOfTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := []) (post := [supportsInterfaceTransition, transferTransition, settleTransition, initializeTransition, mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition, approveTransition, unlockTransition, donateTransition, setOperatorTransition, allowanceTransition, modifyLiquidityTransition, syncTransition, ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition, isOperatorTransition, clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := balanceOfTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp at hu
  · rw [balanceOfSelectorOf]; exact hsel

theorem poolManagerDispatch_supportsInterface {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0))
    (hsel : selIs I (poolManagerSelBytes 1)) :
    dispatchMsg contract I.calldata = some supportsInterfaceTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition]) (post := [transferTransition, settleTransition, initializeTransition, mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition, approveTransition, unlockTransition, donateTransition, setOperatorTransition, allowanceTransition, modifyLiquidityTransition, syncTransition, ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition, isOperatorTransition, clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := supportsInterfaceTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
  · rw [supportsInterfaceSelectorOf]; exact hsel

theorem poolManagerDispatch_transfer {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1))
    (hsel : selIs I (poolManagerSelBytes 2)) :
    dispatchMsg contract I.calldata = some transferTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition]) (post := [settleTransition, initializeTransition, mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition, approveTransition, unlockTransition, donateTransition, setOperatorTransition, allowanceTransition, modifyLiquidityTransition, syncTransition, ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition, isOperatorTransition, clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := transferTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
  · rw [transferSelectorOf]; exact hsel

theorem poolManagerDispatch_settle {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2))
    (hsel : selIs I (poolManagerSelBytes 3)) :
    dispatchMsg contract I.calldata = some settleTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition]) (post := [initializeTransition, mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition, approveTransition, unlockTransition, donateTransition, setOperatorTransition, allowanceTransition, modifyLiquidityTransition, syncTransition, ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition, isOperatorTransition, clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := settleTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
  · rw [settleSelectorOf]; exact hsel

theorem poolManagerDispatch_initialize {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2)) (h3 : ¬ selIs I (poolManagerSelBytes 3))
    (hsel : selIs I (poolManagerSelBytes 4)) :
    dispatchMsg contract I.calldata = some initializeTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition, settleTransition]) (post := [mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition, approveTransition, unlockTransition, donateTransition, setOperatorTransition, allowanceTransition, modifyLiquidityTransition, syncTransition, ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition, isOperatorTransition, clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := initializeTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settleSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
  · rw [initializeSelectorOf]; exact hsel

theorem poolManagerDispatch_mint {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2)) (h3 : ¬ selIs I (poolManagerSelBytes 3)) (h4 : ¬ selIs I (poolManagerSelBytes 4))
    (hsel : selIs I (poolManagerSelBytes 5)) :
    dispatchMsg contract I.calldata = some mintTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition, settleTransition, initializeTransition]) (post := [extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition, approveTransition, unlockTransition, donateTransition, setOperatorTransition, allowanceTransition, modifyLiquidityTransition, syncTransition, ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition, isOperatorTransition, clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := mintTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settleSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [initializeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
  · rw [mintSelectorOf]; exact hsel

theorem poolManagerDispatch_extsload_bytes32 {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2)) (h3 : ¬ selIs I (poolManagerSelBytes 3)) (h4 : ¬ selIs I (poolManagerSelBytes 4)) (h5 : ¬ selIs I (poolManagerSelBytes 5))
    (hsel : selIs I (poolManagerSelBytes 6)) :
    dispatchMsg contract I.calldata = some extsload_bytes32Transition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition, settleTransition, initializeTransition, mintTransition]) (post := [extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition, approveTransition, unlockTransition, donateTransition, setOperatorTransition, allowanceTransition, modifyLiquidityTransition, syncTransition, ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition, isOperatorTransition, clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := extsload_bytes32Transition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settleSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [initializeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
  · rw [extsload_bytes32SelectorOf]; exact hsel

theorem poolManagerDispatch_extsload_bytes32_uint256 {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2)) (h3 : ¬ selIs I (poolManagerSelBytes 3)) (h4 : ¬ selIs I (poolManagerSelBytes 4)) (h5 : ¬ selIs I (poolManagerSelBytes 5)) (h6 : ¬ selIs I (poolManagerSelBytes 6))
    (hsel : selIs I (poolManagerSelBytes 7)) :
    dispatchMsg contract I.calldata = some extsload_bytes32_uint256Transition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition, settleTransition, initializeTransition, mintTransition, extsload_bytes32Transition]) (post := [extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition, approveTransition, unlockTransition, donateTransition, setOperatorTransition, allowanceTransition, modifyLiquidityTransition, syncTransition, ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition, isOperatorTransition, clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := extsload_bytes32_uint256Transition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settleSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [initializeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [extsload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h6
  · rw [extsload_bytes32_uint256SelectorOf]; exact hsel

theorem poolManagerDispatch_extsload_bytes32_array {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2)) (h3 : ¬ selIs I (poolManagerSelBytes 3)) (h4 : ¬ selIs I (poolManagerSelBytes 4)) (h5 : ¬ selIs I (poolManagerSelBytes 5)) (h6 : ¬ selIs I (poolManagerSelBytes 6)) (h7 : ¬ selIs I (poolManagerSelBytes 7))
    (hsel : selIs I (poolManagerSelBytes 8)) :
    dispatchMsg contract I.calldata = some extsload_bytes32_arrayTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition, settleTransition, initializeTransition, mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition]) (post := [takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition, approveTransition, unlockTransition, donateTransition, setOperatorTransition, allowanceTransition, modifyLiquidityTransition, syncTransition, ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition, isOperatorTransition, clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := extsload_bytes32_arrayTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settleSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [initializeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [extsload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [extsload_bytes32_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h7
  · rw [extsload_bytes32_arraySelectorOf]; exact hsel

theorem poolManagerDispatch_take {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2)) (h3 : ¬ selIs I (poolManagerSelBytes 3)) (h4 : ¬ selIs I (poolManagerSelBytes 4)) (h5 : ¬ selIs I (poolManagerSelBytes 5)) (h6 : ¬ selIs I (poolManagerSelBytes 6)) (h7 : ¬ selIs I (poolManagerSelBytes 7)) (h8 : ¬ selIs I (poolManagerSelBytes 8))
    (hsel : selIs I (poolManagerSelBytes 9)) :
    dispatchMsg contract I.calldata = some takeTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition, settleTransition, initializeTransition, mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition]) (post := [setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition, approveTransition, unlockTransition, donateTransition, setOperatorTransition, allowanceTransition, modifyLiquidityTransition, syncTransition, ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition, isOperatorTransition, clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := takeTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settleSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [initializeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [extsload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [extsload_bytes32_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [extsload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
  · rw [takeSelectorOf]; exact hsel

theorem poolManagerDispatch_setProtocolFeeController {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2)) (h3 : ¬ selIs I (poolManagerSelBytes 3)) (h4 : ¬ selIs I (poolManagerSelBytes 4)) (h5 : ¬ selIs I (poolManagerSelBytes 5)) (h6 : ¬ selIs I (poolManagerSelBytes 6)) (h7 : ¬ selIs I (poolManagerSelBytes 7)) (h8 : ¬ selIs I (poolManagerSelBytes 8)) (h9 : ¬ selIs I (poolManagerSelBytes 9))
    (hsel : selIs I (poolManagerSelBytes 10)) :
    dispatchMsg contract I.calldata = some setProtocolFeeControllerTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition, settleTransition, initializeTransition, mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition]) (post := [collectProtocolFeesTransition, settleForTransition, approveTransition, unlockTransition, donateTransition, setOperatorTransition, allowanceTransition, modifyLiquidityTransition, syncTransition, ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition, isOperatorTransition, clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := setProtocolFeeControllerTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settleSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [initializeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [extsload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [extsload_bytes32_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [extsload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
  · rw [setProtocolFeeControllerSelectorOf]; exact hsel

theorem poolManagerDispatch_collectProtocolFees {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2)) (h3 : ¬ selIs I (poolManagerSelBytes 3)) (h4 : ¬ selIs I (poolManagerSelBytes 4)) (h5 : ¬ selIs I (poolManagerSelBytes 5)) (h6 : ¬ selIs I (poolManagerSelBytes 6)) (h7 : ¬ selIs I (poolManagerSelBytes 7)) (h8 : ¬ selIs I (poolManagerSelBytes 8)) (h9 : ¬ selIs I (poolManagerSelBytes 9)) (h10 : ¬ selIs I (poolManagerSelBytes 10))
    (hsel : selIs I (poolManagerSelBytes 11)) :
    dispatchMsg contract I.calldata = some collectProtocolFeesTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition, settleTransition, initializeTransition, mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition]) (post := [settleForTransition, approveTransition, unlockTransition, donateTransition, setOperatorTransition, allowanceTransition, modifyLiquidityTransition, syncTransition, ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition, isOperatorTransition, clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := collectProtocolFeesTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settleSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [initializeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [extsload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [extsload_bytes32_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [extsload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [setProtocolFeeControllerSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
  · rw [collectProtocolFeesSelectorOf]; exact hsel

theorem poolManagerDispatch_settleFor {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2)) (h3 : ¬ selIs I (poolManagerSelBytes 3)) (h4 : ¬ selIs I (poolManagerSelBytes 4)) (h5 : ¬ selIs I (poolManagerSelBytes 5)) (h6 : ¬ selIs I (poolManagerSelBytes 6)) (h7 : ¬ selIs I (poolManagerSelBytes 7)) (h8 : ¬ selIs I (poolManagerSelBytes 8)) (h9 : ¬ selIs I (poolManagerSelBytes 9)) (h10 : ¬ selIs I (poolManagerSelBytes 10)) (h11 : ¬ selIs I (poolManagerSelBytes 11))
    (hsel : selIs I (poolManagerSelBytes 12)) :
    dispatchMsg contract I.calldata = some settleForTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition, settleTransition, initializeTransition, mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition]) (post := [approveTransition, unlockTransition, donateTransition, setOperatorTransition, allowanceTransition, modifyLiquidityTransition, syncTransition, ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition, isOperatorTransition, clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := settleForTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settleSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [initializeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [extsload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [extsload_bytes32_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [extsload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [setProtocolFeeControllerSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [collectProtocolFeesSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
  · rw [settleForSelectorOf]; exact hsel

theorem poolManagerDispatch_approve {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2)) (h3 : ¬ selIs I (poolManagerSelBytes 3)) (h4 : ¬ selIs I (poolManagerSelBytes 4)) (h5 : ¬ selIs I (poolManagerSelBytes 5)) (h6 : ¬ selIs I (poolManagerSelBytes 6)) (h7 : ¬ selIs I (poolManagerSelBytes 7)) (h8 : ¬ selIs I (poolManagerSelBytes 8)) (h9 : ¬ selIs I (poolManagerSelBytes 9)) (h10 : ¬ selIs I (poolManagerSelBytes 10)) (h11 : ¬ selIs I (poolManagerSelBytes 11)) (h12 : ¬ selIs I (poolManagerSelBytes 12))
    (hsel : selIs I (poolManagerSelBytes 13)) :
    dispatchMsg contract I.calldata = some approveTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition, settleTransition, initializeTransition, mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition]) (post := [unlockTransition, donateTransition, setOperatorTransition, allowanceTransition, modifyLiquidityTransition, syncTransition, ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition, isOperatorTransition, clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := approveTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settleSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [initializeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [extsload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [extsload_bytes32_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [extsload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [setProtocolFeeControllerSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [collectProtocolFeesSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [settleForSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
  · rw [approveSelectorOf]; exact hsel

theorem poolManagerDispatch_unlock {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2)) (h3 : ¬ selIs I (poolManagerSelBytes 3)) (h4 : ¬ selIs I (poolManagerSelBytes 4)) (h5 : ¬ selIs I (poolManagerSelBytes 5)) (h6 : ¬ selIs I (poolManagerSelBytes 6)) (h7 : ¬ selIs I (poolManagerSelBytes 7)) (h8 : ¬ selIs I (poolManagerSelBytes 8)) (h9 : ¬ selIs I (poolManagerSelBytes 9)) (h10 : ¬ selIs I (poolManagerSelBytes 10)) (h11 : ¬ selIs I (poolManagerSelBytes 11)) (h12 : ¬ selIs I (poolManagerSelBytes 12)) (h13 : ¬ selIs I (poolManagerSelBytes 13))
    (hsel : selIs I (poolManagerSelBytes 14)) :
    dispatchMsg contract I.calldata = some unlockTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition, settleTransition, initializeTransition, mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition, approveTransition]) (post := [donateTransition, setOperatorTransition, allowanceTransition, modifyLiquidityTransition, syncTransition, ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition, isOperatorTransition, clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := unlockTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settleSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [initializeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [extsload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [extsload_bytes32_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [extsload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [setProtocolFeeControllerSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [collectProtocolFeesSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [settleForSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
  · rw [unlockSelectorOf]; exact hsel

theorem poolManagerDispatch_donate {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2)) (h3 : ¬ selIs I (poolManagerSelBytes 3)) (h4 : ¬ selIs I (poolManagerSelBytes 4)) (h5 : ¬ selIs I (poolManagerSelBytes 5)) (h6 : ¬ selIs I (poolManagerSelBytes 6)) (h7 : ¬ selIs I (poolManagerSelBytes 7)) (h8 : ¬ selIs I (poolManagerSelBytes 8)) (h9 : ¬ selIs I (poolManagerSelBytes 9)) (h10 : ¬ selIs I (poolManagerSelBytes 10)) (h11 : ¬ selIs I (poolManagerSelBytes 11)) (h12 : ¬ selIs I (poolManagerSelBytes 12)) (h13 : ¬ selIs I (poolManagerSelBytes 13)) (h14 : ¬ selIs I (poolManagerSelBytes 14))
    (hsel : selIs I (poolManagerSelBytes 15)) :
    dispatchMsg contract I.calldata = some donateTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition, settleTransition, initializeTransition, mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition, approveTransition, unlockTransition]) (post := [setOperatorTransition, allowanceTransition, modifyLiquidityTransition, syncTransition, ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition, isOperatorTransition, clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := donateTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settleSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [initializeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [extsload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [extsload_bytes32_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [extsload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [setProtocolFeeControllerSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [collectProtocolFeesSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [settleForSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [unlockSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
  · rw [donateSelectorOf]; exact hsel

theorem poolManagerDispatch_setOperator {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2)) (h3 : ¬ selIs I (poolManagerSelBytes 3)) (h4 : ¬ selIs I (poolManagerSelBytes 4)) (h5 : ¬ selIs I (poolManagerSelBytes 5)) (h6 : ¬ selIs I (poolManagerSelBytes 6)) (h7 : ¬ selIs I (poolManagerSelBytes 7)) (h8 : ¬ selIs I (poolManagerSelBytes 8)) (h9 : ¬ selIs I (poolManagerSelBytes 9)) (h10 : ¬ selIs I (poolManagerSelBytes 10)) (h11 : ¬ selIs I (poolManagerSelBytes 11)) (h12 : ¬ selIs I (poolManagerSelBytes 12)) (h13 : ¬ selIs I (poolManagerSelBytes 13)) (h14 : ¬ selIs I (poolManagerSelBytes 14)) (h15 : ¬ selIs I (poolManagerSelBytes 15))
    (hsel : selIs I (poolManagerSelBytes 16)) :
    dispatchMsg contract I.calldata = some setOperatorTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition, settleTransition, initializeTransition, mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition, approveTransition, unlockTransition, donateTransition]) (post := [allowanceTransition, modifyLiquidityTransition, syncTransition, ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition, isOperatorTransition, clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := setOperatorTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settleSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [initializeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [extsload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [extsload_bytes32_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [extsload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [setProtocolFeeControllerSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [collectProtocolFeesSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [settleForSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [unlockSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [donateSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
  · rw [setOperatorSelectorOf]; exact hsel

theorem poolManagerDispatch_allowance {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2)) (h3 : ¬ selIs I (poolManagerSelBytes 3)) (h4 : ¬ selIs I (poolManagerSelBytes 4)) (h5 : ¬ selIs I (poolManagerSelBytes 5)) (h6 : ¬ selIs I (poolManagerSelBytes 6)) (h7 : ¬ selIs I (poolManagerSelBytes 7)) (h8 : ¬ selIs I (poolManagerSelBytes 8)) (h9 : ¬ selIs I (poolManagerSelBytes 9)) (h10 : ¬ selIs I (poolManagerSelBytes 10)) (h11 : ¬ selIs I (poolManagerSelBytes 11)) (h12 : ¬ selIs I (poolManagerSelBytes 12)) (h13 : ¬ selIs I (poolManagerSelBytes 13)) (h14 : ¬ selIs I (poolManagerSelBytes 14)) (h15 : ¬ selIs I (poolManagerSelBytes 15)) (h16 : ¬ selIs I (poolManagerSelBytes 16))
    (hsel : selIs I (poolManagerSelBytes 17)) :
    dispatchMsg contract I.calldata = some allowanceTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition, settleTransition, initializeTransition, mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition, approveTransition, unlockTransition, donateTransition, setOperatorTransition]) (post := [modifyLiquidityTransition, syncTransition, ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition, isOperatorTransition, clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := allowanceTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settleSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [initializeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [extsload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [extsload_bytes32_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [extsload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [setProtocolFeeControllerSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [collectProtocolFeesSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [settleForSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [unlockSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [donateSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [setOperatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
  · rw [allowanceSelectorOf]; exact hsel

theorem poolManagerDispatch_modifyLiquidity {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2)) (h3 : ¬ selIs I (poolManagerSelBytes 3)) (h4 : ¬ selIs I (poolManagerSelBytes 4)) (h5 : ¬ selIs I (poolManagerSelBytes 5)) (h6 : ¬ selIs I (poolManagerSelBytes 6)) (h7 : ¬ selIs I (poolManagerSelBytes 7)) (h8 : ¬ selIs I (poolManagerSelBytes 8)) (h9 : ¬ selIs I (poolManagerSelBytes 9)) (h10 : ¬ selIs I (poolManagerSelBytes 10)) (h11 : ¬ selIs I (poolManagerSelBytes 11)) (h12 : ¬ selIs I (poolManagerSelBytes 12)) (h13 : ¬ selIs I (poolManagerSelBytes 13)) (h14 : ¬ selIs I (poolManagerSelBytes 14)) (h15 : ¬ selIs I (poolManagerSelBytes 15)) (h16 : ¬ selIs I (poolManagerSelBytes 16)) (h17 : ¬ selIs I (poolManagerSelBytes 17))
    (hsel : selIs I (poolManagerSelBytes 18)) :
    dispatchMsg contract I.calldata = some modifyLiquidityTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition, settleTransition, initializeTransition, mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition, approveTransition, unlockTransition, donateTransition, setOperatorTransition, allowanceTransition]) (post := [syncTransition, ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition, isOperatorTransition, clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := modifyLiquidityTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settleSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [initializeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [extsload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [extsload_bytes32_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [extsload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [setProtocolFeeControllerSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [collectProtocolFeesSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [settleForSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [unlockSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [donateSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [setOperatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [allowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
  · rw [modifyLiquiditySelectorOf]; exact hsel

theorem poolManagerDispatch_sync {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2)) (h3 : ¬ selIs I (poolManagerSelBytes 3)) (h4 : ¬ selIs I (poolManagerSelBytes 4)) (h5 : ¬ selIs I (poolManagerSelBytes 5)) (h6 : ¬ selIs I (poolManagerSelBytes 6)) (h7 : ¬ selIs I (poolManagerSelBytes 7)) (h8 : ¬ selIs I (poolManagerSelBytes 8)) (h9 : ¬ selIs I (poolManagerSelBytes 9)) (h10 : ¬ selIs I (poolManagerSelBytes 10)) (h11 : ¬ selIs I (poolManagerSelBytes 11)) (h12 : ¬ selIs I (poolManagerSelBytes 12)) (h13 : ¬ selIs I (poolManagerSelBytes 13)) (h14 : ¬ selIs I (poolManagerSelBytes 14)) (h15 : ¬ selIs I (poolManagerSelBytes 15)) (h16 : ¬ selIs I (poolManagerSelBytes 16)) (h17 : ¬ selIs I (poolManagerSelBytes 17)) (h18 : ¬ selIs I (poolManagerSelBytes 18))
    (hsel : selIs I (poolManagerSelBytes 19)) :
    dispatchMsg contract I.calldata = some syncTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition, settleTransition, initializeTransition, mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition, approveTransition, unlockTransition, donateTransition, setOperatorTransition, allowanceTransition, modifyLiquidityTransition]) (post := [ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition, isOperatorTransition, clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := syncTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settleSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [initializeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [extsload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [extsload_bytes32_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [extsload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [setProtocolFeeControllerSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [collectProtocolFeesSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [settleForSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [unlockSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [donateSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [setOperatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [allowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [modifyLiquiditySelectorOf]; exact Bool.eq_false_of_not_eq_true h18
  · rw [syncSelectorOf]; exact hsel

theorem poolManagerDispatch_owner {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2)) (h3 : ¬ selIs I (poolManagerSelBytes 3)) (h4 : ¬ selIs I (poolManagerSelBytes 4)) (h5 : ¬ selIs I (poolManagerSelBytes 5)) (h6 : ¬ selIs I (poolManagerSelBytes 6)) (h7 : ¬ selIs I (poolManagerSelBytes 7)) (h8 : ¬ selIs I (poolManagerSelBytes 8)) (h9 : ¬ selIs I (poolManagerSelBytes 9)) (h10 : ¬ selIs I (poolManagerSelBytes 10)) (h11 : ¬ selIs I (poolManagerSelBytes 11)) (h12 : ¬ selIs I (poolManagerSelBytes 12)) (h13 : ¬ selIs I (poolManagerSelBytes 13)) (h14 : ¬ selIs I (poolManagerSelBytes 14)) (h15 : ¬ selIs I (poolManagerSelBytes 15)) (h16 : ¬ selIs I (poolManagerSelBytes 16)) (h17 : ¬ selIs I (poolManagerSelBytes 17)) (h18 : ¬ selIs I (poolManagerSelBytes 18)) (h19 : ¬ selIs I (poolManagerSelBytes 19))
    (hsel : selIs I (poolManagerSelBytes 20)) :
    dispatchMsg contract I.calldata = some ownerTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition, settleTransition, initializeTransition, mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition, approveTransition, unlockTransition, donateTransition, setOperatorTransition, allowanceTransition, modifyLiquidityTransition, syncTransition]) (post := [updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition, isOperatorTransition, clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := ownerTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settleSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [initializeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [extsload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [extsload_bytes32_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [extsload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [setProtocolFeeControllerSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [collectProtocolFeesSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [settleForSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [unlockSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [donateSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [setOperatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [allowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [modifyLiquiditySelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [syncSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
  · rw [ownerSelectorOf]; exact hsel

theorem poolManagerDispatch_updateDynamicLPFee {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2)) (h3 : ¬ selIs I (poolManagerSelBytes 3)) (h4 : ¬ selIs I (poolManagerSelBytes 4)) (h5 : ¬ selIs I (poolManagerSelBytes 5)) (h6 : ¬ selIs I (poolManagerSelBytes 6)) (h7 : ¬ selIs I (poolManagerSelBytes 7)) (h8 : ¬ selIs I (poolManagerSelBytes 8)) (h9 : ¬ selIs I (poolManagerSelBytes 9)) (h10 : ¬ selIs I (poolManagerSelBytes 10)) (h11 : ¬ selIs I (poolManagerSelBytes 11)) (h12 : ¬ selIs I (poolManagerSelBytes 12)) (h13 : ¬ selIs I (poolManagerSelBytes 13)) (h14 : ¬ selIs I (poolManagerSelBytes 14)) (h15 : ¬ selIs I (poolManagerSelBytes 15)) (h16 : ¬ selIs I (poolManagerSelBytes 16)) (h17 : ¬ selIs I (poolManagerSelBytes 17)) (h18 : ¬ selIs I (poolManagerSelBytes 18)) (h19 : ¬ selIs I (poolManagerSelBytes 19)) (h20 : ¬ selIs I (poolManagerSelBytes 20))
    (hsel : selIs I (poolManagerSelBytes 21)) :
    dispatchMsg contract I.calldata = some updateDynamicLPFeeTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition, settleTransition, initializeTransition, mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition, approveTransition, unlockTransition, donateTransition, setOperatorTransition, allowanceTransition, modifyLiquidityTransition, syncTransition, ownerTransition]) (post := [exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition, isOperatorTransition, clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := updateDynamicLPFeeTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settleSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [initializeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [extsload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [extsload_bytes32_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [extsload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [setProtocolFeeControllerSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [collectProtocolFeesSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [settleForSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [unlockSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [donateSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [setOperatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [allowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [modifyLiquiditySelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [syncSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [ownerSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
  · rw [updateDynamicLPFeeSelectorOf]; exact hsel

theorem poolManagerDispatch_exttload_bytes32_array {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2)) (h3 : ¬ selIs I (poolManagerSelBytes 3)) (h4 : ¬ selIs I (poolManagerSelBytes 4)) (h5 : ¬ selIs I (poolManagerSelBytes 5)) (h6 : ¬ selIs I (poolManagerSelBytes 6)) (h7 : ¬ selIs I (poolManagerSelBytes 7)) (h8 : ¬ selIs I (poolManagerSelBytes 8)) (h9 : ¬ selIs I (poolManagerSelBytes 9)) (h10 : ¬ selIs I (poolManagerSelBytes 10)) (h11 : ¬ selIs I (poolManagerSelBytes 11)) (h12 : ¬ selIs I (poolManagerSelBytes 12)) (h13 : ¬ selIs I (poolManagerSelBytes 13)) (h14 : ¬ selIs I (poolManagerSelBytes 14)) (h15 : ¬ selIs I (poolManagerSelBytes 15)) (h16 : ¬ selIs I (poolManagerSelBytes 16)) (h17 : ¬ selIs I (poolManagerSelBytes 17)) (h18 : ¬ selIs I (poolManagerSelBytes 18)) (h19 : ¬ selIs I (poolManagerSelBytes 19)) (h20 : ¬ selIs I (poolManagerSelBytes 20)) (h21 : ¬ selIs I (poolManagerSelBytes 21))
    (hsel : selIs I (poolManagerSelBytes 22)) :
    dispatchMsg contract I.calldata = some exttload_bytes32_arrayTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition, settleTransition, initializeTransition, mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition, approveTransition, unlockTransition, donateTransition, setOperatorTransition, allowanceTransition, modifyLiquidityTransition, syncTransition, ownerTransition, updateDynamicLPFeeTransition]) (post := [exttload_bytes32Transition, swapTransition, isOperatorTransition, clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := exttload_bytes32_arrayTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settleSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [initializeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [extsload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [extsload_bytes32_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [extsload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [setProtocolFeeControllerSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [collectProtocolFeesSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [settleForSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [unlockSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [donateSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [setOperatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [allowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [modifyLiquiditySelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [syncSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [ownerSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [updateDynamicLPFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
  · rw [exttload_bytes32_arraySelectorOf]; exact hsel

theorem poolManagerDispatch_exttload_bytes32 {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2)) (h3 : ¬ selIs I (poolManagerSelBytes 3)) (h4 : ¬ selIs I (poolManagerSelBytes 4)) (h5 : ¬ selIs I (poolManagerSelBytes 5)) (h6 : ¬ selIs I (poolManagerSelBytes 6)) (h7 : ¬ selIs I (poolManagerSelBytes 7)) (h8 : ¬ selIs I (poolManagerSelBytes 8)) (h9 : ¬ selIs I (poolManagerSelBytes 9)) (h10 : ¬ selIs I (poolManagerSelBytes 10)) (h11 : ¬ selIs I (poolManagerSelBytes 11)) (h12 : ¬ selIs I (poolManagerSelBytes 12)) (h13 : ¬ selIs I (poolManagerSelBytes 13)) (h14 : ¬ selIs I (poolManagerSelBytes 14)) (h15 : ¬ selIs I (poolManagerSelBytes 15)) (h16 : ¬ selIs I (poolManagerSelBytes 16)) (h17 : ¬ selIs I (poolManagerSelBytes 17)) (h18 : ¬ selIs I (poolManagerSelBytes 18)) (h19 : ¬ selIs I (poolManagerSelBytes 19)) (h20 : ¬ selIs I (poolManagerSelBytes 20)) (h21 : ¬ selIs I (poolManagerSelBytes 21)) (h22 : ¬ selIs I (poolManagerSelBytes 22))
    (hsel : selIs I (poolManagerSelBytes 23)) :
    dispatchMsg contract I.calldata = some exttload_bytes32Transition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition, settleTransition, initializeTransition, mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition, approveTransition, unlockTransition, donateTransition, setOperatorTransition, allowanceTransition, modifyLiquidityTransition, syncTransition, ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition]) (post := [swapTransition, isOperatorTransition, clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := exttload_bytes32Transition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settleSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [initializeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [extsload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [extsload_bytes32_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [extsload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [setProtocolFeeControllerSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [collectProtocolFeesSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [settleForSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [unlockSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [donateSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [setOperatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [allowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [modifyLiquiditySelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [syncSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [ownerSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [updateDynamicLPFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [exttload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h22
  · rw [exttload_bytes32SelectorOf]; exact hsel

theorem poolManagerDispatch_swap {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2)) (h3 : ¬ selIs I (poolManagerSelBytes 3)) (h4 : ¬ selIs I (poolManagerSelBytes 4)) (h5 : ¬ selIs I (poolManagerSelBytes 5)) (h6 : ¬ selIs I (poolManagerSelBytes 6)) (h7 : ¬ selIs I (poolManagerSelBytes 7)) (h8 : ¬ selIs I (poolManagerSelBytes 8)) (h9 : ¬ selIs I (poolManagerSelBytes 9)) (h10 : ¬ selIs I (poolManagerSelBytes 10)) (h11 : ¬ selIs I (poolManagerSelBytes 11)) (h12 : ¬ selIs I (poolManagerSelBytes 12)) (h13 : ¬ selIs I (poolManagerSelBytes 13)) (h14 : ¬ selIs I (poolManagerSelBytes 14)) (h15 : ¬ selIs I (poolManagerSelBytes 15)) (h16 : ¬ selIs I (poolManagerSelBytes 16)) (h17 : ¬ selIs I (poolManagerSelBytes 17)) (h18 : ¬ selIs I (poolManagerSelBytes 18)) (h19 : ¬ selIs I (poolManagerSelBytes 19)) (h20 : ¬ selIs I (poolManagerSelBytes 20)) (h21 : ¬ selIs I (poolManagerSelBytes 21)) (h22 : ¬ selIs I (poolManagerSelBytes 22)) (h23 : ¬ selIs I (poolManagerSelBytes 23))
    (hsel : selIs I (poolManagerSelBytes 24)) :
    dispatchMsg contract I.calldata = some swapTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition, settleTransition, initializeTransition, mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition, approveTransition, unlockTransition, donateTransition, setOperatorTransition, allowanceTransition, modifyLiquidityTransition, syncTransition, ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition]) (post := [isOperatorTransition, clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := swapTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settleSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [initializeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [extsload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [extsload_bytes32_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [extsload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [setProtocolFeeControllerSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [collectProtocolFeesSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [settleForSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [unlockSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [donateSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [setOperatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [allowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [modifyLiquiditySelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [syncSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [ownerSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [updateDynamicLPFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [exttload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [exttload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h23
  · rw [swapSelectorOf]; exact hsel

theorem poolManagerDispatch_isOperator {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2)) (h3 : ¬ selIs I (poolManagerSelBytes 3)) (h4 : ¬ selIs I (poolManagerSelBytes 4)) (h5 : ¬ selIs I (poolManagerSelBytes 5)) (h6 : ¬ selIs I (poolManagerSelBytes 6)) (h7 : ¬ selIs I (poolManagerSelBytes 7)) (h8 : ¬ selIs I (poolManagerSelBytes 8)) (h9 : ¬ selIs I (poolManagerSelBytes 9)) (h10 : ¬ selIs I (poolManagerSelBytes 10)) (h11 : ¬ selIs I (poolManagerSelBytes 11)) (h12 : ¬ selIs I (poolManagerSelBytes 12)) (h13 : ¬ selIs I (poolManagerSelBytes 13)) (h14 : ¬ selIs I (poolManagerSelBytes 14)) (h15 : ¬ selIs I (poolManagerSelBytes 15)) (h16 : ¬ selIs I (poolManagerSelBytes 16)) (h17 : ¬ selIs I (poolManagerSelBytes 17)) (h18 : ¬ selIs I (poolManagerSelBytes 18)) (h19 : ¬ selIs I (poolManagerSelBytes 19)) (h20 : ¬ selIs I (poolManagerSelBytes 20)) (h21 : ¬ selIs I (poolManagerSelBytes 21)) (h22 : ¬ selIs I (poolManagerSelBytes 22)) (h23 : ¬ selIs I (poolManagerSelBytes 23)) (h24 : ¬ selIs I (poolManagerSelBytes 24))
    (hsel : selIs I (poolManagerSelBytes 25)) :
    dispatchMsg contract I.calldata = some isOperatorTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition, settleTransition, initializeTransition, mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition, approveTransition, unlockTransition, donateTransition, setOperatorTransition, allowanceTransition, modifyLiquidityTransition, syncTransition, ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition]) (post := [clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := isOperatorTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settleSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [initializeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [extsload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [extsload_bytes32_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [extsload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [setProtocolFeeControllerSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [collectProtocolFeesSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [settleForSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [unlockSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [donateSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [setOperatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [allowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [modifyLiquiditySelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [syncSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [ownerSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [updateDynamicLPFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [exttload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [exttload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [swapSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
  · rw [isOperatorSelectorOf]; exact hsel

theorem poolManagerDispatch_clear {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2)) (h3 : ¬ selIs I (poolManagerSelBytes 3)) (h4 : ¬ selIs I (poolManagerSelBytes 4)) (h5 : ¬ selIs I (poolManagerSelBytes 5)) (h6 : ¬ selIs I (poolManagerSelBytes 6)) (h7 : ¬ selIs I (poolManagerSelBytes 7)) (h8 : ¬ selIs I (poolManagerSelBytes 8)) (h9 : ¬ selIs I (poolManagerSelBytes 9)) (h10 : ¬ selIs I (poolManagerSelBytes 10)) (h11 : ¬ selIs I (poolManagerSelBytes 11)) (h12 : ¬ selIs I (poolManagerSelBytes 12)) (h13 : ¬ selIs I (poolManagerSelBytes 13)) (h14 : ¬ selIs I (poolManagerSelBytes 14)) (h15 : ¬ selIs I (poolManagerSelBytes 15)) (h16 : ¬ selIs I (poolManagerSelBytes 16)) (h17 : ¬ selIs I (poolManagerSelBytes 17)) (h18 : ¬ selIs I (poolManagerSelBytes 18)) (h19 : ¬ selIs I (poolManagerSelBytes 19)) (h20 : ¬ selIs I (poolManagerSelBytes 20)) (h21 : ¬ selIs I (poolManagerSelBytes 21)) (h22 : ¬ selIs I (poolManagerSelBytes 22)) (h23 : ¬ selIs I (poolManagerSelBytes 23)) (h24 : ¬ selIs I (poolManagerSelBytes 24)) (h25 : ¬ selIs I (poolManagerSelBytes 25))
    (hsel : selIs I (poolManagerSelBytes 26)) :
    dispatchMsg contract I.calldata = some clearTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition, settleTransition, initializeTransition, mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition, approveTransition, unlockTransition, donateTransition, setOperatorTransition, allowanceTransition, modifyLiquidityTransition, syncTransition, ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition, isOperatorTransition]) (post := [setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := clearTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settleSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [initializeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [extsload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [extsload_bytes32_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [extsload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [setProtocolFeeControllerSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [collectProtocolFeesSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [settleForSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [unlockSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [donateSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [setOperatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [allowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [modifyLiquiditySelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [syncSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [ownerSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [updateDynamicLPFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [exttload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [exttload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [swapSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [isOperatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h25
  · rw [clearSelectorOf]; exact hsel

theorem poolManagerDispatch_setProtocolFee {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2)) (h3 : ¬ selIs I (poolManagerSelBytes 3)) (h4 : ¬ selIs I (poolManagerSelBytes 4)) (h5 : ¬ selIs I (poolManagerSelBytes 5)) (h6 : ¬ selIs I (poolManagerSelBytes 6)) (h7 : ¬ selIs I (poolManagerSelBytes 7)) (h8 : ¬ selIs I (poolManagerSelBytes 8)) (h9 : ¬ selIs I (poolManagerSelBytes 9)) (h10 : ¬ selIs I (poolManagerSelBytes 10)) (h11 : ¬ selIs I (poolManagerSelBytes 11)) (h12 : ¬ selIs I (poolManagerSelBytes 12)) (h13 : ¬ selIs I (poolManagerSelBytes 13)) (h14 : ¬ selIs I (poolManagerSelBytes 14)) (h15 : ¬ selIs I (poolManagerSelBytes 15)) (h16 : ¬ selIs I (poolManagerSelBytes 16)) (h17 : ¬ selIs I (poolManagerSelBytes 17)) (h18 : ¬ selIs I (poolManagerSelBytes 18)) (h19 : ¬ selIs I (poolManagerSelBytes 19)) (h20 : ¬ selIs I (poolManagerSelBytes 20)) (h21 : ¬ selIs I (poolManagerSelBytes 21)) (h22 : ¬ selIs I (poolManagerSelBytes 22)) (h23 : ¬ selIs I (poolManagerSelBytes 23)) (h24 : ¬ selIs I (poolManagerSelBytes 24)) (h25 : ¬ selIs I (poolManagerSelBytes 25)) (h26 : ¬ selIs I (poolManagerSelBytes 26))
    (hsel : selIs I (poolManagerSelBytes 27)) :
    dispatchMsg contract I.calldata = some setProtocolFeeTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition, settleTransition, initializeTransition, mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition, approveTransition, unlockTransition, donateTransition, setOperatorTransition, allowanceTransition, modifyLiquidityTransition, syncTransition, ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition, isOperatorTransition, clearTransition]) (post := [protocolFeeControllerTransition, transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := setProtocolFeeTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settleSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [initializeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [extsload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [extsload_bytes32_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [extsload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [setProtocolFeeControllerSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [collectProtocolFeesSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [settleForSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [unlockSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [donateSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [setOperatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [allowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [modifyLiquiditySelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [syncSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [ownerSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [updateDynamicLPFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [exttload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [exttload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [swapSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [isOperatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [clearSelectorOf]; exact Bool.eq_false_of_not_eq_true h26
  · rw [setProtocolFeeSelectorOf]; exact hsel

theorem poolManagerDispatch_protocolFeeController {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2)) (h3 : ¬ selIs I (poolManagerSelBytes 3)) (h4 : ¬ selIs I (poolManagerSelBytes 4)) (h5 : ¬ selIs I (poolManagerSelBytes 5)) (h6 : ¬ selIs I (poolManagerSelBytes 6)) (h7 : ¬ selIs I (poolManagerSelBytes 7)) (h8 : ¬ selIs I (poolManagerSelBytes 8)) (h9 : ¬ selIs I (poolManagerSelBytes 9)) (h10 : ¬ selIs I (poolManagerSelBytes 10)) (h11 : ¬ selIs I (poolManagerSelBytes 11)) (h12 : ¬ selIs I (poolManagerSelBytes 12)) (h13 : ¬ selIs I (poolManagerSelBytes 13)) (h14 : ¬ selIs I (poolManagerSelBytes 14)) (h15 : ¬ selIs I (poolManagerSelBytes 15)) (h16 : ¬ selIs I (poolManagerSelBytes 16)) (h17 : ¬ selIs I (poolManagerSelBytes 17)) (h18 : ¬ selIs I (poolManagerSelBytes 18)) (h19 : ¬ selIs I (poolManagerSelBytes 19)) (h20 : ¬ selIs I (poolManagerSelBytes 20)) (h21 : ¬ selIs I (poolManagerSelBytes 21)) (h22 : ¬ selIs I (poolManagerSelBytes 22)) (h23 : ¬ selIs I (poolManagerSelBytes 23)) (h24 : ¬ selIs I (poolManagerSelBytes 24)) (h25 : ¬ selIs I (poolManagerSelBytes 25)) (h26 : ¬ selIs I (poolManagerSelBytes 26)) (h27 : ¬ selIs I (poolManagerSelBytes 27))
    (hsel : selIs I (poolManagerSelBytes 28)) :
    dispatchMsg contract I.calldata = some protocolFeeControllerTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition, settleTransition, initializeTransition, mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition, approveTransition, unlockTransition, donateTransition, setOperatorTransition, allowanceTransition, modifyLiquidityTransition, syncTransition, ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition, isOperatorTransition, clearTransition, setProtocolFeeTransition]) (post := [transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := protocolFeeControllerTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settleSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [initializeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [extsload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [extsload_bytes32_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [extsload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [setProtocolFeeControllerSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [collectProtocolFeesSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [settleForSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [unlockSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [donateSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [setOperatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [allowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [modifyLiquiditySelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [syncSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [ownerSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [updateDynamicLPFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [exttload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [exttload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [swapSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [isOperatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [clearSelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [setProtocolFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
  · rw [protocolFeeControllerSelectorOf]; exact hsel

theorem poolManagerDispatch_transferOwnership {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2)) (h3 : ¬ selIs I (poolManagerSelBytes 3)) (h4 : ¬ selIs I (poolManagerSelBytes 4)) (h5 : ¬ selIs I (poolManagerSelBytes 5)) (h6 : ¬ selIs I (poolManagerSelBytes 6)) (h7 : ¬ selIs I (poolManagerSelBytes 7)) (h8 : ¬ selIs I (poolManagerSelBytes 8)) (h9 : ¬ selIs I (poolManagerSelBytes 9)) (h10 : ¬ selIs I (poolManagerSelBytes 10)) (h11 : ¬ selIs I (poolManagerSelBytes 11)) (h12 : ¬ selIs I (poolManagerSelBytes 12)) (h13 : ¬ selIs I (poolManagerSelBytes 13)) (h14 : ¬ selIs I (poolManagerSelBytes 14)) (h15 : ¬ selIs I (poolManagerSelBytes 15)) (h16 : ¬ selIs I (poolManagerSelBytes 16)) (h17 : ¬ selIs I (poolManagerSelBytes 17)) (h18 : ¬ selIs I (poolManagerSelBytes 18)) (h19 : ¬ selIs I (poolManagerSelBytes 19)) (h20 : ¬ selIs I (poolManagerSelBytes 20)) (h21 : ¬ selIs I (poolManagerSelBytes 21)) (h22 : ¬ selIs I (poolManagerSelBytes 22)) (h23 : ¬ selIs I (poolManagerSelBytes 23)) (h24 : ¬ selIs I (poolManagerSelBytes 24)) (h25 : ¬ selIs I (poolManagerSelBytes 25)) (h26 : ¬ selIs I (poolManagerSelBytes 26)) (h27 : ¬ selIs I (poolManagerSelBytes 27)) (h28 : ¬ selIs I (poolManagerSelBytes 28))
    (hsel : selIs I (poolManagerSelBytes 29)) :
    dispatchMsg contract I.calldata = some transferOwnershipTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition, settleTransition, initializeTransition, mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition, approveTransition, unlockTransition, donateTransition, setOperatorTransition, allowanceTransition, modifyLiquidityTransition, syncTransition, ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition, isOperatorTransition, clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition]) (post := [burnTransition, protocolFeesAccruedTransition, transferFromTransition])
    (ti := transferOwnershipTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settleSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [initializeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [extsload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [extsload_bytes32_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [extsload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [setProtocolFeeControllerSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [collectProtocolFeesSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [settleForSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [unlockSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [donateSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [setOperatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [allowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [modifyLiquiditySelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [syncSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [ownerSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [updateDynamicLPFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [exttload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [exttload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [swapSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [isOperatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [clearSelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [setProtocolFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [protocolFeeControllerSelectorOf]; exact Bool.eq_false_of_not_eq_true h28
  · rw [transferOwnershipSelectorOf]; exact hsel

theorem poolManagerDispatch_burn {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2)) (h3 : ¬ selIs I (poolManagerSelBytes 3)) (h4 : ¬ selIs I (poolManagerSelBytes 4)) (h5 : ¬ selIs I (poolManagerSelBytes 5)) (h6 : ¬ selIs I (poolManagerSelBytes 6)) (h7 : ¬ selIs I (poolManagerSelBytes 7)) (h8 : ¬ selIs I (poolManagerSelBytes 8)) (h9 : ¬ selIs I (poolManagerSelBytes 9)) (h10 : ¬ selIs I (poolManagerSelBytes 10)) (h11 : ¬ selIs I (poolManagerSelBytes 11)) (h12 : ¬ selIs I (poolManagerSelBytes 12)) (h13 : ¬ selIs I (poolManagerSelBytes 13)) (h14 : ¬ selIs I (poolManagerSelBytes 14)) (h15 : ¬ selIs I (poolManagerSelBytes 15)) (h16 : ¬ selIs I (poolManagerSelBytes 16)) (h17 : ¬ selIs I (poolManagerSelBytes 17)) (h18 : ¬ selIs I (poolManagerSelBytes 18)) (h19 : ¬ selIs I (poolManagerSelBytes 19)) (h20 : ¬ selIs I (poolManagerSelBytes 20)) (h21 : ¬ selIs I (poolManagerSelBytes 21)) (h22 : ¬ selIs I (poolManagerSelBytes 22)) (h23 : ¬ selIs I (poolManagerSelBytes 23)) (h24 : ¬ selIs I (poolManagerSelBytes 24)) (h25 : ¬ selIs I (poolManagerSelBytes 25)) (h26 : ¬ selIs I (poolManagerSelBytes 26)) (h27 : ¬ selIs I (poolManagerSelBytes 27)) (h28 : ¬ selIs I (poolManagerSelBytes 28)) (h29 : ¬ selIs I (poolManagerSelBytes 29))
    (hsel : selIs I (poolManagerSelBytes 30)) :
    dispatchMsg contract I.calldata = some burnTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition, settleTransition, initializeTransition, mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition, approveTransition, unlockTransition, donateTransition, setOperatorTransition, allowanceTransition, modifyLiquidityTransition, syncTransition, ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition, isOperatorTransition, clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition]) (post := [protocolFeesAccruedTransition, transferFromTransition])
    (ti := burnTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settleSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [initializeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [extsload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [extsload_bytes32_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [extsload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [setProtocolFeeControllerSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [collectProtocolFeesSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [settleForSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [unlockSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [donateSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [setOperatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [allowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [modifyLiquiditySelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [syncSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [ownerSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [updateDynamicLPFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [exttload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [exttload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [swapSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [isOperatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [clearSelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [setProtocolFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [protocolFeeControllerSelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [transferOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
  · rw [burnSelectorOf]; exact hsel

theorem poolManagerDispatch_protocolFeesAccrued {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2)) (h3 : ¬ selIs I (poolManagerSelBytes 3)) (h4 : ¬ selIs I (poolManagerSelBytes 4)) (h5 : ¬ selIs I (poolManagerSelBytes 5)) (h6 : ¬ selIs I (poolManagerSelBytes 6)) (h7 : ¬ selIs I (poolManagerSelBytes 7)) (h8 : ¬ selIs I (poolManagerSelBytes 8)) (h9 : ¬ selIs I (poolManagerSelBytes 9)) (h10 : ¬ selIs I (poolManagerSelBytes 10)) (h11 : ¬ selIs I (poolManagerSelBytes 11)) (h12 : ¬ selIs I (poolManagerSelBytes 12)) (h13 : ¬ selIs I (poolManagerSelBytes 13)) (h14 : ¬ selIs I (poolManagerSelBytes 14)) (h15 : ¬ selIs I (poolManagerSelBytes 15)) (h16 : ¬ selIs I (poolManagerSelBytes 16)) (h17 : ¬ selIs I (poolManagerSelBytes 17)) (h18 : ¬ selIs I (poolManagerSelBytes 18)) (h19 : ¬ selIs I (poolManagerSelBytes 19)) (h20 : ¬ selIs I (poolManagerSelBytes 20)) (h21 : ¬ selIs I (poolManagerSelBytes 21)) (h22 : ¬ selIs I (poolManagerSelBytes 22)) (h23 : ¬ selIs I (poolManagerSelBytes 23)) (h24 : ¬ selIs I (poolManagerSelBytes 24)) (h25 : ¬ selIs I (poolManagerSelBytes 25)) (h26 : ¬ selIs I (poolManagerSelBytes 26)) (h27 : ¬ selIs I (poolManagerSelBytes 27)) (h28 : ¬ selIs I (poolManagerSelBytes 28)) (h29 : ¬ selIs I (poolManagerSelBytes 29)) (h30 : ¬ selIs I (poolManagerSelBytes 30))
    (hsel : selIs I (poolManagerSelBytes 31)) :
    dispatchMsg contract I.calldata = some protocolFeesAccruedTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition, settleTransition, initializeTransition, mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition, approveTransition, unlockTransition, donateTransition, setOperatorTransition, allowanceTransition, modifyLiquidityTransition, syncTransition, ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition, isOperatorTransition, clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition, burnTransition]) (post := [transferFromTransition])
    (ti := protocolFeesAccruedTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settleSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [initializeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [extsload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [extsload_bytes32_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [extsload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [setProtocolFeeControllerSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [collectProtocolFeesSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [settleForSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [unlockSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [donateSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [setOperatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [allowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [modifyLiquiditySelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [syncSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [ownerSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [updateDynamicLPFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [exttload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [exttload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [swapSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [isOperatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [clearSelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [setProtocolFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [protocolFeeControllerSelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [transferOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [burnSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
  · rw [protocolFeesAccruedSelectorOf]; exact hsel

theorem poolManagerDispatch_transferFrom {I : ExecutionEnv} (h0 : ¬ selIs I (poolManagerSelBytes 0)) (h1 : ¬ selIs I (poolManagerSelBytes 1)) (h2 : ¬ selIs I (poolManagerSelBytes 2)) (h3 : ¬ selIs I (poolManagerSelBytes 3)) (h4 : ¬ selIs I (poolManagerSelBytes 4)) (h5 : ¬ selIs I (poolManagerSelBytes 5)) (h6 : ¬ selIs I (poolManagerSelBytes 6)) (h7 : ¬ selIs I (poolManagerSelBytes 7)) (h8 : ¬ selIs I (poolManagerSelBytes 8)) (h9 : ¬ selIs I (poolManagerSelBytes 9)) (h10 : ¬ selIs I (poolManagerSelBytes 10)) (h11 : ¬ selIs I (poolManagerSelBytes 11)) (h12 : ¬ selIs I (poolManagerSelBytes 12)) (h13 : ¬ selIs I (poolManagerSelBytes 13)) (h14 : ¬ selIs I (poolManagerSelBytes 14)) (h15 : ¬ selIs I (poolManagerSelBytes 15)) (h16 : ¬ selIs I (poolManagerSelBytes 16)) (h17 : ¬ selIs I (poolManagerSelBytes 17)) (h18 : ¬ selIs I (poolManagerSelBytes 18)) (h19 : ¬ selIs I (poolManagerSelBytes 19)) (h20 : ¬ selIs I (poolManagerSelBytes 20)) (h21 : ¬ selIs I (poolManagerSelBytes 21)) (h22 : ¬ selIs I (poolManagerSelBytes 22)) (h23 : ¬ selIs I (poolManagerSelBytes 23)) (h24 : ¬ selIs I (poolManagerSelBytes 24)) (h25 : ¬ selIs I (poolManagerSelBytes 25)) (h26 : ¬ selIs I (poolManagerSelBytes 26)) (h27 : ¬ selIs I (poolManagerSelBytes 27)) (h28 : ¬ selIs I (poolManagerSelBytes 28)) (h29 : ¬ selIs I (poolManagerSelBytes 29)) (h30 : ¬ selIs I (poolManagerSelBytes 30)) (h31 : ¬ selIs I (poolManagerSelBytes 31))
    (hsel : selIs I (poolManagerSelBytes 32)) :
    dispatchMsg contract I.calldata = some transferFromTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [balanceOfTransition, supportsInterfaceTransition, transferTransition, settleTransition, initializeTransition, mintTransition, extsload_bytes32Transition, extsload_bytes32_uint256Transition, extsload_bytes32_arrayTransition, takeTransition, setProtocolFeeControllerTransition, collectProtocolFeesTransition, settleForTransition, approveTransition, unlockTransition, donateTransition, setOperatorTransition, allowanceTransition, modifyLiquidityTransition, syncTransition, ownerTransition, updateDynamicLPFeeTransition, exttload_bytes32_arrayTransition, exttload_bytes32Transition, swapTransition, isOperatorTransition, clearTransition, setProtocolFeeTransition, protocolFeeControllerTransition, transferOwnershipTransition, burnTransition, protocolFeesAccruedTransition]) (post := [])
    (ti := transferFromTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [supportsInterfaceSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settleSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [initializeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [extsload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [extsload_bytes32_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [extsload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [setProtocolFeeControllerSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [collectProtocolFeesSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [settleForSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [unlockSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [donateSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [setOperatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [allowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [modifyLiquiditySelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [syncSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [ownerSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [updateDynamicLPFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [exttload_bytes32_arraySelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [exttload_bytes32SelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [swapSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [isOperatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [clearSelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [setProtocolFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [protocolFeeControllerSelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [transferOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [burnSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
    · rw [protocolFeesAccruedSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
  · rw [transferFromSelectorOf]; exact hsel

theorem poolManagerDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd, transitions_eq]
  refine dispatchList_none_short _ ?_ h
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [balanceOfSelectorOf]; rfl
  · rw [supportsInterfaceSelectorOf]; rfl
  · rw [transferSelectorOf]; rfl
  · rw [settleSelectorOf]; rfl
  · rw [initializeSelectorOf]; rfl
  · rw [mintSelectorOf]; rfl
  · rw [extsload_bytes32SelectorOf]; rfl
  · rw [extsload_bytes32_uint256SelectorOf]; rfl
  · rw [extsload_bytes32_arraySelectorOf]; rfl
  · rw [takeSelectorOf]; rfl
  · rw [setProtocolFeeControllerSelectorOf]; rfl
  · rw [collectProtocolFeesSelectorOf]; rfl
  · rw [settleForSelectorOf]; rfl
  · rw [approveSelectorOf]; rfl
  · rw [unlockSelectorOf]; rfl
  · rw [donateSelectorOf]; rfl
  · rw [setOperatorSelectorOf]; rfl
  · rw [allowanceSelectorOf]; rfl
  · rw [modifyLiquiditySelectorOf]; rfl
  · rw [syncSelectorOf]; rfl
  · rw [ownerSelectorOf]; rfl
  · rw [updateDynamicLPFeeSelectorOf]; rfl
  · rw [exttload_bytes32_arraySelectorOf]; rfl
  · rw [exttload_bytes32SelectorOf]; rfl
  · rw [swapSelectorOf]; rfl
  · rw [isOperatorSelectorOf]; rfl
  · rw [clearSelectorOf]; rfl
  · rw [setProtocolFeeSelectorOf]; rfl
  · rw [protocolFeeControllerSelectorOf]; rfl
  · rw [transferOwnershipSelectorOf]; rfl
  · rw [burnSelectorOf]; rfl
  · rw [protocolFeesAccruedSelectorOf]; rfl
  · rw [transferFromSelectorOf]; rfl

theorem poolManagerDispatch_none_nomatch {I : ExecutionEnv}
    (hnm : ∀ i, i < 33 → (poolManagerSelBytes i == I.calldata.extract 0 4) = false) :
    dispatchMsg contract I.calldata = none := by
  refine dispatchMsg_none_of_all_ne (contract := contract) (cd := I.calldata) (by rfl) (by rfl) ?_
  intro t ht
  rw [transitions_eq] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [balanceOfSelectorOf]; exact hnm 0 (by omega)
  · rw [supportsInterfaceSelectorOf]; exact hnm 1 (by omega)
  · rw [transferSelectorOf]; exact hnm 2 (by omega)
  · rw [settleSelectorOf]; exact hnm 3 (by omega)
  · rw [initializeSelectorOf]; exact hnm 4 (by omega)
  · rw [mintSelectorOf]; exact hnm 5 (by omega)
  · rw [extsload_bytes32SelectorOf]; exact hnm 6 (by omega)
  · rw [extsload_bytes32_uint256SelectorOf]; exact hnm 7 (by omega)
  · rw [extsload_bytes32_arraySelectorOf]; exact hnm 8 (by omega)
  · rw [takeSelectorOf]; exact hnm 9 (by omega)
  · rw [setProtocolFeeControllerSelectorOf]; exact hnm 10 (by omega)
  · rw [collectProtocolFeesSelectorOf]; exact hnm 11 (by omega)
  · rw [settleForSelectorOf]; exact hnm 12 (by omega)
  · rw [approveSelectorOf]; exact hnm 13 (by omega)
  · rw [unlockSelectorOf]; exact hnm 14 (by omega)
  · rw [donateSelectorOf]; exact hnm 15 (by omega)
  · rw [setOperatorSelectorOf]; exact hnm 16 (by omega)
  · rw [allowanceSelectorOf]; exact hnm 17 (by omega)
  · rw [modifyLiquiditySelectorOf]; exact hnm 18 (by omega)
  · rw [syncSelectorOf]; exact hnm 19 (by omega)
  · rw [ownerSelectorOf]; exact hnm 20 (by omega)
  · rw [updateDynamicLPFeeSelectorOf]; exact hnm 21 (by omega)
  · rw [exttload_bytes32_arraySelectorOf]; exact hnm 22 (by omega)
  · rw [exttload_bytes32SelectorOf]; exact hnm 23 (by omega)
  · rw [swapSelectorOf]; exact hnm 24 (by omega)
  · rw [isOperatorSelectorOf]; exact hnm 25 (by omega)
  · rw [clearSelectorOf]; exact hnm 26 (by omega)
  · rw [setProtocolFeeSelectorOf]; exact hnm 27 (by omega)
  · rw [protocolFeeControllerSelectorOf]; exact hnm 28 (by omega)
  · rw [transferOwnershipSelectorOf]; exact hnm 29 (by omega)
  · rw [burnSelectorOf]; exact hnm 30 (by omega)
  · rw [protocolFeesAccruedSelectorOf]; exact hnm 31 (by omega)
  · rw [transferFromSelectorOf]; exact hnm 32 (by omega)

end Benchmarks.UniswapV4PoolManager
