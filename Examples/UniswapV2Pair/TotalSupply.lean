import Examples.UniswapV2Pair.Dispatch
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `totalSupply()` getter -/

def totalSupplyWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  uniswapSlotWord ⟨0⟩ σ I

/-- The Solm `totalSupply()` body returns the uint256 stored in slot 0. -/
theorem uniswapTotalSupplyBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "totalSupply" = none) :
    ExecTransitionBody config contract evm locals totalSupplyTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat)))) := by
  simpa [totalSupplyTransition] using
    uniswapUint256GetterBodyReturns (slot := ⟨0⟩) (ref := totalSupplyRef)
      (er := ({ base := "totalSupply", steps := [] } : EvaledStorageRef)) evm locals h
      (by simpa [totalSupplyRef] using hlocals)
      (by simp [evalStorageRef, evalStorageRefSteps, totalSupplyRef, EvalResult.bind, pure, bind])
      (by decide) (by rfl)

/-- From `totalSupply()`'s external body entry (pc 853), the bytecode returns slot 0. -/
theorem uniswapX_totalSupply {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨853⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (totalSupplyWord σ I)) := by
  exact RD.uniswapWordGetterExternal (entry := ⟨853⟩) (routine := ⟨2932⟩)
    (slot := ⟨0⟩) hreach uniswap_word_getter_entry_wf uniswap_word_slot_getter_wf
    (by jump_dest) (by jump_dest)

theorem uniswapDecode_totalSupply {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (totalSupplyTransition.params.map Param.name)
      (transitionSignature totalSupplyTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-- `totalSupply()` body core, parameterized by dispatcher/decode facts owned by `Correct`. -/
theorem uniswapTotalSupplyBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some totalSupplyTransition)
    (hdecode :
      decodeCalldata (totalSupplyTransition.params.map Param.name)
        (transitionSignature totalSupplyTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨853⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ totalSupplyTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int (Int.ofNat (totalSupplyWord σ_solm I).toNat)))) := by
    simpa [totalSupplyWord, uniswapSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      uniswapTotalSupplyBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact uniswapUint256GetterBodyCore (entry := ⟨853⟩) (routine := ⟨2932⟩) (slot := ⟨0⟩)
    hcode hdispatch hdecode hreach hAccounts uniswap_word_getter_entry_wf
    uniswap_word_slot_getter_wf (by jump_dest) (by rfl)
    (by simpa [totalSupplyWord] using hbody)

/-- `totalSupply()` body wrapper for top-level routing: selector match supplies decode and reach. -/
theorem uniswapTotalSupplyBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some totalSupplyTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ rfl hsel
  exact uniswapTotalSupplyBodyCore hcode hwv hdispatch (uniswapDecode_totalSupply hsz)
    (uniswapReachTotalSupplyBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
    hAccounts

end UniswapV2Pair
