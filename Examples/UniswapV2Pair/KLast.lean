import Examples.UniswapV2Pair.Dispatch
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `kLast()` getter -/

def kLastWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  uniswapSlotWord ⟨11⟩ σ I

/-- The Solm `kLast()` body returns the uint256 stored in slot 11. -/
theorem uniswapKLastBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "kLast" = none) :
    ExecTransitionBody config contract evm locals kLastTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat)))) := by
  simpa [kLastTransition] using
    uniswapUint256GetterBodyReturns (slot := ⟨11⟩) (ref := kLastRef)
      (er := ({ base := "kLast", steps := [] } : EvaledStorageRef)) evm locals h
      (by simpa [kLastRef] using hlocals)
      (by simp [evalStorageRef, evalStorageRefSteps, kLastRef, EvalResult.bind, pure, bind])
      (by decide) (by rfl)

/-- From `kLast()`'s external body entry (pc 1117), the bytecode returns slot 11. -/
theorem uniswapX_kLast {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1117⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (kLastWord σ I)) := by
  exact RD.uniswapWordGetterExternal (entry := ⟨1117⟩) (routine := ⟨4069⟩)
    (slot := ⟨11⟩) hreach uniswap_word_getter_entry_wf uniswap_word_slot_getter_wf
    (by jump_dest) (by jump_dest)

theorem uniswapDecode_kLast {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (kLastTransition.params.map Param.name)
      (transitionSignature kLastTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-- `kLast()` body core, parameterized by dispatcher/decode facts owned by `Correct`. -/
theorem uniswapKLastBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some kLastTransition)
    (hdecode :
      decodeCalldata (kLastTransition.params.map Param.name)
        (transitionSignature kLastTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1117⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ kLastTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int (Int.ofNat (kLastWord σ_solm I).toNat)))) := by
    simpa [kLastWord, uniswapSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      uniswapKLastBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact uniswapUint256GetterBodyCore (entry := ⟨1117⟩) (routine := ⟨4069⟩) (slot := ⟨11⟩)
    hcode hdispatch hdecode hreach hAccounts uniswap_word_getter_entry_wf
    uniswap_word_slot_getter_wf (by jump_dest) (by rfl)
    (by simpa [kLastWord] using hbody)

/-- `kLast()` body wrapper for top-level routing: selector match supplies decode and reach. -/
theorem uniswapKLastBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x74, 0x64, 0xfc, 0x3d]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some kLastTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x74, 0x64, 0xfc, 0x3d]⟩ rfl hsel
  exact uniswapKLastBodyCore hcode hwv hdispatch (uniswapDecode_kLast hsz)
    (uniswapReachKLastBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts

end UniswapV2Pair
