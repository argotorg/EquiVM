import Examples.UniswapV2Pair.Dispatch
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `DOMAIN_SEPARATOR()` getter -/

def domainSeparatorWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  uniswapSlotWord ⟨3⟩ σ I

/-- The Solm `DOMAIN_SEPARATOR()` body returns the bytes32 stored in slot 3. -/
theorem uniswapDomainSeparatorBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "DOMAIN_SEPARATOR" = none) :
    ExecTransitionBody config contract evm locals domainSeparatorTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some (.fixedBytes ⟨31, by decide⟩
          (EVM.Word.toBytesBE
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩))))) := by
  simpa [domainSeparatorTransition] using
    uniswapBytes32GetterBodyReturns (slot := ⟨3⟩) (ref := domainSeparatorRef)
      (er := ({ base := "DOMAIN_SEPARATOR", steps := [] } : EvaledStorageRef)) evm locals h
      (by simpa [domainSeparatorRef] using hlocals)
      (by simp [evalStorageRef, evalStorageRefSteps, domainSeparatorRef, EvalResult.bind, pure, bind])
      (by decide) (by rfl)

/-- From `DOMAIN_SEPARATOR()`'s external body entry (pc 971), the bytecode returns slot 3. -/
theorem uniswapX_domainSeparator {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨971⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (domainSeparatorWord σ I)) := by
  exact RD.uniswapWordGetterExternal (entry := ⟨971⟩) (routine := ⟨3133⟩)
    (slot := ⟨3⟩) hreach uniswap_word_getter_entry_wf uniswap_word_slot_getter_wf
    (by jump_dest) (by jump_dest)

theorem uniswapDecode_domainSeparator {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (domainSeparatorTransition.params.map Param.name)
      (transitionSignature domainSeparatorTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-- `DOMAIN_SEPARATOR()` body core, parameterized by dispatcher/decode facts owned by `Correct`. -/
theorem uniswapDomainSeparatorBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some domainSeparatorTransition)
    (hdecode :
      decodeCalldata (domainSeparatorTransition.params.map Param.name)
        (transitionSignature domainSeparatorTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨971⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        domainSeparatorTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.fixedBytes ⟨31, by decide⟩
            (EVM.Word.toBytesBE (domainSeparatorWord σ_solm I))))) := by
    simpa [domainSeparatorWord, uniswapSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      uniswapDomainSeparatorBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact uniswapBytes32GetterBodyCore (entry := ⟨971⟩) (routine := ⟨3133⟩) (slot := ⟨3⟩)
    hcode hdispatch hdecode hreach hAccounts uniswap_word_getter_entry_wf
    uniswap_word_slot_getter_wf (by jump_dest) (by rfl)
    (by simpa [domainSeparatorWord] using hbody)

/-- `DOMAIN_SEPARATOR()` body wrapper for top-level routing: selector match supplies decode and reach. -/
theorem uniswapDomainSeparatorBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x36, 0x44, 0xe5, 0x15]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some domainSeparatorTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x36, 0x44, 0xe5, 0x15]⟩ rfl hsel
  exact uniswapDomainSeparatorBodyCore hcode hwv hdispatch
    (uniswapDecode_domainSeparator hsz)
    (uniswapReachDomainSeparatorBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
    hAccounts

end UniswapV2Pair
