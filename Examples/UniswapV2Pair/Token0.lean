import Examples.UniswapV2Pair.Common
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `token0()` getter -/

def token0Word (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  uniswapSlotWord ⟨6⟩ σ I

abbrev token0ReturnWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  uniswapAddressReturnWord ⟨6⟩ σ I

/-- The Solm `token0()` body returns the address stored in slot 6. -/
theorem uniswapToken0BodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "token0" = none) :
    ExecTransitionBody config contract evm locals token0Transition.body
      (.returned { contract := contract, locals := locals } evm
        (some (.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩)
            solcAddrMask).toNat)))) := by
  simpa [token0Transition] using
    uniswapAddressGetterBodyReturns (slot := ⟨6⟩) (ref := token0Ref)
      (er := ({ base := "token0", steps := [] } : EvaledStorageRef)) evm locals h
      (by simpa [token0Ref] using hlocals)
      (by simp [evalStorageRef, evalStorageRefSteps, token0Ref, EvalResult.bind, pure, bind])
      (by decide) (by rfl)

/-- From `token0()`'s external body entry (pc 817), the bytecode returns slot 6 as an address. -/
theorem uniswapX_token0 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨817⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (token0ReturnWord σ I)) := by
  exact RD.uniswapAddressGetterExternal (entry := ⟨817⟩) (routine := ⟨2917⟩)
    (slot := ⟨6⟩) hreach uniswap_address_getter_entry_wf uniswap_address_slot_getter_wf
    (by jump_dest) (by jump_dest)

theorem uniswapDecode_token0 {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (token0Transition.params.map Param.name)
      (transitionSignature token0Transition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-- `token0()` body core, parameterized by the dispatcher/decode facts still owned by `Correct`. -/
theorem uniswapToken0BodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some token0Transition)
    (hdecode :
      decodeCalldata (token0Transition.params.map Param.name)
        (transitionSignature token0Transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨817⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ token0Transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.address (AccountAddress.ofNat (token0ReturnWord σ_solm I).toNat)))) := by
    simpa [token0Word, token0ReturnWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
      using uniswapToken0BodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact uniswapAddressGetterBodyCore (entry := ⟨817⟩) (routine := ⟨2917⟩) (slot := ⟨6⟩)
    hcode hdispatch hdecode hreach hAccounts uniswap_address_getter_entry_wf
    uniswap_address_slot_getter_wf (by jump_dest) (by rfl)
    (by simpa [token0ReturnWord] using hbody)

end UniswapV2Pair
