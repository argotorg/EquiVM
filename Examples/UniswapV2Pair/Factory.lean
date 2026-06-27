import Examples.UniswapV2Pair.Common
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `factory()` getter -/

def factoryWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  uniswapSlotWord ⟨5⟩ σ I

abbrev factoryReturnWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  uniswapAddressReturnWord ⟨5⟩ σ I

/-- The Solm `factory()` body returns the address stored in slot 5. -/
theorem uniswapFactoryBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "factory" = none) :
    ExecTransitionBody config contract evm locals factoryTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some (.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)
            solcAddrMask).toNat)))) := by
  simpa [factoryTransition] using
    uniswapAddressGetterBodyReturns (slot := ⟨5⟩) (ref := factoryRef)
      (er := ({ base := "factory", steps := [] } : EvaledStorageRef)) evm locals h
      (by simpa [factoryRef] using hlocals)
      (by simp [evalStorageRef, evalStorageRefSteps, factoryRef, EvalResult.bind, pure, bind])
      (by decide) (by rfl)

/-- From `factory()`'s external body entry (pc 1324), the bytecode returns slot 5 as an address. -/
theorem uniswapX_factory {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1324⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (factoryReturnWord σ I)) := by
  exact RD.uniswapAddressGetterExternal (entry := ⟨1324⟩) (routine := ⟨5443⟩)
    (slot := ⟨5⟩) hreach uniswap_address_getter_entry_wf uniswap_address_slot_getter_wf
    (by jump_dest) (by jump_dest)

theorem uniswapDecode_factory {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (factoryTransition.params.map Param.name)
      (transitionSignature factoryTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-- `factory()` body core, parameterized by the dispatcher/decode facts still owned by `Correct`. -/
theorem uniswapFactoryBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some factoryTransition)
    (hdecode :
      decodeCalldata (factoryTransition.params.map Param.name)
        (transitionSignature factoryTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1324⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ factoryTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.address (AccountAddress.ofNat (factoryReturnWord σ_solm I).toNat)))) := by
    simpa [factoryWord, factoryReturnWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
      using uniswapFactoryBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact uniswapAddressGetterBodyCore (entry := ⟨1324⟩) (routine := ⟨5443⟩) (slot := ⟨5⟩)
    hcode hdispatch hdecode hreach hAccounts uniswap_address_getter_entry_wf
    uniswap_address_slot_getter_wf (by jump_dest) (by rfl) hbody

end UniswapV2Pair
