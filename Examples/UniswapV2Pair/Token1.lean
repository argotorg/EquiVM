import Examples.UniswapV2Pair.Dispatch
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `token1()` getter -/

def token1Word (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  uniswapSlotWord ⟨7⟩ σ I

abbrev token1ReturnWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  uniswapAddressReturnWord ⟨7⟩ σ I

/-- The Solm `token1()` body returns the address stored in slot 7. -/
theorem uniswapToken1BodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "token1" = none) :
    ExecTransitionBody config contract evm locals token1Transition.body
      (.returned { contract := contract, locals := locals } evm
        (some (.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩)
            solcAddrMask).toNat)))) := by
  simpa [token1Transition] using
    uniswapAddressGetterBodyReturns (slot := ⟨7⟩) (ref := token1Ref)
      (er := ({ base := "token1", steps := [] } : EvaledStorageRef)) evm locals h
      (by simpa [token1Ref] using hlocals)
      (by simp [evalStorageRef, evalStorageRefSteps, token1Ref, EvalResult.bind, pure, bind])
      (by decide) (by rfl)

/-- From `token1()`'s external body entry (pc 1332), the bytecode returns slot 7 as an address. -/
theorem uniswapX_token1 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1332⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (token1ReturnWord σ I)) := by
  exact RD.uniswapAddressGetterExternal (entry := ⟨1332⟩) (routine := ⟨5458⟩)
    (slot := ⟨7⟩) hreach uniswap_address_getter_entry_wf uniswap_address_slot_getter_wf
    (by jump_dest) (by jump_dest)

theorem uniswapDecode_token1 {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (token1Transition.params.map Param.name)
      (transitionSignature token1Transition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-- `token1()` body core, parameterized by the dispatcher/decode facts still owned by `Correct`. -/
theorem uniswapToken1BodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some token1Transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (token1Transition.params.map Param.name)
        (transitionSignature token1Transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1332⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ token1Transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.address (AccountAddress.ofNat (token1ReturnWord σ_solm I).toNat)))) := by
    simpa [token1Word, token1ReturnWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
      using uniswapToken1BodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact uniswapAddressGetterBodyCore (entry := ⟨1332⟩) (routine := ⟨5458⟩) (slot := ⟨7⟩)
    hcode hdispatch hdecode hreach hAccounts uniswap_address_getter_entry_wf
    uniswap_address_slot_getter_wf (by jump_dest) (by rfl)
    (by simpa [token1ReturnWord] using hbody)

/-- `token1()` body wrapper for top-level routing: selector match supplies decode and reach. -/
theorem uniswapToken1Body
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xd2, 0x12, 0x20, 0xa7]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some token1Transition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xd2, 0x12, 0x20, 0xa7]⟩ rfl hsel
  exact uniswapToken1BodyCore hcode hwv hdispatch (uniswapDecode_token1 hsz)
    (uniswapReachToken1Body (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts

end UniswapV2Pair
