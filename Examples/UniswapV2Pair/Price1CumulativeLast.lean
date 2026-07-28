import Examples.UniswapV2Pair.Dispatch
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `price1CumulativeLast()` getter -/

def price1CumulativeLastWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  uniswapSlotWord ⟨10⟩ σ I

/-- The Solm `price1CumulativeLast()` body returns the uint256 stored in slot 10. -/
theorem uniswapPrice1CumulativeLastBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "price1CumulativeLast" = none) :
    ExecTransitionBody config contract evm locals price1CumulativeLastTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨10⟩).toNat))])) := by
  simpa [price1CumulativeLastTransition] using
    uniswapUint256GetterBodyReturns (slot := ⟨10⟩) (ref := price1CumulativeLastRef)
      (er := ({ base := "price1CumulativeLast", steps := [] } : EvaledStorageRef)) evm locals h
      (by simpa [price1CumulativeLastRef] using hlocals)
      (by
        simp [evalStorageRef, evalStorageRefSteps, price1CumulativeLastRef, EvalResult.bind,
          pure, bind])
      (by decide) (by rfl)

/-- From `price1CumulativeLast()`'s body entry (pc 1033), bytecode returns slot 10. -/
theorem uniswapX_price1CumulativeLast {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1033⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (price1CumulativeLastWord σ I)) := by
  exact RD.uniswapWordGetterExternal (entry := ⟨1033⟩) (routine := ⟨3277⟩)
    (slot := ⟨10⟩) hreach uniswap_word_getter_entry_wf uniswap_word_slot_getter_wf
    (by jump_dest) (by jump_dest)

theorem uniswapDecode_price1CumulativeLast {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (price1CumulativeLastTransition.params.map Param.name)
      (transitionSignature price1CumulativeLastTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-- `price1CumulativeLast()` body core, parameterized by dispatcher/decode facts. -/
theorem uniswapPrice1CumulativeLastBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some price1CumulativeLastTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (price1CumulativeLastTransition.params.map Param.name)
        (transitionSignature price1CumulativeLastTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1033⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        price1CumulativeLastTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (price1CumulativeLastWord σ_solm I).toNat))])) := by
    simpa [price1CumulativeLastWord, uniswapSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      uniswapPrice1CumulativeLastBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact uniswapUint256GetterBodyCore (entry := ⟨1033⟩) (routine := ⟨3277⟩) (slot := ⟨10⟩)
    hcode hdispatch hdecode hreach hAccounts uniswap_word_getter_entry_wf
    uniswap_word_slot_getter_wf (by jump_dest) (by rfl)
    (by simpa [price1CumulativeLastWord] using hbody)

/-- `price1CumulativeLast()` wrapper: selector match supplies decode and reach. -/
theorem uniswapPrice1CumulativeLastBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x5a, 0x3d, 0x54, 0x93]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some price1CumulativeLastTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x5a, 0x3d, 0x54, 0x93]⟩ rfl hsel
  exact uniswapPrice1CumulativeLastBodyCore hcode hwv hdispatch
    (uniswapDecode_price1CumulativeLast hsz)
    (uniswapReachPrice1CumulativeLastBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
    hAccounts

end UniswapV2Pair
