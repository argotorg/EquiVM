import Examples.UniswapV2Pair.Dispatch
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `price0CumulativeLast()` getter -/

def price0CumulativeLastWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  uniswapSlotWord ⟨9⟩ σ I

/-- The Solm `price0CumulativeLast()` body returns the uint256 stored in slot 9. -/
theorem uniswapPrice0CumulativeLastBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "price0CumulativeLast" = none) :
    ExecTransitionBody config contract evm locals price0CumulativeLastTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨9⟩).toNat))])) := by
  simpa [price0CumulativeLastTransition] using
    uniswapUint256GetterBodyReturns (slot := ⟨9⟩) (ref := price0CumulativeLastRef)
      (er := ({ base := "price0CumulativeLast", steps := [] } : EvaledStorageRef)) evm locals h
      (by simpa [price0CumulativeLastRef] using hlocals)
      (by
        simp [evalStorageRef, evalStorageRefSteps, price0CumulativeLastRef, EvalResult.bind,
          pure, bind])
      (by decide) (by rfl)

/-- From `price0CumulativeLast()`'s body entry (pc 1025), bytecode returns slot 9. -/
theorem uniswapX_price0CumulativeLast {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1025⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (price0CumulativeLastWord σ I)) := by
  exact RD.uniswapWordGetterExternal (entry := ⟨1025⟩) (routine := ⟨3271⟩)
    (slot := ⟨9⟩) hreach uniswap_word_getter_entry_wf uniswap_word_slot_getter_wf
    (by jump_dest) (by jump_dest)

theorem uniswapDecode_price0CumulativeLast {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (price0CumulativeLastTransition.params.map Param.name)
      (transitionSignature price0CumulativeLastTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-- `price0CumulativeLast()` body core, parameterized by dispatcher/decode facts. -/
theorem uniswapPrice0CumulativeLastBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some price0CumulativeLastTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (price0CumulativeLastTransition.params.map Param.name)
        (transitionSignature price0CumulativeLastTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1025⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        price0CumulativeLastTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (price0CumulativeLastWord σ_solm I).toNat))])) := by
    simpa [price0CumulativeLastWord, uniswapSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      uniswapPrice0CumulativeLastBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact uniswapUint256GetterBodyCore (entry := ⟨1025⟩) (routine := ⟨3271⟩) (slot := ⟨9⟩)
    hcode hdispatch hdecode hreach hAccounts uniswap_word_getter_entry_wf
    uniswap_word_slot_getter_wf (by jump_dest) (by rfl)
    (by simpa [price0CumulativeLastWord] using hbody)

/-- `price0CumulativeLast()` wrapper: selector match supplies decode and reach. -/
theorem uniswapPrice0CumulativeLastBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x59, 0x09, 0xc0, 0xd5]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some price0CumulativeLastTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x59, 0x09, 0xc0, 0xd5]⟩ rfl hsel
  exact uniswapPrice0CumulativeLastBodyCore hcode hwv hdispatch
    (uniswapDecode_price0CumulativeLast hsz)
    (uniswapReachPrice0CumulativeLastBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
    hAccounts

end UniswapV2Pair
