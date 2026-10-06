import Examples.UniswapV2Pair.Dispatch
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

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
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)
            solcAddrMask).toNat))])) := by
  simpa [factoryTransition] using
    uniswapAddressGetterBodyReturns (slot := ⟨5⟩) (ref := factoryRef)
      (er := ({ base := "factory", steps := [] } : EvaledStorageRef)) evm locals h
      (by simpa [factoryRef] using hlocals)
      (by simp [evalStorageRef, evalStorageRefSteps, factoryRef, EvalResult.bind, pure, bind])
      (by decide) (by rfl)

/-- From `factory()`'s external body entry (pc 1324), the bytecode returns slot 5 as an address. -/
theorem uniswapX_factory {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState σ σ₀ g A I) ⟨1324⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDret uniswapV2PairBytecode g (initState σ σ₀ g A I) σ
      (UInt256.toByteArray (factoryReturnWord σ I)) := by
  exact RD.addressGetterExternal (entry := ⟨1324⟩) (routine := ⟨5443⟩)
    (slot := ⟨5⟩) hreach uniswap_address_getter_entry_wf uniswap_address_slot_getter_wf
    (by jump_dest) (by jump_dest)

theorem uniswapDecode_factory {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (factoryTransition.params.map Param.name)
      (transitionSignature factoryTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-- `factory()` body core, parameterized by the dispatcher/decode facts still owned by `Correct`. -/
theorem uniswapFactoryBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some factoryTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (factoryTransition.params.map Param.name)
        (transitionSignature factoryTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1324⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ factoryTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat (factoryReturnWord σ I).toNat))])) := by
    simpa [factoryWord, factoryReturnWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
      using uniswapFactoryBodyReturns
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact uniswapAddressGetterBodyCore (entry := ⟨1324⟩) (routine := ⟨5443⟩) (slot := ⟨5⟩)
    hcode hdispatch hdecode hreach uniswap_address_getter_entry_wf
    uniswap_address_slot_getter_wf (by jump_dest) (by rfl) hbody

/-- `factory()` body wrapper for top-level routing: selector match supplies decode and reach. -/
theorem uniswapFactoryBody
    {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xc4, 0x5a, 0x01, 0x55]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some factoryTransition) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xc4, 0x5a, 0x01, 0x55]⟩ rfl hsel
  exact uniswapFactoryBodyCore hcode hwv hdispatch (uniswapDecode_factory hsz)
    (uniswapReachFactoryBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)

end UniswapV2Pair
