import Examples.UniswapV2Pair.Dispatch
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `PERMIT_TYPEHASH()` constant getter -/

def permitTypehashWord : UInt256 :=
  ⟨49955707469362902507454157297736832118868343942642399513960811609542965143241⟩

theorem permitTypehashWord_toBytesBE :
    EVM.Word.toBytesBE permitTypehashWord = permitTypehashBytes := by
  native_decide

/-- The Solm `PERMIT_TYPEHASH()` body returns the bytes32 literal from Uniswap V2 ERC20. -/
theorem uniswapPermitTypehashBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm locals permitTypehashTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some (.fixedBytes bytes32Width permitTypehashBytes))) := by
  simpa [permitTypehashTransition, permitTypehashBytes] using
    uniswapFixedBytesLiteralBodyReturns evm locals bytes32Width permitTypehashBytes h

/-- From `PERMIT_TYPEHASH()`'s external body entry (pc 933), bytecode returns the EIP-712 hash. -/
theorem uniswapX_permitTypehash {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨933⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray permitTypehashWord) := by
  exact RD.uniswapWordConstGetterExternal (entry := ⟨933⟩) (routine := ⟨3092⟩)
    (val := permitTypehashWord) (width := 32) (op := .PUSH32) hreach
    uniswap_word_getter_entry_wf
    (by
      unfold permitTypehashWord Reasoning.Reach.uniswapConstGetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by jump_dest)

theorem uniswapDecode_permitTypehash {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (permitTypehashTransition.params.map Param.name)
      (transitionSignature permitTypehashTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-- Runtime-only `PERMIT_TYPEHASH()` slice from selector dispatch through return. -/
theorem uniswapPermitTypehashRuntimeBody
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x30, 0xad, 0xf8, 0x1f]⟩) :
    RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (cA, σ)
      (UInt256.toByteArray permitTypehashWord) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x30, 0xad, 0xf8, 0x1f]⟩ rfl hsel
  exact uniswapX_permitTypehash
    (uniswapReachPermitTypehashBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)

/-- `PERMIT_TYPEHASH()` body core, parameterized by dispatcher/decode facts owned by `Correct`. -/
theorem uniswapPermitTypehashBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some permitTypehashTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (permitTypehashTransition.params.map Param.name)
        (transitionSignature permitTypehashTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨933⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        permitTypehashTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.fixedBytes bytes32Width permitTypehashBytes))) := by
    exact uniswapPermitTypehashBodyReturns
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
      (by simp only [initState]; exact hwv)
  have henc :
      returnEquiv (UInt256.toByteArray permitTypehashWord)
        (some (.fixedBytes bytes32Width permitTypehashBytes))
        permitTypehashTransition.returnType := by
    rw [permitTypehashTransition]
    exact returnEquiv_of_encode
      (by
        simpa [bytes32, bytes32Width, permitTypehashWord_toBytesBE] using
          bytes32ReturnEncoding permitTypehashWord)
  exact (RD.uniswapWordConstGetterExternal (g := Sat256.ofUInt256 g)
      (entry := ⟨933⟩) (routine := ⟨3092⟩) (val := permitTypehashWord)
      (width := 32) (op := .PUSH32) hreach uniswap_word_getter_entry_wf
      (by
        unfold permitTypehashWord Reasoning.Reach.uniswapConstGetterWf
        repeat' first | apply And.intro | native_decide)
      (by jump_dest) (by jump_dest)).reEquivExecutionTransport
    hcode hdispatch hdecode hbody rfl hAccounts henc

/-- `PERMIT_TYPEHASH()` body wrapper for top-level routing: selector match supplies decode and reach. -/
theorem uniswapPermitTypehashBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x30, 0xad, 0xf8, 0x1f]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some permitTypehashTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x30, 0xad, 0xf8, 0x1f]⟩ rfl hsel
  exact uniswapPermitTypehashBodyCore hcode hwv hdispatch
    (uniswapDecode_permitTypehash hsz)
    (uniswapReachPermitTypehashBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
    hAccounts

end UniswapV2Pair
