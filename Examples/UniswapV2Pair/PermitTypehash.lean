import Examples.UniswapV2Pair.Dispatch
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `PERMIT_TYPEHASH()` constant getter -/

def permitTypehashBytes : List UInt8 :=
  [ 0x6e, 0x71, 0xed, 0xae, 0x12, 0xb1, 0xb9, 0x7f,
    0x4d, 0x1f, 0x60, 0x37, 0x0f, 0xef, 0x10, 0x10,
    0x5f, 0xa2, 0x77, 0x6a, 0xe0, 0x12, 0x61, 0x14,
    0xa1, 0x69, 0xc6, 0x48, 0x45, 0xd6, 0x12, 0x6c ]

def permitTypehashRuntimeBytes : List UInt8 :=
  [ 0x6e, 0x71, 0xed, 0xae, 0x12, 0xb1, 0xb9, 0x7f,
    0x4d, 0x1f, 0x60, 0x37, 0x0f, 0xef, 0x10, 0x10,
    0x5f, 0xa2, 0xfa, 0xae, 0x01, 0x26, 0x11, 0x4a,
    0x16, 0x9c, 0x64, 0x84, 0x5d, 0x61, 0x26, 0xc9 ]

def permitTypehashWord : UInt256 :=
  ⟨49955707469362902507454157297736832118868343942642399513960811609542965143241⟩

theorem permitTypehashWord_toBytesBE :
    EVM.Word.toBytesBE permitTypehashWord = permitTypehashRuntimeBytes := by
  native_decide

theorem permitTypehashBytes_ne_runtimeBytes :
    permitTypehashBytes ≠ permitTypehashRuntimeBytes := by
  native_decide

theorem permitTypehashBytes_ne_runtimeWordBytes :
    permitTypehashBytes ≠ EVM.Word.toBytesBE permitTypehashWord := by
  rw [permitTypehashWord_toBytesBE]
  exact permitTypehashBytes_ne_runtimeBytes

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
    decodeCalldata (permitTypehashTransition.params.map Param.name)
      (transitionSignature permitTypehashTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-- Runtime-only `PERMIT_TYPEHASH()` slice from selector dispatch through return.

This deliberately does not claim refinement: `permitTypehashBytes_ne_runtimeWordBytes` records the
source/runtime literal mismatch below. -/
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

/-!
`PERMIT_TYPEHASH()` is intentionally left without a body-core refinement here.  The runtime bytecode
pushes `permitTypehashRuntimeBytes`, while `Spec.lean` currently returns `permitTypehashBytes`.
Per `prompt.md`, this file records the exact mismatch without changing trusted semantics.
-/

end UniswapV2Pair
