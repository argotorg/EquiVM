import Benchmarks.WETH9.Routines
import Benchmarks.WETH9.Opcodes

/-!
# WETH9 `totalSupply()` refinement

`totalSupply` returns `address(this).balance` via the `SELFBALANCE` opcode (WETH9's total supply is
the contract's ether balance).  No arguments, non-payable.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.WETH9

/-- The contract's ether balance (the value `SELFBALANCE` pushes and `totalSupply` returns). -/
def totalSupplyWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)

theorem totalSupplyWord_congr {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    totalSupplyWord σ_evm I = totalSupplyWord σ_solm I := by
  have h := hAccounts I.codeOwner
  unfold totalSupplyWord
  revert h
  cases hσ : σ_evm.find? I.codeOwner <;> cases hτ : σ_solm.find? I.codeOwner <;>
    simp_all [accountMapEquiv, accountEquiv]

theorem weth9SelectorDispatchTotalSupply {I : ExecutionEnv} (hsel : selIs I (weth9SelBytes 2)) :
    selectorDispatchMsg contract I.calldata = some totalSupplyTransition := by
  have hcd : I.calldata.extract 0 4 = weth9SelBytes 2 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp only [contract, dispatchList, selectorOf, hcd,
    weth9NameSelectorBytes, weth9ApproveSelectorBytes, weth9TotalSupplySelectorBytes]
  native_decide

theorem weth9Decode_totalSupply_ok {I : ExecutionEnv} (hsz4 : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (totalSupplyTransition.params.map Param.name)
      (transitionSignature totalSupplyTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some (∅ : Store)
  exact decodeCalldataWithMode_empty_ok hsz4

/-- The Solm `totalSupply()` body returns `address(this).balance`. -/
theorem weth9TotalSupplyBodyReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (h : I.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) ∅
      totalSupplyTransition.body
      (.returned { contract := contract, locals := ∅ } (initState cA gh bl σ σ₀ g A I)
        (some [(.int (Int.ofNat (totalSupplyWord σ I).toNat))])) := by
  refine nonpayableReturnExprBodyReturns (by simp only [initState]; exact h) ?_
  show evalExpr? config { contract := contract, locals := ∅ } (initState cA gh bl σ σ₀ g A I)
    (.env .selfbalance) = EvalResult.ok (.int (Int.ofNat (totalSupplyWord σ I).toNat))
  simp only [evalExpr?, envValue, totalSupplyWord, initState, State.lookupAccount,
    Option.option, pure]
  cases σ.find? I.codeOwner <;> rfl

/-! ## EVM trace -/

theorem weth9TotalSupplyX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 2)) :
    RDret weth9Bytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (totalSupplyWord σ I)) := by
  obtain ⟨_, _, h381⟩ := weth9ReachTotalSupply (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h395⟩ := weth9GuardPeelOk (gt := ⟨393⟩) h381 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
  have h1083 := h395.push2 ⟨402⟩ (by native_decide) (by simp)
    |>.push2 ⟨1083⟩ (by native_decide) (by simp)
    |>.jump (by native_decide) (by jump_dest) (by simp)
  have h402 := (RD.selfbalance (h1083.jumpdest (by native_decide) (by simp))
      (by native_decide) (by simp)).swap1 (by native_decide) (by simp)
    |>.jump (by native_decide) (by jump_dest) (by simp)
  exact RD.solcReturnWordFromMem h402
    (by dsimp [solcReturnWordFromMemWf]; repeat' first | apply And.intro | native_decide)
    solcFreePtrMem_mload64 rfl
    (solcReturnMem_mload64 (totalSupplyWord σ I))
    (solcReturnMem_read128 (totalSupplyWord σ I))
    (by decide)

/-! ## Refinement -/

theorem weth9TotalSupplyBodyCoreOk {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = weth9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (weth9SelBytes 2))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (weth9SelBytes 2) (by native_decide) hsel
  have hbal : totalSupplyWord σ_evm I = totalSupplyWord σ_solm I := totalSupplyWord_congr hAccounts
  exact weth9ReEquivExecTransport hcode
    (weth9TotalSupplyX_ok (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    (weth9SelectorDispatchTotalSupply hsel) (weth9Decode_totalSupply_ok hsz4)
    (weth9TotalSupplyBodyReturns hwv) (by rw [← hbal])
    hAccounts
    (returnEquiv_of_encode (by simpa [uint256] using uint256ReturnEncoding (totalSupplyWord σ_evm I)))

theorem weth9TotalSupplyBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = weth9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hsel : selIs I (weth9SelBytes 2))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · exact weth9TotalSupplyBodyCoreOk hcode hsize hwv hsel hAccounts
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (weth9SelBytes 2) (by native_decide) hsel
    obtain ⟨_, _, h381⟩ := weth9ReachTotalSupply (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
    have hrev := weth9GuardPeelRev (gt := ⟨393⟩) h381 hwv
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    exact weth9NonpayableRevert hcode hrev (weth9SelectorDispatchTotalSupply hsel)
      (fun callargs _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end Benchmarks.WETH9
