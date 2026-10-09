import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.Arithmetic
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_048
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_046
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009

/-!
# MetaMorphoV1_1 `decimals()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 9744; reach lemma `metaMorphoV1_1ReachDecimalsBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

abbrev decimalsWord (v : MetaMorphoV1_1Immutables) : UInt256 :=
  v._underlyingDecimals + v.DECIMALS_OFFSET

theorem decimalsWord_toNat (v : MetaMorphoV1_1Immutables) :
    (decimalsWord v).toNat = v._underlyingDecimals.toNat + v.DECIMALS_OFFSET.toNat := by
  rw [decimalsWord, uadd_toNat]
  apply Nat.mod_eq_of_lt
  have h1 := v.underlyingDecimals_lt
  have h2 := v.decimalsOffset_lt
  change _ < 2 ^ 256
  omega

theorem decimalsEncodedSum (v : MetaMorphoV1_1Immutables) :
    UInt256.land (wordsOf (immStore v) "_underlyingDecimals") (UInt256.ofNat 255) +
      UInt256.land (wordsOf (immStore v) "DECIMALS_OFFSET") (UInt256.ofNat 255) =
      decimalsWord v := by
  simp only [wordsOf_immStore__underlyingDecimals, wordsOf_immStore_DECIMALS_OFFSET,
    wordOfInt_ofNat_toNat_gen, u256_ofNat_toNat]
  exact congrArg₂ (fun a b : UInt256 ↦ a + b)
    (lowByteClean v.underlyingDecimals_lt) (lowByteClean v.decimalsOffset_lt)

abbrev decimalsExpr : Expr :=
  .inRange (.uint ⟨8, by decide⟩)
    (.binary .add (.immutable "_underlyingDecimals") (.immutable "DECIMALS_OFFSET"))

theorem decimalsExpr_ok (v : MetaMorphoV1_1Immutables) (evm : EVM.State) (locals : Store)
    (hfit : (decimalsWord v).toNat < 256) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v }
      evm decimalsExpr = .ok (.int (Int.ofNat (decimalsWord v).toNat)) := by
  rw [decimalsWord_toNat] at hfit ⊢
  exact evalExpr_uintInRange ⟨8, by decide⟩
    (evalExpr_natAdd (evalImmutable__underlyingDecimals _ _ _ _ _)
      (evalImmutable_DECIMALS_OFFSET _ _ _ _ _)) hfit

theorem decimalsExpr_revert (v : MetaMorphoV1_1Immutables) (evm : EVM.State) (locals : Store)
    (hover : 256 ≤ (decimalsWord v).toNat) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v }
      evm decimalsExpr = .revert := by
  rw [decimalsWord_toNat] at hover
  exact evalExpr_uintInRange_revert ⟨8, by decide⟩
    (evalExpr_natAdd (evalImmutable__underlyingDecimals _ _ _ _ _)
      (evalImmutable_DECIMALS_OFFSET _ _ _ _ _)) hover

theorem decimalsBodyReturns (v : MetaMorphoV1_1Immutables)
    (evm : EVM.State) (locals : Store) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hfit : (decimalsWord v).toNat < 256) :
    ExecTransitionBody config contract evm locals decimalsTransition.body
      (.returned
        { contract := contract
          locals := (locals.insert "__calldata" (.bytes evm.executionEnv.calldata)).insert
            "__r" (.int (Int.ofNat (decimalsWord v).toNat))
          immutables := immStore v }
        evm (some [.int (Int.ofNat (decimalsWord v).toNat)])) (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  refine ExecBlock.consNormal
    (internalCallReturnExpr (retTy := [.elem (.int (.uint ⟨8, by decide⟩))])
      (expr := decimalsExpr) (by rfl) (decimalsExpr_ok v evm ∅ hfit)) ?_
  exact ABlock.start.returns (by
    simp only [evalExpr?, store_get_self, EvalResult.ofOption])

theorem decimalsBodyRevertsOverflow (v : MetaMorphoV1_1Immutables)
    (evm : EVM.State) (locals : Store) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hover : 256 ≤ (decimalsWord v).toNat) :
    ExecTransitionBody config contract evm locals decimalsTransition.body
      .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  exact ExecBlock.consRevert
    (internalCallRevertExpr (retTy := [.elem (.int (.uint ⟨8, by decide⟩))])
      (expr := decimalsExpr) (by rfl) (decimalsExpr_revert v evm ∅ hover))

set_option maxRecDepth 2000 in
theorem decimalsReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (hfit : (decimalsWord v).toNat < 256)
    (rd : RD (deployedRuntime v) I g s0 ⟨9744⟩ R solcFreePtrMem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ (decimalsWord v).toByteArray := by
  have rd9750 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_9744_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd9761 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_9750_fallthrough
    (immWords := wordsOf (immStore v))
    (by omega) (calldataLengthCheckOk hsz hhi hsize) rd9750
  have rd9842 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_9761_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) (by
      rw [decimalsEncodedSum]
      apply ugt_zero
      change (decimalsWord v).toNat ≤ 255
      omega) rd9761
  have hret := metaMorphoV1_1Blocks.metaMorphoV1_1_block_9842
    (immWords := wordsOf (immStore v)) hstack rd9842
  have hw : UInt256.land
      (UInt256.land (wordsOf (immStore v) "_underlyingDecimals") (UInt256.ofNat 255) +
        UInt256.land (wordsOf (immStore v) "DECIMALS_OFFSET") (UInt256.ofNat 255))
      (UInt256.ofNat 255) = decimalsWord v := by
    rw [decimalsEncodedSum]
    exact lowByteClean hfit
  exact hw ▸ (returnWordMemory _ ▸ hret)

set_option maxRecDepth 2000 in
theorem decimalsRevertOverflow {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (hover : 256 ≤ (decimalsWord v).toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨9744⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd9750 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_9744_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd9761 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_9750_fallthrough
    (immWords := wordsOf (immStore v))
    hstack (calldataLengthCheckOk hsz hhi hsize) rd9750
  have rd9453 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_9761_taken
    (immWords := wordsOf (immStore v)) hstack (by
      rw [decimalsEncodedSum, ugt_one (by
        change 255 < (decimalsWord v).toNat
        omega)]
      decide) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd9761
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_9453
    (immWords := wordsOf (immStore v)) (by
      simpa only [metaMorphoV1_1Blocks.metaMorphoV1_1_block_9761_taken_stack, List.length_cons]
        using hstack) rd9453

set_option maxRecDepth 2000 in
theorem decimalsRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨9744⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_9744_taken
    (immWords := wordsOf (immStore v)) hstack hwv
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) hstack rd917

set_option maxRecDepth 2000 in
theorem decimalsRevertHuge {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hhi : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨9744⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd9750 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_9744_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_9750_taken
    (immWords := wordsOf (immStore v))
    hstack (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨0⟩ ≠ ⟨0⟩
      rw [calldataLengthCheckHuge hhi hsize]
      decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd9750
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) (by omega) rd917

set_option maxRecDepth 2000 in
/-- `decimals()`: the theorem `Correct.lean` routes selector 12 to. -/
theorem metaMorphoV1_1DecimalsBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 12)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 12) rfl hsel
  have hd : dispatchMsg contract I.calldata = some decimalsTransition := by
    apply metaMorphoV1_1Dispatch_decimals <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (decimalsTransition.params.map Param.name)
      (transitionSignature decimalsTransition).paramTypes I.calldata = some ∅ := by
    exact decodeCalldata_empty_ok hsz
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachDecimalsBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · by_cases hfit : (decimalsWord v).toNat < 256
      · exact (decimalsReturn v (by simp) hwv hsz hhi hsize hfit rd).reEquivExecution
          hcode hd hdec (decimalsBodyReturns v _ ∅ hwv hhi hfit)
          (returnEquiv_of_encode (uint8ReturnEncoding (decimalsWord v) hfit))
      · exact (decimalsRevertOverflow v (by simp) hwv hsz hhi hsize
          (Nat.le_of_not_gt hfit) rd).reEquivExecutionRevert hcode hd hdec
          (decimalsBodyRevertsOverflow v _ ∅ hwv hhi (Nat.le_of_not_gt hfit))
    · exact (decimalsRevertHuge v (by simp) hwv (by omega) hsize rd).reEquivExecutionRevert
        hcode hd hdec
        (bodyReverts_calldataBound "__calldata" (2 ^ 255 + 4) hwv (Nat.le_of_not_gt hhi))
  · exact (decimalsRevertNonPayable v (by simp) hwv rd).reEquivExecutionRevert
      hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1
