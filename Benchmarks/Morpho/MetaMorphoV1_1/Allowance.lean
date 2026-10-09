import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.Decode
import Benchmarks.Morpho.MetaMorphoV1_1.NestedMappingStorage
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_011
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_012

/-!
# MetaMorphoV1_1 `allowance(address,address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1454; reach lemma `metaMorphoV1_1ReachAllowanceBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

theorem allowanceBodyReturns (v : MetaMorphoV1_1Immutables)
    (evm : EVM.State) (locals : Store) (owner spender : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hbase : locals.get? "_allowances" = none)
    (howner : locals.get? "owner" = some (.address (AccountAddress.ofNat owner.toNat)))
    (hspender : locals.get? "spender" = some (.address (AccountAddress.ofNat spender.toNat)))
    (hcanon₁ : owner.toNat < EVM.addressModulus) (hcanon₂ : spender.toNat < EVM.addressModulus) :
    ExecTransitionBody config contract evm locals allowanceTransition.body
      (.returned
        { contract := contract
          locals := locals.insert "__calldata" (.bytes evm.executionEnv.calldata)
          immutables := immStore v }
        evm (some [.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (solcMappingSlot (solcMappingSlot ⟨1⟩ owner) spender)).toNat)])) (immStore v) := by
  apply ExecFuncBody.execBlockRet
  exact (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).returns
    (evalStorage_allowance evm _ _ owner spender
      (by rw [store_get_ne _ _ (by decide)]; exact hbase)
      (by rw [store_get_ne _ _ (by decide)]; exact howner)
      (by rw [store_get_ne _ _ (by decide)]; exact hspender) hcanon₁ hcanon₂)

set_option maxRecDepth 2000 in
theorem allowanceReachFirstDecoder {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨1454⟩ R mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨11163⟩
      (⟨1479⟩ :: R) mem aw rdata σ k' C' := by
  have rd1460 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1454_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd1472 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1460_fallthrough
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨64⟩ = ⟨0⟩
      rw [calldataNot3_eq_sub (by omega) hsize]
      exact solcDecodeLenCheckOk_4_64 hsz hhi hsize) rd1460
  have rd11163 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1472
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd1472
  exact ⟨_, _, rd11163⟩

set_option maxRecDepth 2000 in
theorem allowanceReachSecondDecoder {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (rd : RD (deployedRuntime v) I g s0 ⟨1454⟩ R mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨11185⟩
      (⟨1487⟩ :: calldataWord I.calldata 4 :: R) mem aw rdata σ k' C' := by
  obtain ⟨_, _, rd11163⟩ := allowanceReachFirstDecoder v (by omega) hwv hsz hhi hsize rd
  obtain ⟨_, _, rd1479⟩ := decodeAddressAt4 v hstack hcanon
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd11163
  have rd11185 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1479
    (immWords := wordsOf (immStore v))
    (by simpa only [List.length_cons] using (show R.length + 1 + 2 ≤ 1024 by omega))
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd1479
  exact ⟨_, _, rd11185⟩

set_option maxRecDepth 2000 in
theorem allowanceReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (hcanon₁ : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hcanon₂ : (calldataWord I.calldata 36).toNat < EVM.addressModulus)
    (rd : RD (deployedRuntime v) I g s0 ⟨1454⟩ R solcFreePtrMem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ
      (codeOwnerStorageWord I σ (solcMappingSlot
        (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4))
        (calldataWord I.calldata 36))).toByteArray := by
  obtain ⟨_, _, rd11185⟩ :=
    allowanceReachSecondDecoder v (by omega) hwv hsz hhi hsize hcanon₁ rd
  obtain ⟨_, _, rd1487⟩ := decodeAddressAt36 v
    (by simpa only [List.length_cons] using (show R.length + 1 + 5 ≤ 1024 by omega))
    hcanon₂ (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd11185
  have hret := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1487
    (immWords := wordsOf (immStore v)) hstack rd1487
  have hk := nestedMappingHash (UInt256.land solcAddrMask (calldataWord I.calldata 4))
    (UInt256.land (calldataWord I.calldata 36) solcAddrMask) ⟨1⟩
  have hslot := hk.trans (show
    solcMappingSlot (solcMappingSlot ⟨1⟩
      (UInt256.land solcAddrMask (calldataWord I.calldata 4)))
      (UInt256.land (calldataWord I.calldata 36) solcAddrMask) =
      solcMappingSlot (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4))
        (calldataWord I.calldata 36) by
      rw [solcAddrMask_clean_left hcanon₁, solcAddrMask_clean hcanon₂])
  have hbytes := (nestedMappingReturnMemory
    (UInt256.land solcAddrMask (calldataWord I.calldata 4))
    (UInt256.land (calldataWord I.calldata 36) solcAddrMask) ⟨1⟩ _).trans
      (congrArg (fun slot ↦ (codeOwnerStorageWord I σ slot).toByteArray) hslot)
  exact (congrArg (fun bytes ↦ RDret (deployedRuntime v) g s0 σ bytes) hbytes).mp hret

set_option maxRecDepth 2000 in
theorem allowanceRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨1454⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1454_taken
    (immWords := wordsOf (immStore v)) hstack hwv
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) hstack rd917

set_option maxRecDepth 2000 in
theorem allowanceRevertLength {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩)
    (hcond : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨64⟩ ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨1454⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd1460 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1454_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1460_taken
    (immWords := wordsOf (immStore v)) hstack hcond
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd1460
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) (by omega) rd917

set_option maxRecDepth 2000 in
theorem allowanceRevertFirstNoncanonical {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (hnc : ¬ (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (rd : RD (deployedRuntime v) I g s0 ⟨1454⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨_, _, rd11163⟩ := allowanceReachFirstDecoder v (by omega) hwv hsz hhi hsize rd
  exact decodeAddressAt4Revert v hstack hnc rd11163

set_option maxRecDepth 2000 in
theorem allowanceRevertSecondNoncanonical {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hnc : ¬ (calldataWord I.calldata 36).toNat < EVM.addressModulus)
    (rd : RD (deployedRuntime v) I g s0 ⟨1454⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨_, _, rd11185⟩ :=
    allowanceReachSecondDecoder v (by omega) hwv hsz hhi hsize hcanon rd
  exact decodeAddressAt36Revert v (by simpa only [List.length_cons] using hstack) hnc rd11185

set_option maxRecDepth 2000 in
/-- `allowance(address,address)`: the theorem `Correct.lean` routes selector 67 to. -/
theorem metaMorphoV1_1AllowanceBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 67)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 67) rfl hsel
  have hd : dispatchMsg contract I.calldata = some allowanceTransition := by
    apply metaMorphoV1_1Dispatch_allowance <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachAllowanceBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hlen : 68 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · by_cases hcanon₁ : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · by_cases hcanon₂ : (calldataWord I.calldata 36).toNat < EVM.addressModulus
          · have hret := allowanceReturn v (by simp) hwv hlen hhi hsize hcanon₁ hcanon₂ rd
            exact hret.reEquivExecution hcode hd
                (decodeCalldata_address_address_ok hlen hhi hcanon₁ hcanon₂)
                (allowanceBodyReturns v _ _ _ _ hwv hhi (by simp)
                  (by rw [store_get_ne _ _ (by decide)]; exact store_get_self _ _ _)
                  (store_get_self _ _ _) hcanon₁ hcanon₂)
                (returnEquiv_of_encode (uint256ReturnEncoding _))
          · have hrev := allowanceRevertSecondNoncanonical v (by simp)
              hwv hlen hhi hsize hcanon₁ hcanon₂ rd
            exact hrev.reEquivDecodingFailed hcode hd
              (decodeCalldata_address_address_none_noncanon1 hlen hhi hcanon₁ hcanon₂)
        · have hrev := allowanceRevertFirstNoncanonical v (by simp) hwv hlen hhi hsize hcanon₁ rd
          exact hrev.reEquivDecodingFailed hcode hd
            (decodeCalldata_address_address_none_noncanon0 hlen hhi hcanon₁)
      · have hrev := allowanceRevertLength v (by simp) hwv (by
          rw [calldataNot3_eq_sub hsz hsize,
            solcDecodeLenCheckHuge_4_64 (Nat.le_of_not_gt hhi) hsize]
          decide) rd
        exact hrev.reEquivDecodingFailed hcode hd
          (decodeCalldata_address_address_none_huge (Nat.le_of_not_gt hhi))
    · have hrev := allowanceRevertLength v (by simp) hwv (by
        rw [calldataNot3_eq_sub hsz hsize,
          solcDecodeLenCheckShort_4_64 hsz (by omega) hsize]
        decide) rd
      exact hrev.reEquivDecodingFailed hcode hd
        (decodeCalldata_address_address_none_short hsz (by omega))
  · exact dispatchedRevert hcode hd (allowanceRevertNonPayable v (by simp) hwv rd)
      (fun _ ↦ bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1
