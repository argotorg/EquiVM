import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.Decode
import Benchmarks.Morpho.MetaMorphoV1_1.MappingStorage
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_036

/-!
# MetaMorphoV1_1 `balanceOf(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 7204; reach lemma `metaMorphoV1_1ReachBalanceOfBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

theorem balanceOfBodyReturns (v : MetaMorphoV1_1Immutables)
    (evm : EVM.State) (locals : Store) (w : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hbase : locals.get? "_balances" = none)
    (hget : locals.get? "account" = some (.address (AccountAddress.ofNat w.toNat)))
    (hcanon : w.toNat < EVM.addressModulus) :
    ExecTransitionBody config contract evm locals balanceOfTransition.body
      (.returned
        { contract := contract
          locals := locals.insert "__calldata" (.bytes evm.executionEnv.calldata)
          immutables := immStore v }
        evm (some [.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (solcMappingSlot ⟨0⟩ w)).toNat)])) (immStore v) := by
  apply ExecFuncBody.execBlockRet
  exact (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).returns
    (evalStorage_balanceOf evm _ _ w
      (by rw [store_get_ne _ _ (by decide)]; exact hbase)
      (by rw [store_get_ne _ _ (by decide)]; exact hget) hcanon)

set_option maxRecDepth 2000 in
theorem balanceOfReachDecoder {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨7204⟩ R mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨11163⟩
      (⟨7237⟩ :: solcAddrMask :: R) mem aw rdata σ k' C' := by
  have rd7210 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_7204_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd7222 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_7210_fallthrough
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ = ⟨0⟩
      rw [calldataNot3_eq_sub (by omega) hsize]
      exact solcDecodeLenCheckOk_4_32 hsz hhi hsize) rd7210
  have rd11163 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_7222
    (immWords := wordsOf (immStore v)) hstack
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd7222
  exact ⟨_, _, rd11163⟩

set_option maxRecDepth 2000 in
theorem balanceOfReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (rd : RD (deployedRuntime v) I g s0 ⟨7204⟩ R solcFreePtrMem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ
      (codeOwnerStorageWord I σ (solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4))).toByteArray := by
  obtain ⟨_, _, rd11163⟩ := balanceOfReachDecoder v (by omega) hwv hsz hhi hsize rd
  obtain ⟨_, _, rd7237⟩ := decodeAddressAt4 v (by simpa only [List.length_cons] using hstack)
    hcanon (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd11163
  have hret := metaMorphoV1_1Blocks.metaMorphoV1_1_block_7237
    (immWords := wordsOf (immStore v)) (by omega) rd7237
  have hk := mappingScratchHash (UInt256.land (calldataWord I.calldata 4) solcAddrMask) ⟨0⟩
  exact solcAddrMask_clean hcanon ▸ hk ▸ (mappingScratchReturnMemory _ _ _ ▸ hret)

set_option maxRecDepth 2000 in
theorem balanceOfRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨7204⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_7204_taken
    (immWords := wordsOf (immStore v)) hstack hwv
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) hstack rd917

set_option maxRecDepth 2000 in
theorem balanceOfRevertLength {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩)
    (hcond : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨7204⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd7210 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_7204_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_7210_taken
    (immWords := wordsOf (immStore v)) hstack hcond
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd7210
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) (by omega) rd917

set_option maxRecDepth 2000 in
theorem balanceOfRevertNoncanonical {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (hnc : ¬ (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (rd : RD (deployedRuntime v) I g s0 ⟨7204⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨_, _, rd11163⟩ := balanceOfReachDecoder v (by omega) hwv hsz hhi hsize rd
  exact decodeAddressAt4Revert v (by simpa only [List.length_cons] using hstack) hnc rd11163

set_option maxRecDepth 2000 in
/-- `balanceOf(address)`: the theorem `Correct.lean` routes selector 31 to. -/
theorem metaMorphoV1_1BalanceOfBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 31)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 31) rfl hsel
  have hd : dispatchMsg contract I.calldata = some balanceOfTransition := by
    apply metaMorphoV1_1Dispatch_balanceOf <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachBalanceOfBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hlen : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · exact (balanceOfReturn v (by simp) hwv hlen hhi hsize hcanon rd).reEquivExecution
            hcode hd (decodeCalldata_address_ok hlen hhi hcanon)
            (balanceOfBodyReturns v _ _ _ hwv hhi (by simp)
              (store_get_self _ _ _) hcanon)
            (returnEquiv_of_encode (uint256ReturnEncoding _))
        · have hrev := balanceOfRevertNoncanonical v (by simp) hwv hlen hhi hsize hcanon rd
          exact hrev.reEquivDecodingFailed hcode hd
            (decodeCalldata_address_none_noncanon hlen hhi hcanon)
      · have hrev := balanceOfRevertLength v (by simp) hwv (by
          rw [calldataNot3_eq_sub hsz hsize,
            solcDecodeLenCheckHuge_4_32 (Nat.le_of_not_gt hhi) hsize]
          decide) rd
        exact hrev.reEquivDecodingFailed hcode hd
          (decodeCalldata_address_none_huge (Nat.le_of_not_gt hhi))
    · have hrev := balanceOfRevertLength v (by simp) hwv (by
        rw [calldataNot3_eq_sub hsz hsize,
          solcDecodeLenCheckShort_4_32 hsz (by omega) hsize]
        decide) rd
      exact hrev.reEquivDecodingFailed hcode hd (decodeCalldata_address_none_short hsz (by omega))
  · exact dispatchedRevert hcode hd (balanceOfRevertNonPayable v (by simp) hwv rd)
      (fun _ ↦ bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1
