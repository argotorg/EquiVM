import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.AddressGetter
import Benchmarks.CompoundIII.Comet.Storage
import Benchmarks.CompoundIII.Comet.MappingGetter
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_010
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_017

/-!
# CometWithExtendedAssetList `userNonce(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1258; reach lemma `cometWithExtendedAssetListReachUserNonceBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables
open cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def userNonceSlot (addr : AccountAddress) : UInt256 :=
  solcMappingSlot ⟨4⟩ (EVM.word addr.val)

def userNonceWord (σ : AccountMap) (I : ExecutionEnv) (addr : AccountAddress) : UInt256 :=
  solcSlotWordAt (userNonceSlot addr) σ I

theorem evalUserNonce (evm : EVM.State) (locals imms : Store) (addr : AccountAddress)
    (hlocal : locals.get? "userNonce" = none)
    (harg : locals.get? "arg0" = some (.address addr)) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm (.storage ⟨"userNonce", [.mindex (.var "arg0")]⟩) =
      .ok (.int (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userNonceSlot addr)).toNat) := by
  apply evalExpr_storage_scalar_value (hbackend := rfl)
    (loc := uint256Loc (userNonceSlot addr))
    (er := ⟨"userNonce", [.mindex (.address addr)]⟩)
    (t := .int (.uint ⟨256, by decide⟩)) hlocal
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, harg,
      valueToKey?, pure, bind, EvalResult.bind, EvalResult.ofOption]
  · change storageTypeAt? contract.storage ⟨"userNonce", [.mindex (.address addr)]⟩ = _
    rfl
  · simp only [userNonceSlot, solcMappingSlot, uint256Loc, keyValueToWord_address]
    rfl
  · exact storageLocLoad_uint256 evm (userNonceSlot addr)

theorem userNonce_returns {σ σ₀ A I} {g : Sat256} (imms : Store)
    (hvalue : I.weiValue = ⟨0⟩) (hhi : I.calldata.size < 2 ^ 255 + 4) :
    ExecTransitionBody config contract (initState σ σ₀ g A I) (addressGetterArgs "arg0" I)
      userNonceTransition.body
      (.returned
        (calldataLocalFrame
          { contract := contract, locals := addressGetterArgs "arg0" I, immutables := imms }
          (initState σ σ₀ g A I))
        (initState σ σ₀ g A I)
        (some [.int (userNonceWord σ I
          (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)).toNat])) imms := by
  exact .execBlockRet <| (calldataPrologue_ok hvalue hhi).returns (by
    have he := evalUserNonce (initState σ σ₀ g A I)
      ((addressGetterArgs "arg0" I).insert "__calldata" (.bytes I.calldata)) imms
      (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
      (by simp [addressGetterArgs])
      (by simp only [addressGetterArgs, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert]; rfl)
    simpa only [storageLoad_initState_solcSlotWord, userNonceWord, solcSlotWordAt] using he)

theorem userNonceX {σ σ₀ A I} {g : Sat256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 14)) :
    AddressGetterResult (deployedRuntime v) I g (initState σ σ₀ g A I) σ
      (userNonceWord σ I (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)).toByteArray := by
  obtain ⟨k, C, rd⟩ := cometWithExtendedAssetListReachUserNonceBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) v hcode hsz hsize hsel
  have rd1 := cometWithExtendedAssetList_block_1258 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd2 := cometWithExtendedAssetList_block_2634_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hv rd1
    by_cases hlo : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · have rd3 := cometWithExtendedAssetList_block_2641_fallthrough
          (immWords := wordsOf (immStore v)) (by decide)
          (calldataLength_ok (need := 32) (by decide) hlo hhi hsize) rd2
        have rd4 := cometWithExtendedAssetList_block_2653
          (immWords := wordsOf (immStore v)) (by decide)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd3
        by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · simp only [AddressGetterResult, hv, hlo, hhi, hc, and_self, if_true]
          obtain ⟨k', C', rd5⟩ := cometValidateAddress_ok (v := v) (ret := UInt256.ofNat 2664)
            (by change 6 ≤ 1024; decide) hc
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd4
          have rd6 := cometWithExtendedAssetList_block_2664
            (immWords := wordsOf (immStore v)) (by decide) rd5
          let w := calldataWord I.calldata 4
          have hclean : UInt256.land
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))
              (uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32)) = w :=
            solcAddrMask_clean_left hc
          rw [hclean] at rd6
          let mem := twoWordHashMem w ⟨4⟩ solcFreePtrMem
          change RDret (deployedRuntime v) g (initState σ σ₀ g A I) σ
            (((solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem) σ I).toByteArray.write
              0 mem (memLoad ⟨64⟩ mem).toNat 32).readWithPadding
                (memLoad ⟨64⟩ mem).toNat 32) at rd6
          have hhash : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem =
              solcMappingSlot ⟨4⟩ w := mappingGetterHash w ⟨4⟩
          rw [hhash] at rd6
          have hret := (mappingGetterReturnData w ⟨4⟩
            (solcSlotWordAt (solcMappingSlot ⟨4⟩ w) σ I)) ▸ rd6
          simpa only [userNonceWord, userNonceSlot, addressWord_eq_ofNat_address hc] using hret
        · simp only [AddressGetterResult, hc, and_false, if_false]
          exact cometValidateAddress_bad (v := v) (by change 6 ≤ 1024; decide) hc rd4
      · simp only [AddressGetterResult, hhi, false_and, and_false, if_false]
        have rd3 := cometWithExtendedAssetList_block_2641_taken
          (immWords := wordsOf (immStore v)) (by decide)
          (calldataLength_huge (need := 32) (by decide) (by omega) hsize)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
        exact cometRevert1410 (by decide) rd3
    · simp only [AddressGetterResult, hlo, false_and, and_false, if_false]
      have rd3 := cometWithExtendedAssetList_block_2641_taken
        (immWords := wordsOf (immStore v)) (by decide)
        (calldataLength_short (need := 32) (by decide) hsz (by omega) hsize)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact cometRevert1410 (by decide) rd3
  · simp only [AddressGetterResult, hv, false_and, if_false]
    have rd2 := cometWithExtendedAssetList_block_2634_taken
      (immWords := wordsOf (immStore v)) (by decide) hv
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact cometRevert1410 (by decide) rd2

/-- `userNonce(address)`: the theorem `Correct.lean` routes selector 14 to. -/
theorem cometWithExtendedAssetListUserNonceBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 14)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 14) rfl hsel
  apply addressGetter_refines (t := userNonceTransition) hcode hsz
    (cometSelectorDispatch ⟨14, by decide⟩ hsel) rfl rfl rfl
    (uint256ReturnEncoding
      (userNonceWord σ I (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)))
    ?_ (userNonceX v hcode hsz hsize hsel)
  intro hv hhi _
  exact ⟨_, userNonce_returns (immStore v) hv hhi⟩

end Benchmarks.CompoundIII.Comet
