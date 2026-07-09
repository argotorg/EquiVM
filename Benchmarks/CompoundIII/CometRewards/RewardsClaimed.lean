import Benchmarks.CompoundIII.CometRewards.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.CompoundIII.CometRewards

/-! ## `rewardsClaimed(address,address)` getter -/

abbrev rewardsClaimedCometWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev rewardsClaimedAccountWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev rewardsClaimedCometValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (rewardsClaimedCometWord I).toNat)

abbrev rewardsClaimedAccountValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (rewardsClaimedAccountWord I).toNat)

abbrev rewardsClaimedStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "arg0" (rewardsClaimedCometValue I)).insert "arg1"
    (rewardsClaimedAccountValue I)

def rewardsClaimedSlotOf (I : ExecutionEnv) : UInt256 :=
  rewardsClaimedSlot
    (.address (AccountAddress.ofNat (rewardsClaimedCometWord I).toNat))
    (.address (AccountAddress.ofNat (rewardsClaimedAccountWord I).toNat))

def rewardsClaimedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (rewardsClaimedSlotOf I) ⟨0⟩)

noncomputable def rewardsClaimedInnerHashMem (comet : UInt256) : ByteArray :=
  twoWordHashMem comet ⟨2⟩ solcFreePtrMem

noncomputable def rewardsClaimedOuterHashMem (comet account : UInt256) : ByteArray :=
  twoWordHashMem account (solcMappingSlot ⟨2⟩ comet) (rewardsClaimedInnerHashMem comet)

noncomputable def rewardsClaimedReturnMem
    (comet account val : UInt256) : ByteArray :=
  solcScratchReturnMem (rewardsClaimedOuterHashMem comet account) val

theorem rewardsClaimedInnerHashMem_size (comet : UInt256) :
    (rewardsClaimedInnerHashMem comet).size = 96 := by
  exact twoWordHashMem_size_96 comet ⟨2⟩ solcFreePtrMem_size

theorem rewardsClaimedInnerHashMem_read64 (comet : UInt256) :
    (rewardsClaimedInnerHashMem comet).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 comet ⟨2⟩ solcFreePtrMem_size solcFreePtrMem_read64

theorem rewardsClaimedInnerKeccakSlot (comet : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((rewardsClaimedInnerHashMem comet).readWithPadding 0 64))) =
      solcMappingSlot ⟨2⟩ comet := by
  rw [rewardsClaimedInnerHashMem, twoWordHashMem_read0_64 comet ⟨2⟩ solcFreePtrMem_size]
  unfold solcMappingSlot
  exact mappingSlot_single comet ⟨2⟩

theorem rewardsClaimedOuterHashMem_size (comet account : UInt256) :
    (rewardsClaimedOuterHashMem comet account).size = 96 := by
  exact twoWordHashMem_size_96 account (solcMappingSlot ⟨2⟩ comet)
    (rewardsClaimedInnerHashMem_size comet)

theorem rewardsClaimedOuterHashMem_read64 (comet account : UInt256) :
    (rewardsClaimedOuterHashMem comet account).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 account (solcMappingSlot ⟨2⟩ comet)
    (rewardsClaimedInnerHashMem_size comet) (rewardsClaimedInnerHashMem_read64 comet)

theorem rewardsClaimedOuterHashMem_mload64 (comet account : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (rewardsClaimedOuterHashMem comet account).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((rewardsClaimedOuterHashMem comet account).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [rewardsClaimedOuterHashMem_size]; decide) (by decide)
    (rewardsClaimedOuterHashMem_read64 comet account)

theorem rewardsClaimedOuterKeccakSlot (comet account : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((rewardsClaimedOuterHashMem comet account).readWithPadding 0 64))) =
      solcMappingSlot (solcMappingSlot ⟨2⟩ comet) account := by
  rw [rewardsClaimedOuterHashMem, twoWordHashMem_read0_64 account
    (solcMappingSlot ⟨2⟩ comet) (rewardsClaimedInnerHashMem_size comet)]
  unfold solcMappingSlot
  exact mappingSlot_single account (solcMappingSlot ⟨2⟩ comet)

theorem rewardsClaimedReturnMem_mload64 (comet account val : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (rewardsClaimedReturnMem comet account val).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((rewardsClaimedReturnMem comet account val).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact solcScratchReturnMem_mload64 val (rewardsClaimedOuterHashMem_size comet account)
    (rewardsClaimedOuterHashMem_read64 comet account)

theorem rewardsClaimedReturnMem_read128 (comet account val : UInt256) :
    (rewardsClaimedReturnMem comet account val).readWithPadding 128 32 =
      UInt256.toByteArray val := by
  exact solcScratchReturnMem_read128 val (rewardsClaimedOuterHashMem_size comet account)

theorem rewardsClaimedSlotOf_eq_solc (I : ExecutionEnv)
    (hcanonComet : (rewardsClaimedCometWord I).toNat < EVM.addressModulus)
    (hcanonAccount : (rewardsClaimedAccountWord I).toNat < EVM.addressModulus) :
    rewardsClaimedSlotOf I =
      solcMappingSlot (solcMappingSlot ⟨2⟩ (rewardsClaimedCometWord I))
        (rewardsClaimedAccountWord I) := by
  unfold rewardsClaimedSlotOf rewardsClaimedSlot rewardsClaimedCometSlot
  rw [keyValueToWord_address_of_canonical _ hcanonComet,
    keyValueToWord_address_of_canonical _ hcanonAccount]
  rfl

theorem cometRewardsDecode_rewardsClaimed_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (rewardsClaimedCometWord I).toNat < EVM.addressModulus)
    (hcanonAccount : (rewardsClaimedAccountWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (rewardsClaimedTransition.params.map Param.name)
      (transitionSignature rewardsClaimedTransition).paramTypes I.calldata =
        some (rewardsClaimedStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["arg0", "arg1"] [addr, addr]
    I.calldata = _
  simpa [config, rewardsClaimedStore, rewardsClaimedCometValue, rewardsClaimedAccountValue,
    rewardsClaimedCometWord, rewardsClaimedAccountWord, calldataWord]
    using decodeCalldata_address_address_ok (cd := I.calldata) (x := "arg0") (y := "arg1")
      hsz68 hbig hcanonComet hcanonAccount

theorem cometRewardsDecode_rewardsClaimed_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (rewardsClaimedTransition.params.map Param.name)
      (transitionSignature rewardsClaimedTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["arg0", "arg1"] [addr, addr]
    I.calldata = none
  simpa [config, addr] using decodeCalldata_address_address_none_short
    (cd := I.calldata) (x := "arg0") (y := "arg1") hsz4 hshort

theorem cometRewardsDecode_rewardsClaimed_none_noncanon_comet {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hncComet : ¬ (rewardsClaimedCometWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (rewardsClaimedTransition.params.map Param.name)
      (transitionSignature rewardsClaimedTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["arg0", "arg1"] [addr, addr]
    I.calldata = none
  simpa [config, addr, rewardsClaimedCometWord, calldataWord]
    using decodeCalldata_address_address_none_noncanon0
      (cd := I.calldata) (x := "arg0") (y := "arg1") hsz68 hbig hncComet

theorem cometRewardsDecode_rewardsClaimed_none_noncanon_account {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (rewardsClaimedCometWord I).toNat < EVM.addressModulus)
    (hncAccount : ¬ (rewardsClaimedAccountWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (rewardsClaimedTransition.params.map Param.name)
      (transitionSignature rewardsClaimedTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["arg0", "arg1"] [addr, addr]
    I.calldata = none
  simpa [config, addr, rewardsClaimedCometWord, rewardsClaimedAccountWord, calldataWord]
    using decodeCalldata_address_address_none_noncanon1
      (cd := I.calldata) (x := "arg0") (y := "arg1")
      hsz68 hbig hcanonComet hncAccount

theorem cometRewardsDecode_rewardsClaimed_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (rewardsClaimedTransition.params.map Param.name)
      (transitionSignature rewardsClaimedTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["arg0", "arg1"] [addr, addr]
    I.calldata = none
  simpa [config, addr] using decodeCalldata_address_address_none_huge
    (cd := I.calldata) (x := "arg0") (y := "arg1") hbig

theorem rewardsClaimedStore_arg0 (I : ExecutionEnv) :
    (rewardsClaimedStore I).get? "arg0" = some (rewardsClaimedCometValue I) := by
  rw [rewardsClaimedStore, store_get_ne _ _ (by decide), store_get_self]

theorem rewardsClaimedStore_arg1 (I : ExecutionEnv) :
    (rewardsClaimedStore I).get? "arg1" = some (rewardsClaimedAccountValue I) := by
  rw [rewardsClaimedStore, store_get_self]

theorem rewardsClaimedStore_arg0_getElem? (I : ExecutionEnv) :
    (rewardsClaimedStore I)["arg0"]? = some (rewardsClaimedCometValue I) := by
  rw [← Std.HashMap.get?_eq_getElem?, rewardsClaimedStore_arg0]

theorem rewardsClaimedStore_arg1_getElem? (I : ExecutionEnv) :
    (rewardsClaimedStore I)["arg1"]? = some (rewardsClaimedAccountValue I) := by
  rw [← Std.HashMap.get?_eq_getElem?, rewardsClaimedStore_arg1]

theorem evalExpr_rewardsClaimed_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract,
        locals := (rewardsClaimedStore I).insert "__calldata" (.bytes evm.executionEnv.calldata) }
      evm (.storage (rewardsClaimedRef (.var "arg0") (.var "arg1"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (rewardsClaimedSlotOf I)).toNat)) := by
  have her : evalStorageRef config
      { contract := contract,
        locals := (rewardsClaimedStore I).insert "__calldata" (.bytes evm.executionEnv.calldata) }
      evm (rewardsClaimedRef (.var "arg0") (.var "arg1")) =
      .ok { base := "rewardsClaimed",
            steps := [.mindex (.address (AccountAddress.ofNat
                        (rewardsClaimedCometWord I).toNat)),
                      .mindex (.address (AccountAddress.ofNat
                        (rewardsClaimedAccountWord I).toNat))] } := by
    simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, rewardsClaimedRef,
      evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure, valueToKey?,
      Std.HashMap.get?_eq_getElem?]
    rw [← Std.HashMap.get?_eq_getElem?]
    rw [store_get_ne _ _ (by decide), rewardsClaimedStore_arg0]
    rw [← Std.HashMap.get?_eq_getElem?]
    rw [store_get_ne _ _ (by decide), rewardsClaimedStore_arg1]
  have hty : storageTypeAt? contract.storage
      { base := "rewardsClaimed",
        steps := [.mindex (.address (AccountAddress.ofNat (rewardsClaimedCometWord I).toNat)),
                  .mindex (.address (AccountAddress.ofNat
                    (rewardsClaimedAccountWord I).toNat))] } =
      some (.elem (.int uint256Int)) := by
    simp [storageTypeAt?, contract, storageDecls, List.find?, List.foldlM, storageTypeStep?]
  have hloc : config.storage.layout
      { base := "rewardsClaimed",
        steps := [.mindex (.address (AccountAddress.ofNat (rewardsClaimedCometWord I).toNat)),
                  .mindex (.address (AccountAddress.ofNat
                    (rewardsClaimedAccountWord I).toNat))] } =
      fun _ => some (fieldLoc (rewardsClaimedSlotOf I) 0 32 (by decide) (.int uint256Int)) := by
    rfl
  rw [evalExpr_storage_scalar
    (hbase := by
      change ((rewardsClaimedStore I).insert "__calldata"
        (.bytes evm.executionEnv.calldata)).get? "rewardsClaimed" = none
      rw [store_get_ne _ _ (by decide)]
      rw [rewardsClaimedStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
      simp)
    (her := her) (hty := hty) (hloc := hloc)]
  congr 1
  exact cometRewardsStorageLocLoad_uint256 evm (rewardsClaimedSlotOf I)

theorem cometRewardsRewardsClaimedBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ExecTransitionBody config contract evm (rewardsClaimedStore I) rewardsClaimedTransition.body
      (.returned
        { contract := contract,
          locals := (rewardsClaimedStore I).insert "__calldata"
            (.bytes evm.executionEnv.calldata) }
        evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (rewardsClaimedSlotOf I)).toNat))])) := by
  refine ExecFuncBody.execBlockRet ?_
  simpa [rewardsClaimedTransition, externalEntryGuard, nonpayable, calldataSizeGuard,
    rewardsClaimedRef] using
    (((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (rewardsClaimedStore I) hsize)).returns (by
      exact evalExpr_rewardsClaimed_storage evm I)

theorem cometRewardsRewardsClaimedSelector_size {I : ExecutionEnv}
    (hsel : selIs I (cometRewardsSelBytes 6)) :
    4 ≤ I.calldata.size :=
  calldata_size_ge_of_selIs I (cometRewardsSelBytes 6) rfl hsel

theorem cometRewardsDispatch_rewardsClaimed {cd : ByteArray}
    (hsel : (cometRewardsSelBytes 6 == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some rewardsClaimedTransition := by
  have hcd : cd.extract 0 4 = cometRewardsSelBytes 6 :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [claimTransition, claimToTransition, getRewardOwedTransition, governorTransition,
      rewardConfigTransition])
    (post := [setRewardConfigTransition, setRewardConfigWithMultiplierTransition,
      setRewardsClaimedTransition, transferGovernorTransition, withdrawTokenTransition])
    rfl rfl ?_ (by rw [selectorOf, rewardsClaimedSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, claimSelectorBytes, hcd]; decide
  · rw [selectorOf, claimToSelectorBytes, hcd]; decide
  · rw [selectorOf, getRewardOwedSelectorBytes, hcd]; decide
  · rw [selectorOf, governorSelectorBytes, hcd]; decide
  · rw [selectorOf, rewardConfigSelectorBytes, hcd]; decide

theorem cometRewardsRewardsClaimedCalldataCheckOk {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) :
    UInt256.slt
        ((UInt256.ofNat I.calldata.size) + (UInt256.lnot (⟨3⟩ : UInt256)))
        ⟨64⟩ = ⟨0⟩ := by
  change UInt256.slt
      (UInt256.add (UInt256.ofNat I.calldata.size) (UInt256.lnot (⟨3⟩ : UInt256)))
      ⟨64⟩ = ⟨0⟩
  rw [cometRewardsCalldataSizeAddNot3_eq_sub4 (by omega) hsize]
  exact solcDecodeLenCheckOk_4_64 hsz68 hhi hsize

theorem cometRewardsRewardsClaimedCalldataCheckShort {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68) :
    UInt256.slt
        ((UInt256.ofNat I.calldata.size) + (UInt256.lnot (⟨3⟩ : UInt256)))
        ⟨64⟩ = ⟨1⟩ := by
  change UInt256.slt
      (UInt256.add (UInt256.ofNat I.calldata.size) (UInt256.lnot (⟨3⟩ : UInt256)))
      ⟨64⟩ = ⟨1⟩
  rw [cometRewardsCalldataSizeAddNot3_eq_sub4 hsz4 hsize]
  exact solcDecodeLenCheckShort_4_64 hsz4 hshort hsize

theorem cometRewardsRewardsClaimedCalldataCheckHuge {I : ExecutionEnv}
    (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    UInt256.slt
        ((UInt256.ofNat I.calldata.size) + (UInt256.lnot (⟨3⟩ : UInt256)))
        ⟨64⟩ = ⟨1⟩ := by
  change UInt256.slt
      (UInt256.add (UInt256.ofNat I.calldata.size) (UInt256.lnot (⟨3⟩ : UInt256)))
      ⟨64⟩ = ⟨1⟩
  rw [cometRewardsCalldataSizeAddNot3_eq_sub4 (by omega) hsize]
  exact solcDecodeLenCheckHuge_4_64 hbig hsize

theorem cometRewardsRewardsClaimedX_dec2831_comet {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) rewardsClaimedPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2831⟩
      [⟨1674⟩, ⟨0⟩, ⟨64⟩, ⟨32⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt := cometRewardsRewardsClaimedCalldataCheckOk (I := I) hsz68 hsize hhi
  obtain ⟨_, _, rd1644⟩ := hreach
  have rd1653 := evm_run rd1644 with [jumpdest, pop, pop, pop, callvalue]
  rw [hwv] at rd1653
  have rd1660 := evm_run rd1653 with [
    push2 ⟨670⟩, jumpiNT (by decide),
    dup1, push1 ⟨3⟩, not, calldatasize, add, slt]
  rw [hslt] at rd1660
  exact ⟨_, _, evm_run rd1660 with [
    push2 ⟨670⟩, jumpiNT (by decide),
    push1 ⟨32⟩, swap2, push2 ⟨1674⟩, push2 ⟨2831⟩, jump (by native_decide)]⟩

theorem cometRewardsRewardsClaimedX_dec1674_comet {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (rewardsClaimedCometWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) rewardsClaimedPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1674⟩
      [rewardsClaimedCometWord I, ⟨0⟩, ⟨64⟩, ⟨32⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2831⟩ :=
    cometRewardsRewardsClaimedX_dec2831_comet (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hsz68 hsize hhi hreach
  exact ⟨_, _, evm_run rd2831 with [
    jumpdest, push1 ⟨4⟩, calldataload, swap1,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and, dup3, sub,
    push2 ⟨1004⟩,
    jumpiNT (by
      have hclean :
          UInt256.land
            (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
            solcAddrMask =
          uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32) := by
        exact solcAddrMask_clean (by
          simpa [rewardsClaimedCometWord, calldataWord] using hcanonComet)
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, hclean]
      exact u256_sub_self _),
    jump (by native_decide)]⟩

theorem cometRewardsRewardsClaimedX_dec2853_account {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (rewardsClaimedCometWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) rewardsClaimedPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2853⟩
      [⟨1683⟩, ⟨64⟩, rewardsClaimedCometWord I, ⟨0⟩, ⟨64⟩, ⟨32⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1674⟩ :=
    cometRewardsRewardsClaimedX_dec1674_comet (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hwv hsz68 hsize hhi hcanonComet hreach
  exact ⟨_, _, evm_run rd1674 with [
    jumpdest, dup3, push2 ⟨1683⟩, push2 ⟨2853⟩, jump (by native_decide)]⟩

theorem cometRewardsRewardsClaimedX_dec1683_account {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (rewardsClaimedCometWord I).toNat < EVM.addressModulus)
    (hcanonAccount : (rewardsClaimedAccountWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) rewardsClaimedPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1683⟩
      [rewardsClaimedAccountWord I, ⟨64⟩, rewardsClaimedCometWord I,
        ⟨0⟩, ⟨64⟩, ⟨32⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2853⟩ :=
    cometRewardsRewardsClaimedX_dec2853_account (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hwv hsz68 hsize hhi hcanonComet hreach
  exact ⟨_, _, evm_run rd2853 with [
    jumpdest, push1 ⟨36⟩, calldataload, swap1,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and, dup3, sub,
    push2 ⟨1004⟩,
    jumpiNT (by
      have hclean :
          UInt256.land
            (uInt256OfByteArray (I.calldata.readBytes (⟨36⟩ : UInt256).toNat 32))
            solcAddrMask =
          uInt256OfByteArray (I.calldata.readBytes (⟨36⟩ : UInt256).toNat 32) := by
        exact solcAddrMask_clean (by
          simpa [rewardsClaimedAccountWord, calldataWord] using hcanonAccount)
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, hclean]
      exact u256_sub_self _),
    jump (by native_decide)]⟩

set_option maxHeartbeats 2000000 in
theorem cometRewardsX_rewardsClaimed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (rewardsClaimedCometWord I).toNat < EVM.addressModulus)
    (hcanonAccount : (rewardsClaimedAccountWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) rewardsClaimedPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDret cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (rewardsClaimedWord σ I)) := by
  obtain ⟨_, _, rd1683⟩ :=
    cometRewardsRewardsClaimedX_dec1683_account (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hwv hsz68 hsize hhi hcanonComet hcanonAccount hreach
  have hinner := rewardsClaimedInnerKeccakSlot (rewardsClaimedCometWord I)
  have houter := rewardsClaimedOuterKeccakSlot
    (rewardsClaimedCometWord I) (rewardsClaimedAccountWord I)
  have hslot := rewardsClaimedSlotOf_eq_solc I hcanonComet hcanonAccount
  have rd1716 := evm_run rd1683 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap3, dup4, and,
    dup5,
    raw mstore 0 (wordAt0Mem (rewardsClaimedCometWord I) solcFreePtrMem)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide, solcAddrMask_clean_left hcanonComet]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨2⟩, dup7,
    raw mstore 0 (rewardsClaimedInnerHashMem (rewardsClaimedCometWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    swap3,
    raw keccak256 0 (solcMappingSlot ⟨2⟩ (rewardsClaimedCometWord I))
      (UInt256.ofNat 3) (by decide) mem_cost hinner (by decide) (by evm_ov),
    swap2, and, push1 ⟨0⟩, swap1, dup2,
    raw mstore 0
      (wordAt0Mem (rewardsClaimedAccountWord I)
        (rewardsClaimedInnerHashMem (rewardsClaimedCometWord I)))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide, solcAddrMask_clean hcanonAccount]
        rfl)
      (by decide) (by evm_ov),
    swap1, dup4,
    raw mstore 0
      (rewardsClaimedOuterHashMem (rewardsClaimedCometWord I)
        (rewardsClaimedAccountWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    dup2, swap1,
    raw keccak256 0
      (solcMappingSlot (solcMappingSlot ⟨2⟩ (rewardsClaimedCometWord I))
        (rewardsClaimedAccountWord I))
      (UInt256.ofNat 3) (by decide) mem_cost houter (by decide) (by evm_ov)]
  rw [← hslot] at rd1716
  obtain ⟨_, _, rd1717⟩ := rd1716.sload (by decide) (by evm_ov)
  have rd1722 := evm_run rd1717 with [
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide) mem_cost
      (rewardsClaimedOuterHashMem_mload64
        (rewardsClaimedCometWord I) (rewardsClaimedAccountWord I))
      (by decide) (by evm_ov),
    swap1, dup2,
    raw mstore 6
      (rewardsClaimedReturnMem (rewardsClaimedCometWord I)
        (rewardsClaimedAccountWord I) (rewardsClaimedWord σ I))
      (UInt256.ofNat 5) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov)]
  exact evm_run rd1722 with [
    raw ret 0 (UInt256.toByteArray (rewardsClaimedWord σ I)) (by decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (⟨32⟩ : UInt256).toNat = 32 from by decide]
        exact rewardsClaimedReturnMem_read128
          (rewardsClaimedCometWord I) (rewardsClaimedAccountWord I)
          (rewardsClaimedWord σ I))
      (by evm_ov)]

theorem cometRewardsRewardsClaimedX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz4 : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) rewardsClaimedPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt := cometRewardsRewardsClaimedCalldataCheckShort (I := I) hsz4 hsize hshort
  obtain ⟨_, _, rd1644⟩ := hreach
  have rd1653 := evm_run rd1644 with [jumpdest, pop, pop, pop, callvalue]
  rw [hwv] at rd1653
  have rd1660 := evm_run rd1653 with [
    push2 ⟨670⟩, jumpiNT (by decide),
    dup1, push1 ⟨3⟩, not, calldatasize, add, slt]
  rw [hslt] at rd1660
  exact evm_run rd1660 with [
    push2 ⟨670⟩, jumpiT (by decide) (by native_decide),
    jumpdest, pop, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem cometRewardsRewardsClaimedX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) rewardsClaimedPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt := cometRewardsRewardsClaimedCalldataCheckHuge (I := I) hsize hbig
  obtain ⟨_, _, rd1644⟩ := hreach
  have rd1653 := evm_run rd1644 with [jumpdest, pop, pop, pop, callvalue]
  rw [hwv] at rd1653
  have rd1660 := evm_run rd1653 with [
    push2 ⟨670⟩, jumpiNT (by decide),
    dup1, push1 ⟨3⟩, not, calldatasize, add, slt]
  rw [hslt] at rd1660
  exact evm_run rd1660 with [
    push2 ⟨670⟩, jumpiT (by decide) (by native_decide),
    jumpdest, pop, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem cometRewardsRewardsClaimedX_noncanon_comet {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (rewardsClaimedCometWord I)
      (UInt256.land (rewardsClaimedCometWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) rewardsClaimedPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2831⟩ :=
    cometRewardsRewardsClaimedX_dec2831_comet (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hsz68 hsize hhi hreach
  exact evm_run rd2831 with [
    jumpdest, push1 ⟨4⟩, calldataload, swap1,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and, dup3, sub,
    push2 ⟨1004⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      exact u256_sub_ne_zero_of_ne (by
        intro heq
        have hclean :
            UInt256.eq (rewardsClaimedCometWord I)
              (UInt256.land (rewardsClaimedCometWord I) solcAddrMask) = ⟨1⟩ := by
          have heq' : rewardsClaimedCometWord I =
              UInt256.land (rewardsClaimedCometWord I) solcAddrMask := by
            simpa [rewardsClaimedCometWord, calldataWord] using heq
          rw [← heq']
          exact uInt256_eq_self _
        rw [hclean] at hnc
        exact (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) hnc))
      (by native_decide),
    jumpdest, push1 ⟨0⟩, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem cometRewardsRewardsClaimedX_noncanon_account {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (rewardsClaimedCometWord I).toNat < EVM.addressModulus)
    (hnc : UInt256.eq (rewardsClaimedAccountWord I)
      (UInt256.land (rewardsClaimedAccountWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) rewardsClaimedPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2853⟩ :=
    cometRewardsRewardsClaimedX_dec2853_account (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hwv hsz68 hsize hhi hcanonComet hreach
  exact evm_run rd2853 with [
    jumpdest, push1 ⟨36⟩, calldataload, swap1,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and, dup3, sub,
    push2 ⟨1004⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      exact u256_sub_ne_zero_of_ne (by
        intro heq
        have hclean :
            UInt256.eq (rewardsClaimedAccountWord I)
              (UInt256.land (rewardsClaimedAccountWord I) solcAddrMask) = ⟨1⟩ := by
          have heq' : rewardsClaimedAccountWord I =
              UInt256.land (rewardsClaimedAccountWord I) solcAddrMask := by
            simpa [rewardsClaimedAccountWord, calldataWord] using heq
          rw [← heq']
          exact uInt256_eq_self _
        rw [hclean] at hnc
        exact (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) hnc))
      (by native_decide),
    jumpdest, push1 ⟨0⟩, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

/-- `rewardsClaimed(address,address)` body, reached at pc 1644. -/
theorem cometRewardsRewardsClaimedBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = cometRewardsBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (cometRewardsSelBytes 6))
    (hreach : ∃ k C, RD cometRewardsBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) rewardsClaimedPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have _hperm : I.perm = true := hperm
  have hsz4 := cometRewardsRewardsClaimedSelector_size hsel
  have hd := cometRewardsDispatch_rewardsClaimed (cd := I.calldata) hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonComet : (rewardsClaimedCometWord I).toNat < EVM.addressModulus
      · by_cases hcanonAccount : (rewardsClaimedAccountWord I).toNat < EVM.addressModulus
        · have hdec :=
            cometRewardsDecode_rewardsClaimed_ok (I := I) hsz68 hhi hcanonComet hcanonAccount
          have hslot := rewardsClaimedSlotOf_eq_solc I hcanonComet hcanonAccount
          have hword : rewardsClaimedWord σ_evm I = rewardsClaimedWord σ_solm I :=
            accountMapEquiv_storage_findD hAccounts I.codeOwner (rewardsClaimedSlotOf I) ⟨0⟩
          have hbody :
              ExecTransitionBody config contract
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (rewardsClaimedStore I)
                rewardsClaimedTransition.body
                (.returned
                  { contract := contract,
                    locals := (rewardsClaimedStore I).insert "__calldata"
                      (.bytes I.calldata) }
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (some [(.int (Int.ofNat (rewardsClaimedWord σ_solm I).toNat))])) := by
            simpa [rewardsClaimedWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
              using cometRewardsRewardsClaimedBodyReturns
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                (by simp only [initState]; exact hwv)
                (by simp only [initState]; exact hhi)
          exact (cometRewardsX_rewardsClaimed (g := Sat256.ofUInt256 g)
              hwv hsz68 hsize hhi hcanonComet hcanonAccount hreach)
            |>.reEquivExecutionTransport hcode hd hdec hbody (by rw [← hword])
              hAccounts
              (returnEquiv_of_encode
                (by simpa [uint256] using uint256ReturnEncoding (rewardsClaimedWord σ_evm I)))
        · have hdec := cometRewardsDecode_rewardsClaimed_none_noncanon_account
            (I := I) hsz68 hhi hcanonComet hcanonAccount
          have hnc : UInt256.eq (rewardsClaimedAccountWord I)
              (UInt256.land (rewardsClaimedAccountWord I) solcAddrMask) = ⟨0⟩ :=
            uInt256_eq_zero_of_ne
              (fun he => hcanonAccount (solcAddrCanonical_of_clean he))
          exact (cometRewardsRewardsClaimedX_noncanon_account (g := Sat256.ofUInt256 g)
              hwv hsz68 hsize hhi hcanonComet hnc hreach)
            |>.reEquivDecodingFailed hcode hd hdec
      · have hdec := cometRewardsDecode_rewardsClaimed_none_noncanon_comet
          (I := I) hsz68 hhi hcanonComet
        have hnc : UInt256.eq (rewardsClaimedCometWord I)
            (UInt256.land (rewardsClaimedCometWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne
            (fun he => hcanonComet (solcAddrCanonical_of_clean he))
        exact (cometRewardsRewardsClaimedX_noncanon_comet (g := Sat256.ofUInt256 g)
            hwv hsz68 hsize hhi hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbig : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := cometRewardsDecode_rewardsClaimed_none_huge (I := I) hbig
      exact (cometRewardsRewardsClaimedX_hugearg (g := Sat256.ofUInt256 g)
          hwv hsize hbig hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := cometRewardsDecode_rewardsClaimed_none_short (I := I) hsz4 hshort
    exact (cometRewardsRewardsClaimedX_shortarg (g := Sat256.ofUInt256 g)
        hwv hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.CompoundIII.CometRewards
