import Benchmarks.CompoundIII.CometRewards.Common
import Benchmarks.CompoundIII.CometRewards.Governor

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.CompoundIII.CometRewards

/-! ## `transferGovernor(address)` -/

abbrev transferGovernorNewGovernorWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev transferGovernorNewGovernorValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (transferGovernorNewGovernorWord I).toNat)

abbrev transferGovernorStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "newGovernor" (transferGovernorNewGovernorValue I)

def transferGovernorStoredWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  setAddressOffset0Word (governorWord σ I) (transferGovernorNewGovernorWord I)

def transferGovernorPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      (transferGovernorNewGovernorWord I))

abbrev transferGovernorFrame (evm : EVM.State) (I : ExecutionEnv) : Frame :=
  { contract := contract,
    locals := (transferGovernorStore I).insert "__calldata" (.bytes evm.executionEnv.calldata) }

theorem cometRewardsDecode_transferGovernor_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (transferGovernorNewGovernorWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode
      (transferGovernorTransition.params.map Param.name)
      (transitionSignature transferGovernorTransition).paramTypes I.calldata =
        some (transferGovernorStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["newGovernor"] [addr] I.calldata = _
  simpa [config, transferGovernorStore, transferGovernorNewGovernorValue,
    transferGovernorNewGovernorWord, calldataWord]
    using decodeCalldata_address_ok (cd := I.calldata) (x := "newGovernor")
      hsz36 hbig hcanon

theorem cometRewardsDecode_transferGovernor_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode
      (transferGovernorTransition.params.map Param.name)
      (transitionSignature transferGovernorTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["newGovernor"] [addr] I.calldata = none
  simpa [config, addr] using decodeCalldata_address_none_short
    (cd := I.calldata) (x := "newGovernor") hsz4 hshort

theorem cometRewardsDecode_transferGovernor_none_noncanon {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (transferGovernorNewGovernorWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode
      (transferGovernorTransition.params.map Param.name)
      (transitionSignature transferGovernorTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["newGovernor"] [addr] I.calldata = none
  simpa [config, addr, transferGovernorNewGovernorWord, calldataWord]
    using decodeCalldata_address_none_noncanon
      (cd := I.calldata) (x := "newGovernor") hsz36 hbig hnc

theorem cometRewardsDecode_transferGovernor_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode
      (transferGovernorTransition.params.map Param.name)
      (transitionSignature transferGovernorTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["newGovernor"] [addr] I.calldata = none
  simpa [config, addr] using decodeCalldata_address_none_huge
    (cd := I.calldata) (x := "newGovernor") hbig

theorem cometRewardsTransferGovernorSelector_size {I : ExecutionEnv}
    (hsel : selIs I (cometRewardsSelBytes 9)) :
    4 ≤ I.calldata.size :=
  calldata_size_ge_of_selIs I (cometRewardsSelBytes 9) rfl hsel

theorem cometRewardsDispatch_transferGovernor {cd : ByteArray}
    (hsel : (cometRewardsSelBytes 9 == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some transferGovernorTransition := by
  have hcd : cd.extract 0 4 = cometRewardsSelBytes 9 :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [claimTransition, claimToTransition, getRewardOwedTransition, governorTransition,
      rewardConfigTransition, rewardsClaimedTransition, setRewardConfigTransition,
      setRewardConfigWithMultiplierTransition, setRewardsClaimedTransition])
    (post := [withdrawTokenTransition])
    rfl rfl ?_ (by rw [selectorOf, transferGovernorSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, claimSelectorBytes, hcd]
    decide
  · rw [selectorOf, claimToSelectorBytes, hcd]
    decide
  · rw [selectorOf, getRewardOwedSelectorBytes, hcd]
    decide
  · rw [selectorOf, governorSelectorBytes, hcd]
    decide
  · rw [selectorOf, rewardConfigSelectorBytes, hcd]
    decide
  · rw [selectorOf, rewardsClaimedSelectorBytes, hcd]
    decide
  · rw [selectorOf, setRewardConfigSelectorBytes, hcd]
    decide
  · rw [selectorOf, setRewardConfigWithMultiplierSelectorBytes, hcd]
    decide
  · rw [selectorOf, setRewardsClaimedSelectorBytes, hcd]
    decide

theorem cometRewardsTransferGovernorCalldataCheckOk {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) :
    UInt256.slt
        ((UInt256.ofNat I.calldata.size) + (UInt256.lnot (⟨3⟩ : UInt256)))
        ⟨32⟩ = ⟨0⟩ := by
  change UInt256.slt
      (UInt256.add (UInt256.ofNat I.calldata.size) (UInt256.lnot (⟨3⟩ : UInt256)))
      ⟨32⟩ = ⟨0⟩
  rw [cometRewardsCalldataSizeAddNot3_eq_sub4 (by omega) hsize]
  exact solcDecodeLenCheckOk_4_32 hsz36 hhi hsize

theorem cometRewardsTransferGovernorCalldataCheckShort {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36) :
    UInt256.slt
        ((UInt256.ofNat I.calldata.size) + (UInt256.lnot (⟨3⟩ : UInt256)))
        ⟨32⟩ = ⟨1⟩ := by
  change UInt256.slt
      (UInt256.add (UInt256.ofNat I.calldata.size) (UInt256.lnot (⟨3⟩ : UInt256)))
      ⟨32⟩ = ⟨1⟩
  rw [cometRewardsCalldataSizeAddNot3_eq_sub4 hsz4 hsize]
  exact solcDecodeLenCheckShort_4_32 hsz4 hshort hsize

theorem cometRewardsTransferGovernorCalldataCheckHuge {I : ExecutionEnv}
    (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    UInt256.slt
        ((UInt256.ofNat I.calldata.size) + (UInt256.lnot (⟨3⟩ : UInt256)))
        ⟨32⟩ = ⟨1⟩ := by
  change UInt256.slt
      (UInt256.add (UInt256.ofNat I.calldata.size) (UInt256.lnot (⟨3⟩ : UInt256)))
      ⟨32⟩ = ⟨1⟩
  rw [cometRewardsCalldataSizeAddNot3_eq_sub4 (by omega) hsize]
  exact solcDecodeLenCheckHuge_4_32 hbig hsize

theorem cometRewardsTransferGovernorX_dec2831_newGovernor {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) transferGovernorPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2831⟩
      [⟨829⟩, ⟨64⟩, ⟨4⟩, ⟨0⟩, cometRewardsSelWord I, ⟨4⟩, ⟨224⟩, ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt := cometRewardsTransferGovernorCalldataCheckOk (I := I) hsz36 hsize hhi
  obtain ⟨_, _, rd801⟩ := hreach
  have rd806 := evm_run rd801 with [
    jumpdest, dup5, dup3, dup6, callvalue]
  rw [hwv] at rd806
  have rd818 := evm_run rd806 with [
    push2 ⟨938⟩, jumpiNT (by decide),
    push1 ⟨32⟩, calldatasize, push1 ⟨3⟩, not, add, slt]
  rw [show UInt256.lnot (⟨3⟩ : UInt256) + UInt256.ofNat I.calldata.size =
      UInt256.ofNat I.calldata.size + UInt256.lnot (⟨3⟩ : UInt256)
      from u256_add_comm _ _] at rd818
  rw [hslt] at rd818
  have rd828 := evm_run rd818 with [
    push2 ⟨938⟩, jumpiNT (by decide),
    push2 ⟨829⟩, push2 ⟨2831⟩]
  exact ⟨_, _, evm_run rd828 with [jump (by native_decide)]⟩

theorem cometRewardsTransferGovernorX_dec829_newGovernor {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (transferGovernorNewGovernorWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) transferGovernorPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨829⟩
      [transferGovernorNewGovernorWord I, ⟨64⟩, ⟨4⟩, ⟨0⟩, cometRewardsSelWord I,
        ⟨4⟩, ⟨224⟩, ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2831⟩ :=
    cometRewardsTransferGovernorX_dec2831_newGovernor (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hsz36 hsize hhi hreach
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
          simpa [transferGovernorNewGovernorWord, calldataWord] using hcanon)
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, hclean]
      exact u256_sub_self _),
    jump (by native_decide)]⟩

theorem cometRewardsTransferGovernorX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz4 : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) transferGovernorPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt := cometRewardsTransferGovernorCalldataCheckShort (I := I) hsz4 hsize hshort
  obtain ⟨_, _, rd801⟩ := hreach
  have rd806 := evm_run rd801 with [
    jumpdest, dup5, dup3, dup6, callvalue]
  rw [hwv] at rd806
  have rd818 := evm_run rd806 with [
    push2 ⟨938⟩, jumpiNT (by decide),
    push1 ⟨32⟩, calldatasize, push1 ⟨3⟩, not, add, slt]
  rw [show UInt256.lnot (⟨3⟩ : UInt256) + UInt256.ofNat I.calldata.size =
      UInt256.ofNat I.calldata.size + UInt256.lnot (⟨3⟩ : UInt256)
      from u256_add_comm _ _] at rd818
  rw [hslt] at rd818
  exact evm_run rd818 with [
    push2 ⟨938⟩, jumpiT (by decide) (by native_decide),
    jumpdest, dup3, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem cometRewardsTransferGovernorX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) transferGovernorPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt := cometRewardsTransferGovernorCalldataCheckHuge (I := I) hsize hbig
  obtain ⟨_, _, rd801⟩ := hreach
  have rd806 := evm_run rd801 with [
    jumpdest, dup5, dup3, dup6, callvalue]
  rw [hwv] at rd806
  have rd818 := evm_run rd806 with [
    push2 ⟨938⟩, jumpiNT (by decide),
    push1 ⟨32⟩, calldatasize, push1 ⟨3⟩, not, add, slt]
  rw [show UInt256.lnot (⟨3⟩ : UInt256) + UInt256.ofNat I.calldata.size =
      UInt256.ofNat I.calldata.size + UInt256.lnot (⟨3⟩ : UInt256)
      from u256_add_comm _ _] at rd818
  rw [hslt] at rd818
  exact evm_run rd818 with [
    push2 ⟨938⟩, jumpiT (by decide) (by native_decide),
    jumpdest, dup3, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem cometRewardsTransferGovernorX_noncanon_newGovernor {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (transferGovernorNewGovernorWord I)
      (UInt256.land (transferGovernorNewGovernorWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) transferGovernorPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2831⟩ :=
    cometRewardsTransferGovernorX_dec2831_newGovernor (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hsz36 hsize hhi hreach
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
            UInt256.eq (transferGovernorNewGovernorWord I)
              (UInt256.land (transferGovernorNewGovernorWord I) solcAddrMask) = ⟨1⟩ := by
          have heq' : transferGovernorNewGovernorWord I =
              UInt256.land (transferGovernorNewGovernorWord I) solcAddrMask := by
            simpa [transferGovernorNewGovernorWord, calldataWord] using heq
          rw [← heq']
          exact uInt256_eq_self _
        rw [hclean] at hnc
        exact (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) hnc))
      (by native_decide),
    jumpdest, push1 ⟨0⟩, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem transferGovernorStoredWord_evm_expr (σ : AccountMap) (I : ExecutionEnv) :
    UInt256.lor
        (UInt256.land (transferGovernorNewGovernorWord I) solcAddrMask)
        (UInt256.land (UInt256.lnot solcAddrMask) (governorWord σ I)) =
      transferGovernorStoredWord σ I := by
  unfold transferGovernorStoredWord setAddressOffset0Word
  rw [u256_land_comm (UInt256.lnot solcAddrMask) (governorWord σ I)]
  exact u256_lor_comm
    (UInt256.land (transferGovernorNewGovernorWord I) solcAddrMask)
    (UInt256.land (governorWord σ I) (UInt256.lnot solcAddrMask))

theorem solcWord_eq_of_maskedAddress_eq_source {w : UInt256} {I : ExecutionEnv}
    (h : AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat = I.source) :
    UInt256.land w solcAddrMask = solcSourceWord I := by
  apply u256_inj
  have hcanon := solcAddrMask_result_canonical w
  have hval := congrArg Fin.val h
  unfold AccountAddress.ofNat at hval
  rw [Fin.val_ofNat] at hval
  rw [solcSourceWord_toNat]
  rw [Nat.mod_eq_of_lt (by
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)] at hval
  exact hval

theorem transferGovernorStore_newGovernor (I : ExecutionEnv) :
    (transferGovernorStore I).get? "newGovernor" =
      some (transferGovernorNewGovernorValue I) := by
  rw [transferGovernorStore, store_get_self]

theorem transferGovernorStore_governor (I : ExecutionEnv) :
    (transferGovernorStore I).get? "governor" = none := by
  rw [transferGovernorStore, store_get_ne _ _ (by decide)]
  native_decide

theorem evalExpr_transferGovernor_newGovernor (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config (transferGovernorFrame evm I) evm (.var "newGovernor") =
      .ok (transferGovernorNewGovernorValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [store_get_ne _ _ (by decide), transferGovernorStore_newGovernor]

theorem evalExpr_transferGovernor_governor (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config (transferGovernorFrame evm I) evm (.storage governorRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef config
      (transferGovernorFrame evm I) evm governorRef =
        .ok { base := "governor", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, governorRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage
      ({ base := "governor", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar (t := .address)
    (hbase := by
      change ((transferGovernorStore I).insert "__calldata"
        (.bytes evm.executionEnv.calldata)).get? "governor" = none
      rw [store_get_ne _ _ (by decide)]
      exact transferGovernorStore_governor I)
    (her := her) (hty := hty) (hloc := by rfl),
    cometRewardsStorageLocLoad_address_offset0]

theorem evalExpr_transferGovernor_sender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config (transferGovernorFrame evm I) evm sender =
      .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_transferGovernor_auth_true (evm : EVM.State) (I : ExecutionEnv)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv) :
    evalExpr? config (transferGovernorFrame evm I) evm
      (.binary .eq sender (.storage governorRef)) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_transferGovernor_sender, evalExpr_transferGovernor_governor,
    bind, EvalResult.bind, evalBinaryOp?]
  rw [solcMaskedAddress_eq_source_of_word_eq (I := evm.executionEnv) hgov]
  simp [BEq.beq]

theorem evalExpr_transferGovernor_auth_false (evm : EVM.State) (I : ExecutionEnv)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask ≠
        solcSourceWord evm.executionEnv) :
    evalExpr? config (transferGovernorFrame evm I) evm
      (.binary .eq sender (.storage governorRef)) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_transferGovernor_sender, evalExpr_transferGovernor_governor,
    bind, EvalResult.bind, evalBinaryOp?]
  have haddr :
      evm.executionEnv.source ≠
        AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
            solcAddrMask).toNat := by
    intro haddr
    exact hgov (by
      exact solcWord_eq_of_maskedAddress_eq_source (I := evm.executionEnv) haddr.symm)
  rw [show ((.address evm.executionEnv.source : Value) ==
        .address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
            solcAddrMask).toNat)) = false by
    simp [BEq.beq, haddr]]

theorem transferGovernorAssignGovernor (evm : EVM.State) (I : ExecutionEnv)
    (hcanon : (transferGovernorNewGovernorWord I).toNat < EVM.addressModulus) :
    assignStorageRef? config (transferGovernorFrame evm I)
      evm .storage governorRef (transferGovernorNewGovernorValue I) =
      .ok (transferGovernorFrame evm I, transferGovernorPostState evm I) := by
  have her : evalStorageRef config
      (transferGovernorFrame evm I) evm governorRef =
        .ok { base := "governor", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, governorRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage
      ({ base := "governor", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
    decide
  have hstore :
      storageLocStore evm (fieldLoc ⟨0⟩ 0 20 (by decide) .address)
          (transferGovernorNewGovernorValue I) =
        some (transferGovernorPostState evm I) := by
    simpa [transferGovernorPostState, transferGovernorNewGovernorValue,
      fieldLoc, loc, addressOffset0Loc] using
      storageLocStore_address_offset0 evm ⟨0⟩
        (transferGovernorNewGovernorWord I) hcanon
  exact assignStorageRef_storage_scalar_value (cfg := config)
    (solm := transferGovernorFrame evm I)
    (evm := evm) (evm' := transferGovernorPostState evm I)
    (slot := governorRef) (er := { base := "governor", steps := [] })
    (ty := .elem .address) (loc := fieldLoc ⟨0⟩ 0 20 (by decide) .address)
    (value := transferGovernorNewGovernorValue I)
    (by
      change ((transferGovernorStore I).insert "__calldata"
        (.bytes evm.executionEnv.calldata)).get? "governor" = none
      rw [store_get_ne _ _ (by decide)]
      exact transferGovernorStore_governor I)
    her hty (by rfl) (by trivial) hstore

theorem cometRewardsTransferGovernorBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (hcanon : (transferGovernorNewGovernorWord I).toNat < EVM.addressModulus) :
    ExecTransitionBody config contract evm (transferGovernorStore I)
      transferGovernorTransition.body
      (.returned
        (transferGovernorFrame evm I)
        (transferGovernorPostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  simpa [transferGovernorTransition, externalEntryGuard, nonpayable, calldataSizeGuard] using
    ((((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (transferGovernorStore I) hsize)).requireStep
          (evalExpr_transferGovernor_auth_true evm I hgov)).run
      (ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_transferGovernor_newGovernor evm I)
          (transferGovernorAssignGovernor evm I hcanon))
        ExecBlock.nil)

theorem cometRewardsTransferGovernorBodyReverts_auth (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask ≠
        solcSourceWord evm.executionEnv) :
    ExecTransitionBody config contract evm (transferGovernorStore I)
      transferGovernorTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [transferGovernorTransition, externalEntryGuard, nonpayable, calldataSizeGuard] using
    ((((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (transferGovernorStore I) hsize)).requireRevert
          (evalExpr_transferGovernor_auth_false evm I hgov))

theorem cometRewardsTransferGovernorBodyRevertsHuge (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbig : 2 ^ 255 + 4 ≤ evm.executionEnv.calldata.size) :
    ExecTransitionBody config contract evm (transferGovernorStore I)
      transferGovernorTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [transferGovernorTransition, externalEntryGuard, nonpayable, calldataSizeGuard] using
    (((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireRevert
        (cometRewardsCalldataGuard_false evm (transferGovernorStore I) hbig))

def transferGovernorUnauthorizedSelector : UInt256 :=
  UInt256.shiftLeft (⟨431085831⟩ : UInt256) ⟨227⟩

noncomputable def transferGovernorUnauthorizedMem (caller : UInt256) : ByteArray :=
  (UInt256.toByteArray caller).write 0
    (solcReturnMem transferGovernorUnauthorizedSelector) 132 32

set_option maxHeartbeats 1000000 in
theorem cometRewardsX_transferGovernor_success {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (transferGovernorNewGovernorWord I).toNat < EVM.addressModulus)
    (hauth : governorReturnWord σ I = solcSourceWord I)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) transferGovernorPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDret cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ (transferGovernorStoredWord σ I))
      ByteArray.empty := by
  obtain ⟨_, _, rd829⟩ :=
    cometRewardsTransferGovernorX_dec829_newGovernor (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hwv hsz36 hsize hhi hcanon hreach
  have rd831 := evm_run rd829 with [jumpdest, dup4]
  obtain ⟨_, _, rd832₀⟩ := rd831.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd832⟩ : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨832⟩
      [governorWord σ I, transferGovernorNewGovernorWord I, ⟨64⟩, ⟨4⟩, ⟨0⟩,
        cometRewardsSelWord I, ⟨4⟩, ⟨224⟩, ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [governorWord] using rd832₀⟩
  have rd856₀ := evm_run rd832 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup1, dup3, and,
    swap5, swap2, swap4, swap3, swap1, swap2, caller, dup7, swap1, sub]
  have rd856 := rd856₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by decide] at rd856
  rw [show UInt256.sub (solcSourceWord I) (governorReturnWord σ I) = ⟨0⟩ by
    rw [← hauth, u256_sub_self]] at rd856
  have rd857 := evm_run rd856 with [push2 ⟨915⟩, jumpiNT (by decide)]
  have rd873₀ := evm_run rd857 with [
    pop, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, swap3, swap1,
    swap3, and, dup3]
  have rd874₀ := RD.lor rd873₀ (by decide) (by evm_ov)
  have rd874 := rd874₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by decide] at rd874
  rw [transferGovernorStoredWord_evm_expr] at rd874
  have rd875 := evm_run rd874 with [dup5]
  obtain ⟨_, _, rd876₀⟩ := rd875.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd876⟩ : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨876⟩
      [⟨64⟩, UInt256.land (transferGovernorNewGovernorWord I) solcAddrMask,
        governorReturnWord σ I, ⟨0⟩, cometRewardsSelWord I, ⟨4⟩, ⟨224⟩, ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ (transferGovernorStoredWord σ I)) k C := by
    exact ⟨_, _, by simpa [governorReturnWord] using rd876₀⟩
  have rd878 := evm_run rd876 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    swap2]
  have rd911 := rd878.pushConst
    (⟨50513617581459704403207506987288494667897455834126950341013904819243569522016⟩ :
      UInt256)
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd913 := evm_run rd911 with [dup5, dup5]
  have rd914 := rd913.log3 0 (UInt256.ofNat 3) (by decide) hperm mem_cost
    (by decide) (by evm_ov)
  exact evm_run rd914 with [
    raw ret 0 ByteArray.empty (by decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (⟨0⟩ : UInt256).toNat = 0 from by decide]
        exact byteArray_readWithPadding_zero _ 128)
      (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem cometRewardsX_transferGovernor_revert_auth {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (transferGovernorNewGovernorWord I).toNat < EVM.addressModulus)
    (hauth : governorReturnWord σ I ≠ solcSourceWord I)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) transferGovernorPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd829⟩ :=
    cometRewardsTransferGovernorX_dec829_newGovernor (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hwv hsz36 hsize hhi hcanon hreach
  have rd831 := evm_run rd829 with [jumpdest, dup4]
  obtain ⟨_, _, rd832₀⟩ := rd831.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd832⟩ : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨832⟩
      [governorWord σ I, transferGovernorNewGovernorWord I, ⟨64⟩, ⟨4⟩, ⟨0⟩,
        cometRewardsSelWord I, ⟨4⟩, ⟨224⟩, ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [governorWord] using rd832₀⟩
  have rd856₀ := evm_run rd832 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup1, dup3, and,
    swap5, swap2, swap4, swap3, swap1, swap2, caller, dup7, swap1, sub]
  have rd856 := rd856₀
  have hsub : UInt256.sub (solcSourceWord I) (governorReturnWord σ I) ≠ ⟨0⟩ := by
    exact u256_sub_ne_zero_of_ne (by
      intro h
      exact hauth h.symm)
  exact evm_run rd856 with [
    push2 ⟨915⟩, jumpiT (by simpa using hsub) (by native_decide),
    jumpdest, push1 ⟨36⟩, swap1, dup5,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    swap1, push4 ⟨431085831⟩, push1 ⟨227⟩, shl, dup3,
    raw mstore 6 (solcReturnMem transferGovernorUnauthorizedSelector)
      (UInt256.ofNat 5) (by decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        rfl)
      (by decide) (by evm_ov),
    caller, swap1, dup3, add,
    raw mstore 3 (transferGovernorUnauthorizedMem (solcSourceWord I))
      (UInt256.ofNat 6) (by decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by decide,
          show (⟨132⟩ : UInt256).toNat = 132 from by decide]
        unfold transferGovernorUnauthorizedMem solcSourceWord
        rfl)
      (by decide) (by evm_ov),
    raw rev 0 (by decide) mem_cost (by evm_ov)]

/-- `transferGovernor(address)` body, reached at pc 801. -/
theorem cometRewardsTransferGovernorBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = cometRewardsBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (cometRewardsSelBytes 9))
    (hreach : ∃ k C, RD cometRewardsBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) transferGovernorPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have _hperm : I.perm = true := hperm
  have hsz4 := cometRewardsTransferGovernorSelector_size hsel
  have hd := cometRewardsDispatch_transferGovernor (cd := I.calldata) hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (transferGovernorNewGovernorWord I).toNat < EVM.addressModulus
      · have hdec := cometRewardsDecode_transferGovernor_ok (I := I) hsz36 hhi hcanon
        have hword : governorWord σ_evm I = governorWord σ_solm I :=
          accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ ⟨0⟩
        have hretWord : governorReturnWord σ_evm I = governorReturnWord σ_solm I := by
          simp [governorReturnWord, hword]
        by_cases hauth : governorReturnWord σ_evm I = solcSourceWord I
        · have hauthSolm : governorReturnWord σ_solm I = solcSourceWord I := by
            rw [← hretWord]
            exact hauth
          have hbody :
              ExecTransitionBody config contract
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (transferGovernorStore I)
                transferGovernorTransition.body
                (.returned
                  (transferGovernorFrame
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
                  (transferGovernorPostState
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
                  none) := by
            exact cometRewardsTransferGovernorBodyReturns
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv)
              (by simp only [initState]; exact hhi)
              (by
                simpa [governorReturnWord, governorWord, initState, Solm.EVM.storageLoad,
                  State.lookupAccount] using hauthSolm)
              hcanon
          have hstored :
              transferGovernorStoredWord σ_evm I = transferGovernorStoredWord σ_solm I := by
            simp [transferGovernorStoredWord, hword]
          have hcreated :
              (cA, sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
                  (transferGovernorStoredWord σ_evm I)).1 =
                (transferGovernorPostState
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I).createdAccounts := by
            simp [transferGovernorPostState, initState, storageStore_createdAccounts]
          have hAccountsPost :
              accountMapEquiv
                (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
                  (transferGovernorStoredWord σ_evm I))
                (transferGovernorPostState
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I).accountMap := by
            unfold transferGovernorPostState
            rw [storageStore_accountMap]
            change accountMapEquiv
              (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
                (transferGovernorStoredWord σ_evm I))
              (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
                (transferGovernorStoredWord σ_solm I))
            rw [← hstored]
            exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩
              (transferGovernorStoredWord σ_evm I) hAccounts
          exact (cometRewardsX_transferGovernor_success (g := Sat256.ofUInt256 g)
              hperm hwv hsz36 hsize hhi hcanon hauth hreach)
            |>.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody hcreated
              hAccountsPost
              (returnEquiv.fallthrough rfl (by rfl) (by native_decide))
        · have hauthSolm :
              governorReturnWord σ_solm I ≠ solcSourceWord I := by
            intro hbad
            exact hauth (by
              rw [hretWord]
              exact hbad)
          have hbody :
              ExecTransitionBody config contract
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (transferGovernorStore I)
                transferGovernorTransition.body .reverted := by
            exact cometRewardsTransferGovernorBodyReverts_auth
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv)
              (by simp only [initState]; exact hhi)
              (by
                simpa [governorReturnWord, governorWord, initState, Solm.EVM.storageLoad,
                  State.lookupAccount] using hauthSolm)
          exact (cometRewardsX_transferGovernor_revert_auth (g := Sat256.ofUInt256 g)
              hwv hsz36 hsize hhi hcanon hauth hreach)
            |>.reEquivExecutionRevert hcode hd hdec hbody
      · have hdec := cometRewardsDecode_transferGovernor_none_noncanon
          (I := I) hsz36 hhi hcanon
        have hnc : UInt256.eq (transferGovernorNewGovernorWord I)
            (UInt256.land (transferGovernorNewGovernorWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne
            (fun he => hcanon (solcAddrCanonical_of_clean he))
        exact (cometRewardsTransferGovernorX_noncanon_newGovernor (g := Sat256.ofUInt256 g)
            hwv hsz36 hsize hhi hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbig : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := cometRewardsDecode_transferGovernor_none_huge (I := I) hbig
      exact (cometRewardsTransferGovernorX_hugearg (g := Sat256.ofUInt256 g)
          hwv hsize hbig hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 36 := by omega
    have hdec := cometRewardsDecode_transferGovernor_none_short (I := I) hsz4 hshort
    exact (cometRewardsTransferGovernorX_shortarg (g := Sat256.ofUInt256 g)
        hwv hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.CompoundIII.CometRewards
