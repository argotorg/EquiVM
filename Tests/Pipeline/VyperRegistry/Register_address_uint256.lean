import Tests.Pipeline.VyperRegistry.Register_address

variable {fork : Ethereum.Fork}

/-!
# Registry `register(address,uint256)`

Dispatcher bucket 7, arm entry pc 776: the 68-byte guard, `weight` from calldata word 2 into
memory offset 288 (pc 786), then the shared body (`registerTail`, from pc 793).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
  Reasoning.VyperBounded

namespace Tests.Pipeline.VyperRegistry

set_option maxRecDepth 2000000

abbrev rauStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "account" (.address (AccountAddress.ofNat (argWord I).toNat))).insert "weight"
    (uint256Value (argWord2 I))

theorem rauDecode_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size)
    (hcanon : (argWord I).toNat < EVM.addressModulus) :
    config.externalABI.decodeCalldata? (register_address_uint256Transition.params.map Param.name)
      (transitionSignature register_address_uint256Transition).paramTypes I.calldata = some (rauStore I) := by
  rw [argWord_eq] at hcanon
  simpa [config, contract, Syntax.contractSyntax, register_address_uint256Transition, rauStore, argWord_eq, argWord2_eq] using
    decodeCalldataWithMode_vyper_addr_uint256_ok (cd := I.calldata) (x := "account") (y := "weight") hsz68 hcanon

theorem rauDecode_short {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    config.externalABI.decodeCalldata? (register_address_uint256Transition.params.map Param.name)
      (transitionSignature register_address_uint256Transition).paramTypes I.calldata = none := by
  simpa [config, contract, Syntax.contractSyntax, register_address_uint256Transition] using
    decodeCalldataWithMode_vyper_addr_uint256_none_short (cd := I.calldata) (x := "account") (y := "weight") hsz hshort

theorem rauDecode_noncanon {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size)
    (hnc : ¬ (argWord I).toNat < EVM.addressModulus) :
    config.externalABI.decodeCalldata? (register_address_uint256Transition.params.map Param.name)
      (transitionSignature register_address_uint256Transition).paramTypes I.calldata = none := by
  rw [argWord_eq] at hnc
  simpa [config, contract, Syntax.contractSyntax, register_address_uint256Transition] using
    decodeCalldataWithMode_vyper_addr_uint256_none_noncanon (cd := I.calldata) (x := "account") (y := "weight") hsz68 hnc

/-- `register(address,uint256)`: the theorem `Correct.lean` routes selector 3 to. -/
theorem registryRegister_address_uint256Body {σ σ₀ A I} {g : UInt256} (hwf : storageWF σ I)
    (hcode : I.code = registryBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (registrySelBytes 3)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (registrySelBytes 3) rfl hsel
  obtain ⟨_, _, rd⟩ := registryReachRegister_address_uint256Body (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  have hd : dispatchMsg contract I.calldata = some register_address_uint256Transition :=
    registryDispatch_register_address_uint256 (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel) hsel
  by_cases hshort : I.calldata.size < 68
  · have rd1 := registryBlocks.registry_block_776_taken (by simp) (guard68_short hsize hshort) (by jump_dest) rd
    have rd2 := registryBlocks.registry_block_1661 (by simp) rd1
    exact RDrev.reEquivDecodingFailed hcode rd2 hd (rauDecode_short hsz hshort)
  have hsz68 : 68 ≤ I.calldata.size := by omega
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · have rd1 := registryBlocks.registry_block_776_taken (by simp) (guard_wv hwv) (by jump_dest) rd
    have rd2 := registryBlocks.registry_block_1661 (by simp) rd1
    exact RDrev.reEquivOfDispatch hcode hd
      (fun _ => by rw [register_address_uint256Body_eq]; exact bodyReverts_nonPayable (by simpa [initState] using hwv)) rd2
  have rd1 := registryBlocks.registry_block_776_fallthrough (by simp) (guard68_ok hwv hsz68 hsize) rd
  have rd2 := registryBlocks.registry_block_786 (by simp) rd1
  simp only [registryBlocks.registry_block_786_memory, ulit_toNat' 288 (by decide)] at rd2
  by_cases hcanon : (argWord I).toNat < EVM.addressModulus
  swap
  · have rd3 := registryBlocks.registry_block_793_taken (by simp)
      (by intro h; exact hcanon (u256_lt_addressModulus_of_shiftRight160_zero _ h)) (by jump_dest) rd2
    have rd4 := registryBlocks.registry_block_1661 (by simp [registryBlocks.registry_block_793_taken_stack]) rd3
    exact RDrev.reEquivDecodingFailed hcode rd4 hd (rauDecode_noncanon hsz68 hcanon)
  have rd3 := registryBlocks.registry_block_793_fallthrough (by simp) (u256_shiftRight160_zero_of_lt _ hcanon) rd2
  simp only [registryBlocks.registry_block_793_fallthrough_stack] at rd3
  have hcv : evalExpr? config (frame (rauStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) :=
    evalCallvalueEq_true (by simpa [initState] using hwv)
  refine registerTail hwf hcode 7 (by decide) (argWord2 I) rd3 hcanon register_address_uint256Transition hd (rauStore I)
    (rauDecode_ok hsz68 hcanon) rfl (rauStore I)
    (by rw [store_get_ne _ _ (by decide), store_get_self]) (store_get_self _ _ _) (by simp) (by simp) (by simp) (by simp) ?_
  intro result h
  rw [register_address_uint256Body_eq]
  exact ExecBlock.consNormal (ExecStmt.requireTrue hcv) h

end Tests.Pipeline.VyperRegistry
