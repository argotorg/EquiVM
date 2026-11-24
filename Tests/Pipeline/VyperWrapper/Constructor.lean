import Tests.Pipeline.VyperWrapper.CallHelpers
import Tests.Pipeline.VyperWrapper.CreationBlocks_001

variable {fork : Ethereum.Fork}

/-!
# Wrapper constructor correctness

The init code checks `callvalue` (pc 0, revert at 54), copies the `token` argument from the end
of the initcode and validates it as an address (pc 10), writes it after the runtime (offset 1780)
and returns the runtime followed by the immutable word (pc 27).  The Stele constructor is
`require(msg.value == 0); TOKEN = token;`; the deployment appends the ABI-encoded argument to the
creation code, so the argument is an address and the initcode tail is its word.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
open Reasoning.VyperImmutables

namespace Tests.Pipeline.VyperWrapper

set_option maxRecDepth 2000000

theorem ctorBody_eq : contract.ctor.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)), .setImmutable "TOKEN" (.var "token")] := by rfl

theorem ctorParams_eq : contract.ctor.params = [{ name := "token", ty := .elem .address }] := by rfl

/-- The constructor's final immutables. -/
abbrev ctorImms (t : AccountAddress) : Store := (initialImmutables contract).insert "TOKEN" (.address t)

theorem ctorImms_fit (t : AccountAddress) : immutablesFit contract (ctorImms t) := by
  intro d hd
  rw [show contract.immutables = [⟨"TOKEN", .address⟩] from rfl] at hd
  simp at hd
  subst hd
  exact ⟨.address t, store_get_self _ _ _, by simp [elemValueFits]⟩

/-- A deployment of the one-address constructor: the argument is an address and the initcode
carries its word. -/
theorem ctorDeploy {initcode deployed : ByteArray} {args : List Value}
    (hdeploy : genSolidityConstructorDeployment contract.ctor.params initcode args = some deployed) :
    ∃ t : AccountAddress, args = [.address t] ∧ deployed = initcode ++ (addrWord t).toByteArray := by
  rw [ctorParams_eq] at hdeploy
  rcases args with _ | ⟨v, _ | ⟨v2, rest⟩⟩
  · simp [genSolidityConstructorDeployment, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?] at hdeploy
  · cases v with
    | address t =>
      refine ⟨t, rfl, ?_⟩
      have henc : encodeABIValues? [.elem .address] [.address t] = some (EVM.Word.toBytesBE (addrWord t)) := by
        unfold encodeABIValues?
        rw [abiTupleHeadSize_scalarWords_eq (by decide)]
        simp only [bind, Option.bind]
        rw [encodeFrom_static_cons rfl (encodeABIValue_address t), encodeFrom_nil]
        simp
      simp only [genSolidityConstructorDeployment, List.map, bind, Option.bind, henc,
        word_toBytesBE_toByteArray_eq_toByteArray, Option.some.injEq] at hdeploy
      exact hdeploy.symm
    | _ => simp [genSolidityConstructorDeployment, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
        encodeABIValue?, encodeABIWord?] at hdeploy
  · simp [genSolidityConstructorDeployment, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?] at hdeploy

theorem addrWord_canon (t : AccountAddress) : (addrWord t).toNat < EVM.addressModulus := by
  rw [ulit_toNat' _ (lt_trans t.isLt (by decide))]; exact t.isLt

/-- The bytes the init code returns: the runtime (code offset 58, 1780 bytes) followed by the
`TOKEN` word. -/
theorem ctorOutput (t : AccountAddress) :
    ((wrapperCreationBytecode ++ (addrWord t).toByteArray).write 58
      ((addrWord t).toByteArray.write 0 ((addrWord t).toByteArray.write 0 (addrWord t).toByteArray 64 32) 1780 32)
      0 1780).readWithPadding 0 1812 = wrapperBytecode ++ (addrWord t).toByteArray := by
  have hcsize : wrapperCreationBytecode.size = 1838 := by native_decide
  have hrt : wrapperCreationBytecode.extract 58 (58 + 1780) = wrapperBytecode := by native_decide
  have hw32 : (addrWord t).toByteArray.size = 32 := toByteArray_size _
  have hb1 : (addrWord t).toByteArray.write 0 (addrWord t).toByteArray 64 32 =
      (addrWord t).toByteArray ++ ByteArray.zeroes 32 ++ (addrWord t).toByteArray := by
    rw [toByteArray_write_eq _ _ 64 (by rw [hw32]; omega) (by rw [hw32]; exact lt_usize _ (by decide)), hw32]
  have hb1s : ((addrWord t).toByteArray ++ ByteArray.zeroes 32 ++ (addrWord t).toByteArray).size = 96 := by
    rw [ByteArray.size_append, ByteArray.size_append, hw32, ByteArray_zeroes_size]
  have hb2 : (addrWord t).toByteArray.write 0 ((addrWord t).toByteArray ++ ByteArray.zeroes 32 ++ (addrWord t).toByteArray) 1780 32 =
      ((addrWord t).toByteArray ++ ByteArray.zeroes 32 ++ (addrWord t).toByteArray) ++ ByteArray.zeroes 1684 ++ (addrWord t).toByteArray := by
    rw [toByteArray_write_eq _ _ 1780 (by rw [hb1s]; omega) (by rw [hb1s]; exact lt_usize _ (by decide)), hb1s]
  have hb2s : (((addrWord t).toByteArray ++ ByteArray.zeroes 32 ++ (addrWord t).toByteArray) ++ ByteArray.zeroes 1684 ++
      (addrWord t).toByteArray).size = 1812 := by
    rw [ByteArray.size_append, ByteArray.size_append, hb1s, ByteArray_zeroes_size, hw32]
  have hempty : (((addrWord t).toByteArray ++ ByteArray.zeroes 32 ++ (addrWord t).toByteArray) ++ ByteArray.zeroes 1684 ++
      (addrWord t).toByteArray).extract 0 0 = ByteArray.empty :=
    byteArray_eq_empty_of_size_eq_zero _ (by rw [ByteArray.size_extract]; omega)
  have hwx : (addrWord t).toByteArray.extract 0 32 = (addrWord t).toByteArray := by
    have hx := byteArray_extract_self (addrWord t).toByteArray
    rw [hw32] at hx
    exact hx
  rw [hb1, hb2, write_eq_gen_from _ _ 58 0 1780 (by decide) (by rw [ByteArray.size_append, hcsize, hw32]; omega) (by rw [hb2s]; omega),
    extract_append_left wrapperCreationBytecode (addrWord t).toByteArray 58 (58 + 1780) (by rw [hcsize]), hrt, hempty,
    empty_append, hb2s, Nat.zero_add,
    extract_append_right_window _ _ _ _ (by rw [ByteArray.size_append, hb1s, ByteArray_zeroes_size]),
    ByteArray.size_append, hb1s, ByteArray_zeroes_size]
  simp only [show (1780 - (96 + 1684) : Nat) = 0 from rfl, show (1812 - (96 + 1684) : Nat) = 32 from rfl, hwx]
  have hfin : (wrapperBytecode ++ (addrWord t).toByteArray).size = 1812 := by
    rw [ByteArray.size_append, hw32]; native_decide
  rw [readWithPadding_eq_extract' _ _ _ (by norm_num) (by norm_num) (by rw [hfin]), Nat.zero_add, ← hfin]
  exact byteArray_extract_self _

theorem wrapperConstructorCorrect :
    typedConstructorRefinement config wrapperCreationBytecode contract (immutableLayout.deployed wrapperBytecode) := by
  intro fork _hfork σ σ₀ g A I args deployedInitcode hdeploy hcode hcalldata hperm
  have hdeploy' : genSolidityConstructorDeployment contract.ctor.params wrapperCreationBytecode args = some deployedInitcode :=
    hdeploy
  obtain ⟨t, hargs, hinit⟩ := ctorDeploy hdeploy'
  subst hargs
  have hcode' : I.code = wrapperCreationBytecode ++ (addrWord t).toByteArray := hcode.trans hinit
  have rd0 := RD.normalizePC (pc' := UInt256.ofNat 0)
    (RD.initState (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode') rfl
  have hcsize : wrapperCreationBytecode.size = 1838 := by native_decide
  have hw32 : (addrWord t).toByteArray.size = 32 := toByteArray_size _
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := wrapperCreationBlocks.wrapperCreation_block_0_fallthrough (by simp) (by rw [hwv]; rfl) rd0
    -- pc 10: the argument word copied from the initcode tail
    have hcopy : (wrapperCreationBytecode ++ (addrWord t).toByteArray).write (UInt256.ofNat 1838).toNat ByteArray.empty
        (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat = (addrWord t).toByteArray.write 0 ByteArray.empty 0 32 := by
      rw [ulit_toNat' 1838 (by decide), ulit_toNat' 32 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl]
      apply copy_word_bytes _ _ _ _ _ (by rw [ByteArray.size_append, hcsize, hw32]) hw32
      rw [readWithPadding_eq_extract' _ _ _ (by decide) (by decide) (by rw [ByteArray.size_append, hcsize, hw32]),
        extract_append_right_window _ _ _ _ (by rw [hcsize]), hcsize]
      simp only [Nat.sub_self, show (1838 + 32 - 1838 : Nat) = 32 from rfl]
      have hx := byteArray_extract_self (addrWord t).toByteArray
      rw [hw32] at hx
      exact hx
    have hw0 : (addrWord t).toByteArray.write 0 ByteArray.empty 0 32 = (addrWord t).toByteArray := by
      rw [toByteArray_write_eq _ _ 0 (Nat.zero_le _) (lt_usize _ (by decide)), empty_append,
        zeroes_zero (n := 0 - ByteArray.empty.size) (by rfl), empty_append]
    have hload0 : memLoad (⟨0⟩ : UInt256) ((addrWord t).toByteArray.write 0 ByteArray.empty 0 32) = addrWord t := by
      rw [show (⟨0⟩ : UInt256) = UInt256.ofNat 0 from by decide]
      exact memLoad_write_back _ _ 0 (by decide) (by show 0 - ByteArray.empty.size < USize.size; exact lt_usize _ (by decide))
    have rd2 := wrapperCreationBlocks.wrapperCreation_block_10_fallthrough (by simp)
      (by rw [hcopy, hload0]; exact u256_shiftRight160_zero_of_lt _ (addrWord_canon t)) rd1
    simp only [wrapperCreationBlocks.wrapperCreation_block_10_fallthrough_stack,
      wrapperCreationBlocks.wrapperCreation_block_10_fallthrough_memory] at rd2
    rw [hcopy, hload0, hw0] at rd2
    -- pc 27: the runtime copy and the return
    have rd3 := wrapperCreationBlocks.wrapperCreation_block_27 (by simp) rd2
    have hload64 : memLoad (UInt256.ofNat 64) ((addrWord t).toByteArray.write 0 (addrWord t).toByteArray 64 32) = addrWord t :=
      memLoad_write_back _ _ 64 (by decide) (by rw [hw32]; exact lt_usize _ (by decide))
    rw [ulit_toNat' 58 (by decide), ulit_toNat' 64 (by decide), ulit_toNat' 1780 (by decide), ulit_toNat' 0 (by decide),
      ulit_toNat' 1812 (by decide), hload64, ctorOutput t] at rd3
    -- Stele
    have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        ((∅ : Store).insert "token" (.address t)) contract.ctor.body
        (.returned { contract := contract, locals := (∅ : Store).insert "token" (.address t), immutables := ctorImms t }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) none) (initialImmutables contract) := by
      rw [ctorBody_eq]
      exact ExecFuncBody.execBlockOK (ExecBlock.consNormal
        (ExecStmt.requireTrue (evalCallvalueEq_true (by simpa [initState] using hwv)))
        (ExecBlock.consNormal (ExecStmt.setImmutable
          (by
            rw [evalExpr?]
            show EvalResult.ofOption _ (((∅ : Store).insert "token" (.address t)).get? "token") = _
            rw [store_get_self]; rfl)
          (by rfl) (by simp [elemValueFits])) ExecBlock.nil))
    rcases rd3 with hoog | ⟨s, hX, hacc⟩
    · exact typedConstructorRefinementFor.outOfGas
        (by simpa using Xi_error_of_X (by rw [← hcode'] at hoog; exact hoog))
    · have hxi := Xi_success_of_X (by rw [← hcode'] at hX; exact hX)
      rw [hacc] at hxi
      exact typedConstructorRefinementFor.execution (by simpa using hxi)
        (steleCtorExec.intro rfl (by rfl) (by rfl) hbody)
        (ctorResultEquiv.success rfl rfl rfl (by
          show wrapperBytecode ++ (addrWord t).toByteArray = immutableLayout.deployed wrapperBytecode (ctorImms t)
          rw [deployed_of_fit (ctorImms_fit t), suffixWords_TOKEN, wordsOf_TOKEN (store_get_self _ _ _)]
          rfl))
        (ctorImms_fit t)
  · have rd1 := wrapperCreationBlocks.wrapperCreation_block_0_taken (by simp) (fun h => hwv h)
      (by native_decide) rd0
    have rd2 := wrapperCreationBlocks.wrapperCreation_block_54 (by simp) rd1
    rcases rd2.xiResult hcode' with hoog | ⟨g', o, hxi⟩
    · exact typedConstructorRefinementFor.outOfGas (by simpa using hoog)
    · exact typedConstructorRefinementFor.execution (by simpa using hxi)
        (steleCtorExec.intro rfl (by rfl) (by rfl) (by
          rw [ctorBody_eq]
          exact ExecFuncBody.execBlockRevert (ExecBlock.consRevert
            (ExecStmt.requireFalse (evalCallvalueEq_false (by simpa [initState] using hwv))))))
        (ctorResultEquiv.revert rfl rfl) trivial

end Tests.Pipeline.VyperWrapper
