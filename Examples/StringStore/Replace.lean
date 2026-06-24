import Examples.StringStore.Getters

/-!
# StringStore — `replaceFromHistory(uint256)` branch scaffolding
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace StringStore

theorem stringStoreDispatch_replaceFromHistory {cd : ByteArray}
    (hsel : ((⟨#[0x0f, 0x76, 0xd8, 0xb4]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg stringStoreContract cd = some replaceFromHistoryTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x0f, 0x76, 0xd8, 0xb4]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [setTransition, appendToHistoryTransition])
    (post := [dropLastTransition, clearCurrentTransition, clearAllTransition,
      storeRawTransition, currentLengthGetter, historyLengthGetter, rawLengthGetter]) rfl ?_
    (by rw [selectorOf, replaceFromHistorySelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · rw [selectorOf, setSelectorBytes, hcd]; decide
  · rw [selectorOf, appendToHistorySelectorBytes, hcd]; decide

theorem stringStoreReachReplaceFromHistory {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x0f, 0x76, 0xd8, 0xb4]⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨160⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  have hmatches := stringStoreLowMatches 0 (by omega) hsz hsel
  exact stringStoreReachLowBody 0 (by omega) ⟨160⟩ hcode hwv hsz hsize
    (stringStorePivotTaken 0 (by omega) hsz hsel)
    hmatches.1 hmatches.2 (by jump_dest) (by decide)

theorem stringStoreReachReplaceFromHistoryDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x0f, 0x76, 0xd8, 0xb4]⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2465⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨181⟩, ⟨186⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨k0, C0, hreach⟩ := stringStoreReachReplaceFromHistory
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz hsize hsel
  have hsizeWord :
      (⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ =
        UInt256.ofNat I.calldata.size := by
    exact uadd_lit_usub_ofNat_lit hsz hsize
  exact ⟨_, _, by
    simpa [hsizeWord] using
      (evm_run hreach with [
        jumpdest, push2 ⟨186⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
        push2 ⟨181⟩, swap2, swap1, push2 ⟨2465⟩,
        jump (by jump_dest) ])⟩

theorem stringStoreX_replaceFromHistoryDecoderHeadShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x0f, 0x76, 0xd8, 0xb4]⟩)
    (hshort : I.calldata.size < 36) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k0, C0, hdec⟩ := stringStoreReachReplaceFromHistoryDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz hshort hsize
  exact evm_run hdec with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨2486⟩,
    jumpiNT (by rw [hslt]; decide),
    push2 ⟨2485⟩, push2 ⟨2406⟩,
    jump (by jump_dest),
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem stringStoreX_replaceFromHistoryDecoderHeadHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x0f, 0x76, 0xd8, 0xb4]⟩)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k0, C0, hdec⟩ := stringStoreReachReplaceFromHistoryDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  exact evm_run hdec with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨2486⟩,
    jumpiNT (by rw [hslt]; decide),
    push2 ⟨2485⟩, push2 ⟨2406⟩,
    jump (by jump_dest),
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem decodeCalldata_replaceFromHistory_none_headShort {I : ExecutionEnv}
    (hshort : I.calldata.size < 36) :
    decodeCalldata (replaceFromHistoryTransition.params.map Param.name)
      (transitionSignature replaceFromHistoryTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["index"] [uint256] I.calldata = none
  simpa [uint256, uint256Int, abiUInt256] using
    (decodeCalldata_uint256_none_short (cd := I.calldata) (x := "index") hshort)

theorem decodeCalldata_replaceFromHistory_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (replaceFromHistoryTransition.params.map Param.name)
      (transitionSignature replaceFromHistoryTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["index"] [uint256] I.calldata = none
  simpa [uint256, uint256Int, abiUInt256] using
    (decodeCalldata_uint256_none_huge (cd := I.calldata) (x := "index") hbig)

theorem stringStoreReplaceFromHistoryHeadShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0f, 0x76, 0xd8, 0xb4]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x0f, 0x76, 0xd8, 0xb4]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := stringStoreDispatch_replaceFromHistory (cd := I.calldata) hsel'
  have hdec := decodeCalldata_replaceFromHistory_none_headShort (I := I) hshort
  have hrev := stringStoreX_replaceFromHistoryDecoderHeadShort
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel hshort
  exact hrev.reEquivElim hcode fun _ _ hrun => by
    exact reEquiv_decodingFailed hd hdec hrun

theorem stringStoreReplaceFromHistoryHeadHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0f, 0x76, 0xd8, 0xb4]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz : 4 ≤ I.calldata.size) (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x0f, 0x76, 0xd8, 0xb4]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := stringStoreDispatch_replaceFromHistory (cd := I.calldata) hsel'
  have hdec := decodeCalldata_replaceFromHistory_none_huge (I := I) hbig
  have hrev := stringStoreX_replaceFromHistoryDecoderHeadHuge
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel hbig
  exact hrev.reEquivElim hcode fun _ _ hrun => by
    exact reEquiv_decodingFailed hd hdec hrun

theorem replaceFromHistoryBodyReturns
    {evm evmCurrent evmRaw : EVM.State} {index : Int} {copy : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hread :
      evalExpr? stringStoreConfig
        { contract := stringStoreContract
          locals := (∅ : Store).insert "index" (.int index) }
        evm (.storage (historyElemRef (.var "index"))) = .ok (.bytes copy))
    (hassignCurrent :
      assignStorageRef? stringStoreConfig
        { contract := stringStoreContract
          locals := ((∅ : Store).insert "index" (.int index)).insert "copy" (.bytes copy) }
        evm .storage currentRef (.bytes copy) =
          .ok ({ contract := stringStoreContract
                 locals := ((∅ : Store).insert "index" (.int index)).insert "copy" (.bytes copy) },
              evmCurrent))
    (hassignRaw :
      assignStorageRef? stringStoreConfig
        { contract := stringStoreContract
          locals := ((∅ : Store).insert "index" (.int index)).insert "copy" (.bytes copy) }
        evmCurrent .storage rawRef (.bytes copy) =
          .ok ({ contract := stringStoreContract
                 locals := ((∅ : Store).insert "index" (.int index)).insert "copy" (.bytes copy) },
              evmRaw)) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm
      ((∅ : Store).insert "index" (.int index)) replaceFromHistoryTransition.body
      (.returned
        { contract := stringStoreContract
          locals := ((∅ : Store).insert "index" (.int index)).insert "copy" (.bytes copy) }
        evmRaw (some (.int copy.size))) := by
  let locals0 : Store := (∅ : Store).insert "index" (.int index)
  let locals1 : Store := locals0.insert "copy" (.bytes copy)
  let solm0 : Frame := { contract := stringStoreContract, locals := locals0 }
  let solm1 : Frame := { contract := stringStoreContract, locals := locals1 }
  have hcopy : evalExpr? stringStoreConfig solm1 evm (.var "copy") = .ok (.bytes copy) := by
    simp [solm1, locals1, locals0, evalExpr?, EvalResult.ofOption]
  have hcopyRaw : evalExpr? stringStoreConfig solm1 evmCurrent (.var "copy") = .ok (.bytes copy) := by
    simp [solm1, locals1, locals0, evalExpr?, EvalResult.ofOption]
  have hret :
      evalExpr? stringStoreConfig solm1 evmRaw (.arrayLength .localVar { base := "copy" }) =
        .ok (.int copy.size) := by
    simp [solm1, locals1, locals0, evalExpr?, readLocalPath?, EvalResult.bind, bind, pure]
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.letDecl (by simpa [solm0, locals0] using hread)) <|
        ExecBlock.consNormal (ExecStmt.assign hcopy (by simpa [solm1, locals1, locals0] using hassignCurrent)) <|
          ExecBlock.consNormal (ExecStmt.assign hcopyRaw (by simpa [solm1, locals1, locals0] using hassignRaw)) <|
            ExecBlock.consReturn (ExecStmt.return hret)

end StringStore
