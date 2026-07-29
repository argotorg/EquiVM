import Benchmarks.Dss.Dai.Dispatch
import Benchmarks.Dss.Dai.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Dai

/-! ## ABI decode and source-level body for `totalSupply()` -/

abbrev totalSupplyStore : Store :=
  ∅

abbrev totalSupplyStorageSlot : UInt256 :=
  ⟨1⟩

def totalSupplyWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD totalSupplyStorageSlot ⟨0⟩)

theorem daiDecode_totalSupply_ok {I : ExecutionEnv} (hsz4 : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (totalSupplyTransition.params.map Param.name)
      (transitionSignature totalSupplyTransition).paramTypes I.calldata =
        some totalSupplyStore := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata =
    some (∅ : Store)
  exact decodeCalldataWithMode_empty_ok hsz4

/-- The Solm `totalSupply()` body returns the scalar storage slot `1`. -/
theorem daiTotalSupplyBodyReturns (evm : EVM.State)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm totalSupplyStore totalSupplyTransition.body
      (.returned { contract := contract, locals := totalSupplyStore } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            totalSupplyStorageSlot).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := totalSupplyStore })
        (slot := totalSupplyRef)
        (er := ({ base := "totalSupply", steps := [] } : EvaledStorageRef))
        (t := .int uint256Int)
        (loc := wordLoc totalSupplyStorageSlot (.int uint256Int))
        (value := .int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            totalSupplyStorageSlot).toNat))
        (hbase := by
          simp [totalSupplyStore, totalSupplyRef])
        (her := by
          simp [evalStorageRef, totalSupplyRef, totalSupplyStore, EvalResult.bind, bind, pure])
        (hty := by
          simp [storageTypeAt?, contract, storageDecls, uint256St])
        (hloc := by rfl)
        (hload := by
          simpa [wordLoc, uint256Loc, uint256Int] using
            storageLocLoad_uint256 evm totalSupplyStorageSlot)])

/-! ## EVM trace -/

theorem daiX_totalSupply_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨516⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret daiBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (totalSupplyWord σ I)) := by
  exact RD.daiWordGetterExternal
    (entry := ⟨516⟩) (returnPc := ⟨524⟩) (routine := ⟨1405⟩)
    (slot := totalSupplyStorageSlot)
    hreach
    dai_getter_entry_wf
    dai_word_slot_getter_wf
    (by jump_dest)
    (by jump_dest)
    dai_return_word_from_mem_wf

theorem daiTotalSupplyBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = daiBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some totalSupplyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (totalSupplyTransition.params.map Param.name)
        (transitionSignature totalSupplyTransition).paramTypes I.calldata =
          some totalSupplyStore)
    (hreach : ∃ k C, RD daiBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨516⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : totalSupplyWord σ_evm I = totalSupplyWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner totalSupplyStorageSlot ⟨0⟩
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        totalSupplyStore
        totalSupplyTransition.body
        (.returned { contract := contract, locals := totalSupplyStore }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (totalSupplyWord σ_solm I).toNat))])) := by
    simpa [totalSupplyWord, totalSupplyStorageSlot, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      daiTotalSupplyBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (by simp only [initState]; exact hwv)
  exact (daiX_totalSupply_ok (g := Sat256.ofUInt256 g) hreach)
    |>.reEquivExecutionTransport hcode hdispatch hdecode hbody (by rw [← hword])
      hAccounts
      (returnEquiv_of_encode
        (by simpa [uint256] using uint256ReturnEncoding (totalSupplyWord σ_evm I)))

/-- `totalSupply()` body refines its Solm transition. -/
theorem daiTotalSupplyBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (daiSelBytes 17))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (daiSelBytes 17) (by native_decide) hsel
  have hdispatch : dispatchMsg contract I.calldata = some totalSupplyTransition :=
    daiDispatchTotalSupply hsel
  have hreach := daiReachTotalSupplyBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  exact daiTotalSupplyBodyCoreOk hcode hsize hwv hdispatch
    (daiDecode_totalSupply_ok hsz4) hreach hAccounts

end Benchmarks.Dss.Dai
