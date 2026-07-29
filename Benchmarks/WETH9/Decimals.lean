import Benchmarks.WETH9.Routines

/-!
# WETH9 `decimals()` refinement

`decimals` is a public non-payable uint8 getter reading storage slot 2 (masked with `0xff`).
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.WETH9

/-- The uint8 `decimals` value = low byte of storage slot 2. -/
def decimalsWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨2⟩ ⟨0⟩)) ⟨255⟩

theorem land255_double (x : UInt256) :
    UInt256.land (UInt256.land ⟨255⟩ x) ⟨255⟩ = UInt256.land x ⟨255⟩ := by
  apply u256_inj
  have h255 : (⟨255⟩ : UInt256).toNat = 255 := by decide
  rw [uland_toNat, uland_toNat, uland_toNat, h255]
  rw [Nat.and_comm 255 x.toNat, Nat.and_assoc, Nat.and_self]

theorem decimalsWord_lt (σ : AccountMap) (I : ExecutionEnv) :
    (decimalsWord σ I).toNat < EVM.twoPow 8 := by
  unfold decimalsWord
  rw [uland_toNat]
  have h255 : (⟨255⟩ : UInt256).toNat = 255 := by decide
  rw [h255, show EVM.twoPow 8 = 256 from by decide]
  exact lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem weth9SelectorDispatchDecimals {I : ExecutionEnv} (hsel : selIs I (weth9SelBytes 5)) :
    selectorDispatchMsg contract I.calldata = some decimalsTransition := by
  have hcd : I.calldata.extract 0 4 = weth9SelBytes 5 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp only [contract, dispatchList, selectorOf, hcd,
    weth9NameSelectorBytes, weth9ApproveSelectorBytes, weth9TotalSupplySelectorBytes,
    weth9TransferFromSelectorBytes, weth9WithdrawSelectorBytes, weth9DecimalsSelectorBytes]
  native_decide

theorem weth9Decode_decimals_ok {I : ExecutionEnv} (hsz4 : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (decimalsTransition.params.map Param.name)
      (transitionSignature decimalsTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some (∅ : Store)
  exact decodeCalldataWithMode_empty_ok hsz4

/-- The Solm `decimals()` body returns the low byte of slot 2. -/
theorem weth9DecimalsBodyReturns (evm : EVM.State)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm ∅ decimalsTransition.body
      (.returned { contract := contract, locals := ∅ } evm
        (some [(.int (Int.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩) ⟨255⟩).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := ∅ })
        (slot := decimalsRef)
        (er := ({ base := "decimals", steps := [] } : EvaledStorageRef))
        (t := .int uint8Int)
        (loc := uint8Loc ⟨2⟩)
        (value := .int (Int.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩) ⟨255⟩).toNat))
        (hbase := by simp [decimalsRef])
        (her := by simp [evalStorageRef, evalStorageRefStep, decimalsRef, EvalResult.bind,
          EvalResult.ofOption, bind, pure])
        (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint8St, uint8Int])
        (hloc := by rfl)
        (hload := by
          simp only [uint8Loc, uint8Int]
          rw [storageLocLoad_uint_offset0 evm ⟨2⟩ 1 ⟨8, by decide⟩ (by decide)]
          rfl)])

/-! ## EVM trace -/

theorem weth9DecimalsReturnWf : solcReturnUint8FromMemWf weth9Bytecode ⟨550⟩ := by
  dsimp [solcReturnUint8FromMemWf]; repeat' first | apply And.intro | native_decide

/-- The uint8 return-encoder tail at pc 550, parameterised over the raw slot word `w` (kept a
    variable so the `land` reconciliation stays symbolic and cheap). -/
theorem weth9DecimalsReturn {cA gh bl σ σ₀ A I} {g : Sat256} {w : UInt256} {k C : ℕ}
    (h : RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨550⟩
      [UInt256.land ⟨255⟩ w, ⟨550⟩, weth9SelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDret weth9Bytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.land w ⟨255⟩)) := by
  have hthis := RD.solcReturnUint8FromMem h weth9DecimalsReturnWf solcFreePtrMem_mload64 rfl
    (solcReturnMem_mload64 (UInt256.land (UInt256.land ⟨255⟩ w) ⟨255⟩))
    (solcReturnMem_read128 (UInt256.land (UInt256.land ⟨255⟩ w) ⟨255⟩))
    (by simp only [List.length_singleton]; omega)
  rwa [land255_double] at hthis

set_option maxHeartbeats 4000000 in
theorem weth9DecimalsX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 5)) :
    RDret weth9Bytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (decimalsWord σ I)) := by
  obtain ⟨_, _, h529⟩ := weth9ReachDecimals (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h543⟩ := weth9GuardPeelOk (gt := ⟨541⟩) h529 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
  have h1544 := h543.push2 ⟨550⟩ (by native_decide) (by simp)
    |>.push2 ⟨1544⟩ (by native_decide) (by simp)
    |>.jump (by native_decide) (by jump_dest) (by simp)
  have h1545 := h1544.jumpdest (by native_decide) (by simp)
    |>.push1 ⟨2⟩ (by native_decide) (by simp)
  obtain ⟨_, _, h1548⟩ := h1545.sload (by native_decide) (by simp)
  have h550 := h1548.push1 ⟨255⟩ (by native_decide) (by simp)
    |>.and (by native_decide) (by simp)
    |>.dup2 (by native_decide) (by simp)
    |>.jump (by native_decide) (by jump_dest) (by simp)
  unfold decimalsWord
  exact weth9DecimalsReturn h550

/-! ## Refinement -/

theorem weth9DecimalsBodyCoreOk {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = weth9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (weth9SelBytes 5))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (weth9SelBytes 5) (by native_decide) hsel
  have hword : decimalsWord σ_evm I = decimalsWord σ_solm I := by
    unfold decimalsWord
    rw [accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩]
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ decimalsTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (decimalsWord σ_solm I).toNat))])) := by
    have hb := weth9DecimalsBodyReturns (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (by simp only [initState]; exact hwv)
    simpa [decimalsWord, Solm.EVM.storageLoad, State.lookupAccount, initState] using hb
  exact weth9ReEquivExecTransport hcode
    (weth9DecimalsX_ok (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    (weth9SelectorDispatchDecimals hsel) (weth9Decode_decimals_ok hsz4) hbody (by rw [← hword])
    hAccounts
    (returnEquiv_of_encode
      (by simpa [uint8, uint8Int] using
        uint8ReturnEncoding (decimalsWord σ_evm I) (decimalsWord_lt σ_evm I)))

theorem weth9DecimalsBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = weth9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I (weth9SelBytes 5))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · exact weth9DecimalsBodyCoreOk hcode hsize hwv hsel hAccounts
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (weth9SelBytes 5) (by native_decide) hsel
    obtain ⟨_, _, h529⟩ := weth9ReachDecimals (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
    have hrev := weth9GuardPeelRev (gt := ⟨541⟩) h529 hwv
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    exact weth9NonpayableRevert hcode hrev (weth9SelectorDispatchDecimals hsel)
      (fun callargs _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end Benchmarks.WETH9
