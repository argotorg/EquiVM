import Benchmarks.Dss.Dai.Dispatch
import Benchmarks.Dss.Dai.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Dai

/-! ## ABI decode and source-level body for `PERMIT_TYPEHASH()` -/

abbrev permitTypehashStore : Store :=
  ∅

abbrev permitTypehashWord : UInt256 :=
  ⟨0xea2aa0a1be11a07ed86d755c93467f4f82362b452371d1ba94d1715123511acb⟩

theorem permitTypehashBytes_eq_word :
    permitTypehashBytes = EVM.Word.toBytesBE permitTypehashWord := by
  native_decide

theorem daiDecode_permitTypehash_ok {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode
      (permitTypehashTransition.params.map Param.name)
      (transitionSignature permitTypehashTransition).paramTypes I.calldata =
        some permitTypehashStore := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata =
    some (∅ : Store)
  exact decodeCalldataWithMode_empty_ok hsz4

/-- The Solm `PERMIT_TYPEHASH()` body returns Maker's permit typehash constant. -/
theorem daiPermitTypehashBodyReturns (evm : EVM.State)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm permitTypehashStore permitTypehashTransition.body
      (.returned { contract := contract, locals := permitTypehashStore } evm
        (some [(.fixedBytes bytes32Width (EVM.Word.toBytesBE permitTypehashWord))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      unfold permitTypehashExpr
      rw [permitTypehashBytes_eq_word]
      simp [evalExpr?, pure])

/-! ## EVM trace -/

theorem daiX_permitTypehash_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨596⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret daiBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray permitTypehashWord) := by
  exact RD.daiWordConstGetterExternal
    (entry := ⟨596⟩) (returnPc := ⟨524⟩) (routine := ⟨1964⟩)
    (val := permitTypehashWord) (width := 32) (op := .PUSH32)
    hreach
    dai_getter_entry_wf
    dai_const_getter_wf
    (by jump_dest)
    (by jump_dest)
    dai_return_word_from_mem_wf

theorem daiPermitTypehashBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = daiBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some permitTypehashTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode
        (permitTypehashTransition.params.map Param.name)
        (transitionSignature permitTypehashTransition).paramTypes I.calldata =
          some permitTypehashStore)
    (hreach : ∃ k C, RD daiBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨596⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        permitTypehashStore
        permitTypehashTransition.body
        (.returned { contract := contract, locals := permitTypehashStore }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.fixedBytes bytes32Width (EVM.Word.toBytesBE permitTypehashWord))])) := by
    exact daiPermitTypehashBodyReturns
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (by simp only [initState]; exact hwv)
  exact (daiX_permitTypehash_ok (g := Sat256.ofUInt256 g) hreach)
    |>.reEquivExecutionTransport hcode hdispatch hdecode hbody (by rfl)
      hAccounts
      (returnEquiv_of_encode
        (by simpa [bytes32, bytes32Width] using
          bytes32ReturnEncoding permitTypehashWord))

/-- `PERMIT_TYPEHASH()` body refines its Solm transition. -/
theorem daiPermitTypehashBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (daiSelBytes 12))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (daiSelBytes 12) (by native_decide) hsel
  have hdispatch : dispatchMsg contract I.calldata = some permitTypehashTransition :=
    daiDispatchPermitTypehash hsel
  have hreach := daiReachPermitTypehashBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  exact daiPermitTypehashBodyCoreOk hcode hsize hwv hdispatch
    (daiDecode_permitTypehash_ok hsz4) hreach hAccounts

end Benchmarks.Dss.Dai
