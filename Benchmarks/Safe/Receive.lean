import Benchmarks.Safe.Routines

/-! # Safe receive refinement -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Safe

abbrev safeReceiveEventTopic : UInt256 :=
  ⟨27613899205238800472750487981127851187820584748339481801398827578897088740413⟩

theorem safeReceiveDispatch {I : ExecutionEnv} (hcalldata : I.calldata.size = 0) :
    receiveDispatchMsg contract I.calldata = some receiveTransition := by
  simp [receiveDispatchMsg, contract, hcalldata]

theorem safeReceiveBodyReturns {cA gh bl σ σ₀ A I} {g : Sat256} :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) ∅
      receiveTransition.body
      (.returned { contract := contract, locals := ∅ } (initState cA gh bl σ σ₀ g A I)
        none) := by
  simpa [ExecTransitionBody, receiveTransition] using
    (ExecFuncBody.execBlockOK
      (cfg := config)
      (solm := { contract := contract, locals := ∅ })
      (evm := initState cA gh bl σ σ₀ g A I)
      (body := [])
      ExecBlock.nil)

theorem safeReceiveX {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode)
    (hperm : I.perm = true)
    (hcalldata : I.calldata.size = 0) :
    RDret safeBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ) ByteArray.empty := by
  have hshort : I.calldata.size < 4 := by rw [hcalldata]; decide
  have hzero : UInt256.ofNat I.calldata.size = (⟨0⟩ : UInt256) := by
    rw [hcalldata]; decide
  have h5 := evm_run
      (RD.initState (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcode)
      with [
        push1 ⟨128⟩,
        push1 ⟨64⟩,
        raw mstore 9 solcFreePtrMem (UInt256.ofNat 3) (by native_decide)
          mem_cost (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
          (by decide) (by evm_ov)]
  have h11 := evm_run h5 with [
    push1 ⟨4⟩,
    calldatasize,
    lt]
  have h475 := (h11.pushConst (⟨475⟩ : UInt256) (op := .PUSH2) (width := 2)
      (by decide) (by native_decide) (by evm_ov))
    |>.jumpiT (by native_decide) (lt_four_ne_zero_of_lt hshort) (by native_decide)
      (by decide)
  have h477 := evm_run h475 with [
    jumpdest,
    calldatasize]
  have h481 := (h477.pushConst (⟨535⟩ : UInt256) (op := .PUSH2) (width := 2)
      (by decide) (by native_decide) (by evm_ov))
    |>.jumpiNT (by native_decide) hzero (by evm_ov)
  have h488 := evm_run h481 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    callvalue,
    dup2,
    raw mstore 6 (solcReturnMem I.weiValue) (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    caller,
    swap1]
  have h522 := h488.pushConst safeReceiveEventTopic (op := .PUSH32) (width := 32)
    (by decide) (by native_decide) (by evm_ov)
  have h533 := evm_run h522 with [
    swap1,
    push1 ⟨32⟩,
    add,
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost (solcReturnMem_mload64 I.weiValue) (by decide) (by evm_ov),
    dup1,
    swap2,
    sub,
    swap1]
  have h534 := _root_.Benchmarks.Safe.RD.log2 0 (UInt256.ofNat 5) h533 (by native_decide) hperm
    mem_cost (by native_decide) (by simp)
  exact h534.stop (by native_decide) (by evm_ov)

theorem safeReEquivReceiveExec {cfg : Config} {contract : ContractDecl}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256} {o : ByteArray}
    (hcode : I.code = safeBytecode)
    (h : RDret safeBytecode g (initState cA gh bl σ_evm σ₀ g A I) (cA, σ_evm) o)
    (hreceive : receiveDispatchMsg contract I.calldata = some receiveTransition)
    (hbody : ExecTransitionBody cfg contract
              (initState cA gh bl σ_solm σ₀ g A I) ∅ receiveTransition.body
              (.returned { contract := contract, locals := ∅ }
                (initState cA gh bl σ_solm σ₀ g A I) none))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (henc : returnEquiv o none []) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀ g.toUInt256 A I := by
  refine RDret.reEquivElim (cfg := cfg) (contract := contract) hcode h ?_
  intro g' A' hxi
  have hbody' :
      ExecTransitionBody cfg contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g.toUInt256) A I) ∅
        receiveTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g.toUInt256) A I) none) := by
    simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hbody
  exact reEquiv_receiveExecution hreceive rfl rfl hbody'
    (execResultsEquiv.success hxi rfl rfl hAccounts (.abi henc))

theorem safeReceiveBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode)
    (_hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hcalldata : I.calldata.size = 0)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact safeReEquivReceiveExec hcode
    (safeReceiveX (g := Sat256.ofUInt256 g) hcode hperm hcalldata)
    (safeReceiveDispatch hcalldata) safeReceiveBodyReturns hAccounts
    (returnEquiv.fallthrough (dvs := []) rfl rfl (by native_decide))

end Benchmarks.Safe
