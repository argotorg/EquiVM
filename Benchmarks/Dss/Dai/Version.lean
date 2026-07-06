import Benchmarks.Dss.Dai.StringReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Dai

/-! ## `version()` dynamic string getter -/

abbrev versionStore : Store :=
  ∅

abbrev daiVersionLen : UInt256 :=
  ⟨1⟩

def daiVersionReturnBytes : ByteArray :=
  (encodeReturnValue? stringTy (.bytes daiVersionBytes)).getD ByteArray.empty

theorem daiVersionReturnEncoding :
    encodeReturnValue? stringTy (.bytes daiVersionBytes) = some daiVersionReturnBytes := by
  native_decide

/-- The Solm `version()` body returns `"1"` as a dynamic string value. -/
theorem daiVersionBodyReturns (evm : EVM.State)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm versionStore versionTransition.body
      (.returned { contract := contract, locals := versionStore } evm
        (some [.bytes daiVersionBytes])) := by
  simpa [versionTransition, versionStore, daiVersionBytes] using
    daiBytesLiteralBodyReturns evm versionStore daiVersionBytes h

private def daiVersionRawWord : UInt256 :=
  ⟨0x31⟩

private def daiVersionLiteralWord : UInt256 :=
  UInt256.shiftLeft daiVersionRawWord ⟨248⟩

private theorem daiVersionReturnRead :
    (daiStringAbiMem3 daiVersionLen daiVersionLiteralWord).readWithPadding 192 96 =
      daiVersionReturnBytes := by
  native_decide

/-- Runtime-only `version()` slice from selector dispatch through dynamic string return. -/
theorem daiX_version_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨688⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret daiBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      daiVersionReturnBytes := by
  obtain ⟨_, _, h688⟩ := hreach
  have h2245 := evm_run h688 with [
    jumpdest, push2 ⟨335⟩, push2 ⟨2245⟩, jump (by jump_dest)]
  have h2255 := evm_run h2245 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    dup1, push1 ⟨64⟩, add, push1 ⟨64⟩]
  have h2256 := evm_run h2255 with [
    raw mstore 0 daiStringObjectMem0 (UInt256.ofNat 3) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov)]
  have h2260 := evm_run h2256 with [dup1, push1 daiVersionLen, dup2]
  have h2261 := evm_run h2260 with [
    raw mstore 6 (daiStringObjectMem1 daiVersionLen) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by native_decide) (by decide) (by evm_ov)]
  have h2264 := evm_run h2261 with [push1 ⟨32⟩, add]
  have h2266 := h2264.pushConst daiVersionRawWord
    (width := 1) (op := .PUSH1) (by decide) (by native_decide) (by evm_ov)
  have h2270 := evm_run h2266 with [push1 ⟨248⟩, shl, dup2]
  have h2271 := evm_run h2270 with [
    raw mstore 3 (daiStringObjectMem daiVersionLen daiVersionLiteralWord)
      (UInt256.ofNat 6) (by native_decide) mem_cost
      (by native_decide) (by decide) (by evm_ov)]
  have h335 := evm_run h2271 with [pop, dup2, jump (by jump_dest)]
  have h344 := evm_run h335 with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    push1 ⟨32⟩, dup1, dup3,
    raw mstore 3 (daiStringAbiMem0 daiVersionLen daiVersionLiteralWord)
      (UInt256.ofNat 7) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov)]
  have h350 := evm_run h344 with [
    dup4,
    raw mload 0 daiVersionLen (UInt256.ofNat 7) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    dup2, dup4, add,
    raw mstore 3 (daiStringAbiMem1 daiVersionLen daiVersionLiteralWord)
      (UInt256.ofNat 8) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov)]
  have h367 := evm_run h350 with [
    dup4,
    raw mload 0 daiVersionLen (UInt256.ofNat 8) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    swap2, swap3, dup4, swap3, swap1, dup4, add, swap2, dup6, add, swap1,
    dup1, dup4, dup4, push1 ⟨0⟩]
  have h378 := evm_run h367 with [
    jumpdest, dup4, dup2, lt, iszero, push2 ⟨393⟩, jumpiNT (by decide)]
  have h393a := evm_run h378 with [
    dup2, dup2, add,
    raw mload 0 daiVersionLiteralWord (UInt256.ofNat 8) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    dup4, dup3, add,
    raw mstore 3 (daiStringAbiMem2 daiVersionLen daiVersionLiteralWord)
      (UInt256.ofNat 9) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨369⟩, jump (by jump_dest)]
  have h393 := evm_run h393a with [
    jumpdest, dup4, dup2, lt, iszero, push2 ⟨393⟩, jumpiT (by decide) (by jump_dest)]
  have h413 := evm_run h393 with [
    jumpdest, pop, pop, pop, pop, swap1, pop, swap1, dup2, add, swap1,
    push1 ⟨31⟩, and, dup1, iszero, push2 ⟨438⟩, jumpiNT (by decide)]
  have h438 := evm_run h413 with [
    dup1, dup3, sub, dup1,
    raw mload 0 daiVersionLiteralWord (UInt256.ofNat 9) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    push1 ⟨1⟩, dup4, push1 ⟨32⟩, sub, push2 ⟨256⟩, exp, sub, not, and, dup2,
    raw mstore 0 (daiStringAbiMem3 daiVersionLen daiVersionLiteralWord)
      (UInt256.ofNat 9) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, swap2, pop]
  have h451 := evm_run h438 with [
    jumpdest, pop, swap3, pop, pop, pop, push1 ⟨64⟩,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  exact evm_run h451 with [
    raw ret 0 daiVersionReturnBytes (by native_decide)
      mem_cost daiVersionReturnRead (by evm_ov)]

theorem daiVersionBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = daiBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some versionTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (versionTransition.params.map Param.name)
        (transitionSignature versionTransition).paramTypes I.calldata =
          some versionStore)
    (hreach : ∃ k C, RD daiBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨688⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        versionStore
        versionTransition.body
        (.returned { contract := contract, locals := versionStore }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [.bytes daiVersionBytes])) := by
    exact daiVersionBodyReturns
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (by simp only [initState]; exact hwv)
  exact (daiX_version_ok (g := Sat256.ofUInt256 g) hreach)
    |>.reEquivExecutionTransport hcode hdispatch hdecode hbody rfl
      hAccounts
      (by
        rw [versionTransition]
        exact returnEquiv_of_encode daiVersionReturnEncoding)

theorem daiDecode_version_ok {I : ExecutionEnv} (hsz4 : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (versionTransition.params.map Param.name)
      (transitionSignature versionTransition).paramTypes I.calldata =
        some versionStore := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata =
    some (∅ : Store)
  exact decodeCalldataWithMode_empty_ok hsz4

/-- `version()` body refines its Solm transition. -/
theorem daiVersionBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (daiSelBytes 20))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (daiSelBytes 20) (by native_decide) hsel
  have hdispatch : dispatchMsg contract I.calldata = some versionTransition :=
    daiDispatchVersion hsel
  have hreach := daiReachVersionBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  exact daiVersionBodyCoreOk hcode hsize hwv hdispatch
    (daiDecode_version_ok hsz4) hreach hAccounts

end Benchmarks.Dss.Dai
