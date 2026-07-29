import Benchmarks.Dss.Dai.StringReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Dai

/-! ## `name()` dynamic string getter -/

abbrev nameStore : Store :=
  ∅

abbrev daiNameLen : UInt256 :=
  ⟨14⟩

def daiNameReturnBytes : ByteArray :=
  (encodeReturnValue? stringTy (.bytes daiNameBytes)).getD ByteArray.empty

theorem daiNameReturnEncoding :
    encodeReturnValue? stringTy (.bytes daiNameBytes) = some daiNameReturnBytes := by
  native_decide

/-- The Solm `name()` body returns `"Dai Stablecoin"` as a dynamic string value. -/
theorem daiNameBodyReturns (evm : EVM.State)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm nameStore nameTransition.body
      (.returned { contract := contract, locals := nameStore } evm
        (some [.bytes daiNameBytes])) := by
  simpa [nameTransition, nameStore, daiNameBytes] using
    daiBytesLiteralBodyReturns evm nameStore daiNameBytes h

private def daiNameRawWord : UInt256 :=
  ⟨0x2230b49029ba30b13632b1b7b4b7⟩

private def daiNameLiteralWord : UInt256 :=
  UInt256.shiftLeft daiNameRawWord ⟨145⟩

private theorem daiNameReturnRead :
    (daiStringAbiMem3 daiNameLen daiNameLiteralWord).readWithPadding 192 96 =
      daiNameReturnBytes := by
  native_decide

/-- Runtime-only `name()` slice from selector dispatch through dynamic string return. -/
theorem daiX_name_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨327⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret daiBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      daiNameReturnBytes := by
  obtain ⟨_, _, h327⟩ := hreach
  have h1260 := evm_run h327 with [
    jumpdest, push2 ⟨335⟩, push2 ⟨1260⟩, jump (by jump_dest)]
  have h1270 := evm_run h1260 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    dup1, push1 ⟨64⟩, add, push1 ⟨64⟩]
  have h1271 := evm_run h1270 with [
    raw mstore 0 daiStringObjectMem0 (UInt256.ofNat 3) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov)]
  have h1275 := evm_run h1271 with [dup1, push1 daiNameLen, dup2]
  have h1276 := evm_run h1275 with [
    raw mstore 6 (daiStringObjectMem1 daiNameLen) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by native_decide) (by decide) (by evm_ov)]
  have h1279 := evm_run h1276 with [push1 ⟨32⟩, add]
  have h1294 := h1279.pushConst daiNameRawWord
    (width := 14) (op := .PUSH14) (by decide) (by native_decide) (by evm_ov)
  have h1298 := evm_run h1294 with [push1 ⟨145⟩, shl, dup2]
  have h1299 := evm_run h1298 with [
    raw mstore 3 (daiStringObjectMem daiNameLen daiNameLiteralWord)
      (UInt256.ofNat 6) (by native_decide) mem_cost
      (by native_decide) (by decide) (by evm_ov)]
  have h335 := evm_run h1299 with [pop, dup2, jump (by jump_dest)]
  have h344 := evm_run h335 with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    push1 ⟨32⟩, dup1, dup3,
    raw mstore 3 (daiStringAbiMem0 daiNameLen daiNameLiteralWord)
      (UInt256.ofNat 7) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov)]
  have h350 := evm_run h344 with [
    dup4,
    raw mload 0 daiNameLen (UInt256.ofNat 7) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    dup2, dup4, add,
    raw mstore 3 (daiStringAbiMem1 daiNameLen daiNameLiteralWord)
      (UInt256.ofNat 8) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov)]
  have h367 := evm_run h350 with [
    dup4,
    raw mload 0 daiNameLen (UInt256.ofNat 8) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    swap2, swap3, dup4, swap3, swap1, dup4, add, swap2, dup6, add, swap1,
    dup1, dup4, dup4, push1 ⟨0⟩]
  have h378 := evm_run h367 with [
    jumpdest, dup4, dup2, lt, iszero, push2 ⟨393⟩, jumpiNT (by decide)]
  have h393a := evm_run h378 with [
    dup2, dup2, add,
    raw mload 0 daiNameLiteralWord (UInt256.ofNat 8) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    dup4, dup3, add,
    raw mstore 3 (daiStringAbiMem2 daiNameLen daiNameLiteralWord)
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
    raw mload 0 daiNameLiteralWord (UInt256.ofNat 9) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    push1 ⟨1⟩, dup4, push1 ⟨32⟩, sub, push2 ⟨256⟩, exp, sub, not, and, dup2,
    raw mstore 0 (daiStringAbiMem3 daiNameLen daiNameLiteralWord)
      (UInt256.ofNat 9) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, swap2, pop]
  have h451 := evm_run h438 with [
    jumpdest, pop, swap3, pop, pop, pop, push1 ⟨64⟩,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  exact evm_run h451 with [
    raw ret 0 daiNameReturnBytes (by native_decide)
      mem_cost daiNameReturnRead (by evm_ov)]

theorem daiNameBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = daiBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some nameTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (nameTransition.params.map Param.name)
        (transitionSignature nameTransition).paramTypes I.calldata =
          some nameStore)
    (hreach : ∃ k C, RD daiBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨327⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        nameStore
        nameTransition.body
        (.returned { contract := contract, locals := nameStore }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [.bytes daiNameBytes])) := by
    exact daiNameBodyReturns
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (by simp only [initState]; exact hwv)
  exact (daiX_name_ok (g := Sat256.ofUInt256 g) hreach)
    |>.reEquivExecutionTransport hcode hdispatch hdecode hbody rfl
      hAccounts
      (by
        rw [nameTransition]
        exact returnEquiv_of_encode daiNameReturnEncoding)

theorem daiDecode_name_ok {I : ExecutionEnv} (hsz4 : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (nameTransition.params.map Param.name)
      (transitionSignature nameTransition).paramTypes I.calldata =
        some nameStore := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata =
    some (∅ : Store)
  exact decodeCalldataWithMode_empty_ok hsz4

/-- `name()` body refines its Solm transition. -/
theorem daiNameBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (daiSelBytes 9))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (daiSelBytes 9) (by native_decide) hsel
  have hdispatch : dispatchMsg contract I.calldata = some nameTransition :=
    daiDispatchName hsel
  have hreach := daiReachNameBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  exact daiNameBodyCoreOk hcode hsize hwv hdispatch
    (daiDecode_name_ok hsz4) hreach hAccounts

end Benchmarks.Dss.Dai
