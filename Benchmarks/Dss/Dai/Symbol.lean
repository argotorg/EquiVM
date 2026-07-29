import Benchmarks.Dss.Dai.StringReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Dai

/-! ## `symbol()` dynamic string getter -/

abbrev symbolStore : Store :=
  ∅

abbrev daiSymbolLen : UInt256 :=
  ⟨3⟩

def daiSymbolReturnBytes : ByteArray :=
  (encodeReturnValue? stringTy (.bytes daiSymbolBytes)).getD ByteArray.empty

theorem daiSymbolReturnEncoding :
    encodeReturnValue? stringTy (.bytes daiSymbolBytes) = some daiSymbolReturnBytes := by
  native_decide

/-- The Solm `symbol()` body returns `"DAI"` as a dynamic string value. -/
theorem daiSymbolBodyReturns (evm : EVM.State)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm symbolStore symbolTransition.body
      (.returned { contract := contract, locals := symbolStore } evm
        (some [.bytes daiSymbolBytes])) := by
  simpa [symbolTransition, symbolStore, daiSymbolBytes] using
    daiBytesLiteralBodyReturns evm symbolStore daiSymbolBytes h

private def daiSymbolRawWord : UInt256 :=
  ⟨0x444149⟩

private def daiSymbolLiteralWord : UInt256 :=
  UInt256.shiftLeft daiSymbolRawWord ⟨232⟩

private theorem daiSymbolReturnRead :
    (daiStringAbiMem3 daiSymbolLen daiSymbolLiteralWord).readWithPadding 192 96 =
      daiSymbolReturnBytes := by
  native_decide

/-- Runtime-only `symbol()` slice from selector dispatch through dynamic string return. -/
theorem daiX_symbol_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨900⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret daiBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      daiSymbolReturnBytes := by
  obtain ⟨_, _, h900⟩ := hreach
  have h3190 := evm_run h900 with [
    jumpdest, push2 ⟨335⟩, push2 ⟨3190⟩, jump (by jump_dest)]
  have h3200 := evm_run h3190 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    dup1, push1 ⟨64⟩, add, push1 ⟨64⟩]
  have h3201 := evm_run h3200 with [
    raw mstore 0 daiStringObjectMem0 (UInt256.ofNat 3) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov)]
  have h3205 := evm_run h3201 with [dup1, push1 daiSymbolLen, dup2]
  have h3206 := evm_run h3205 with [
    raw mstore 6 (daiStringObjectMem1 daiSymbolLen) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by native_decide) (by decide) (by evm_ov)]
  have h3209 := evm_run h3206 with [push1 ⟨32⟩, add]
  have h3213 := h3209.pushConst daiSymbolRawWord
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have h3217 := evm_run h3213 with [push1 ⟨232⟩, shl, dup2]
  have h3218 := evm_run h3217 with [
    raw mstore 3 (daiStringObjectMem daiSymbolLen daiSymbolLiteralWord)
      (UInt256.ofNat 6) (by native_decide) mem_cost
      (by native_decide) (by decide) (by evm_ov)]
  have h335 := evm_run h3218 with [pop, dup2, jump (by jump_dest)]
  have h344 := evm_run h335 with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    push1 ⟨32⟩, dup1, dup3,
    raw mstore 3 (daiStringAbiMem0 daiSymbolLen daiSymbolLiteralWord)
      (UInt256.ofNat 7) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov)]
  have h350 := evm_run h344 with [
    dup4,
    raw mload 0 daiSymbolLen (UInt256.ofNat 7) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    dup2, dup4, add,
    raw mstore 3 (daiStringAbiMem1 daiSymbolLen daiSymbolLiteralWord)
      (UInt256.ofNat 8) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov)]
  have h367 := evm_run h350 with [
    dup4,
    raw mload 0 daiSymbolLen (UInt256.ofNat 8) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    swap2, swap3, dup4, swap3, swap1, dup4, add, swap2, dup6, add, swap1,
    dup1, dup4, dup4, push1 ⟨0⟩]
  have h378 := evm_run h367 with [
    jumpdest, dup4, dup2, lt, iszero, push2 ⟨393⟩, jumpiNT (by decide)]
  have h393a := evm_run h378 with [
    dup2, dup2, add,
    raw mload 0 daiSymbolLiteralWord (UInt256.ofNat 8) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    dup4, dup3, add,
    raw mstore 3 (daiStringAbiMem2 daiSymbolLen daiSymbolLiteralWord)
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
    raw mload 0 daiSymbolLiteralWord (UInt256.ofNat 9) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    push1 ⟨1⟩, dup4, push1 ⟨32⟩, sub, push2 ⟨256⟩, exp, sub, not, and, dup2,
    raw mstore 0 (daiStringAbiMem3 daiSymbolLen daiSymbolLiteralWord)
      (UInt256.ofNat 9) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, swap2, pop]
  have h451 := evm_run h438 with [
    jumpdest, pop, swap3, pop, pop, pop, push1 ⟨64⟩,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  exact evm_run h451 with [
    raw ret 0 daiSymbolReturnBytes (by native_decide)
      mem_cost daiSymbolReturnRead (by evm_ov)]

theorem daiSymbolBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = daiBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some symbolTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (symbolTransition.params.map Param.name)
        (transitionSignature symbolTransition).paramTypes I.calldata =
          some symbolStore)
    (hreach : ∃ k C, RD daiBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨900⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        symbolStore
        symbolTransition.body
        (.returned { contract := contract, locals := symbolStore }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [.bytes daiSymbolBytes])) := by
    exact daiSymbolBodyReturns
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (by simp only [initState]; exact hwv)
  exact (daiX_symbol_ok (g := Sat256.ofUInt256 g) hreach)
    |>.reEquivExecutionTransport hcode hdispatch hdecode hbody rfl
      hAccounts
      (by
        rw [symbolTransition]
        exact returnEquiv_of_encode daiSymbolReturnEncoding)

theorem daiDecode_symbol_ok {I : ExecutionEnv} (hsz4 : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (symbolTransition.params.map Param.name)
      (transitionSignature symbolTransition).paramTypes I.calldata =
        some symbolStore := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata =
    some (∅ : Store)
  exact decodeCalldataWithMode_empty_ok hsz4

/-- `symbol()` body refines its Solm transition. -/
theorem daiSymbolBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (daiSelBytes 16))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (daiSelBytes 16) (by native_decide) hsel
  have hdispatch : dispatchMsg contract I.calldata = some symbolTransition :=
    daiDispatchSymbol hsel
  have hreach := daiReachSymbolBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  exact daiSymbolBodyCoreOk hcode hsize hwv hdispatch
    (daiDecode_symbol_ok hsz4) hreach hAccounts

end Benchmarks.Dss.Dai
