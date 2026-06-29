import Examples.UniswapV2Pair.StringReturn
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `symbol()` dynamic string getter -/

def symbolReturnBytes : ByteArray :=
  (encodeReturnValue? .string (.bytes symbolBytes)).getD ByteArray.empty

theorem symbolReturnEncoding :
    encodeReturnValue? .string (.bytes symbolBytes) = some symbolReturnBytes := by
  native_decide

/-- The Solm `symbol()` body returns `"UNI-V2"` as a dynamic string value. -/
theorem uniswapSymbolBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm locals symbolTransition.body
      (.returned { contract := contract, locals := locals } evm (some (.bytes symbolBytes))) := by
  simpa [symbolTransition] using uniswapBytesLiteralBodyReturns evm locals symbolBytes h

private def symbolLiteralWord : UInt256 :=
  UInt256.shiftLeft ⟨46897361759001⟩ ⟨209⟩

private def symbolObjectMem0 : ByteArray :=
  (UInt256.toByteArray ⟨192⟩).write 0 solcFreePtrMem 64 32

private def symbolObjectMem1 : ByteArray :=
  (UInt256.toByteArray ⟨6⟩).write 0 symbolObjectMem0 128 32

private def symbolObjectMem : ByteArray :=
  (UInt256.toByteArray symbolLiteralWord).write 0 symbolObjectMem1 160 32

private def symbolAbiMem0 : ByteArray :=
  (UInt256.toByteArray ⟨32⟩).write 0 symbolObjectMem 192 32

private def symbolAbiMem1 : ByteArray :=
  (UInt256.toByteArray ⟨6⟩).write 0 symbolAbiMem0 224 32

private def symbolAbiMem2 : ByteArray :=
  (UInt256.toByteArray symbolLiteralWord).write 0 symbolAbiMem1 256 32

private def symbolTailMask : UInt256 :=
  UInt256.lnot (UInt256.sub (UInt256.exp ⟨256⟩ (UInt256.sub ⟨32⟩ ⟨6⟩)) ⟨1⟩)

private def symbolCleanWord : UInt256 :=
  UInt256.land symbolTailMask symbolLiteralWord

private def symbolAbiMem3 : ByteArray :=
  (UInt256.toByteArray symbolCleanWord).write 0 symbolAbiMem2 256 32

private theorem symbolReturnRead :
    symbolAbiMem3.readWithPadding 192 96 = symbolReturnBytes := by
  native_decide

/-- Runtime-only `symbol()` slice from selector dispatch through dynamic string return. -/
theorem uniswapX_symbol {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1226⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      symbolReturnBytes := by
  obtain ⟨_, _, h1226⟩ := hreach
  have h5027 := evm_run h1226 with [jumpdest, push2 ⟨580⟩, push2 ⟨5027⟩, jump (by jump_dest)]
  have h5037 := evm_run h5027 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    dup1, push1 ⟨64⟩, add, push1 ⟨64⟩]
  have h5037store := evm_run h5037 with [
    raw mstore 0 symbolObjectMem0 (UInt256.ofNat 3) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov)]
  have h5042 := evm_run h5037store with [dup1, push1 ⟨6⟩, dup2]
  have h5042store := evm_run h5042 with [
    raw mstore 6 symbolObjectMem1 (UInt256.ofNat 5) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov)]
  have h5046a := evm_run h5042store with [push1 ⟨32⟩, add]
  have h5053 := h5046a.pushConst (⟨46897361759001⟩ : UInt256)
    (width := 6) (op := .PUSH6) (by decide) (by native_decide) (by evm_ov)
  have h5058 := evm_run h5053 with [push1 ⟨209⟩, shl, dup2]
  have h5058store := evm_run h5058 with [
    raw mstore 3 symbolObjectMem (UInt256.ofNat 6) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov)]
  have h580 := evm_run h5058store with [pop, dup2, jump (by jump_dest)]
  have h590 := evm_run h580 with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    push1 ⟨32⟩, dup1, dup3,
    raw mstore 3 symbolAbiMem0 (UInt256.ofNat 7) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov)]
  have h596 := evm_run h590 with [
    dup4,
    raw mload 0 ⟨6⟩ (UInt256.ofNat 7) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    dup2, dup4, add,
    raw mstore 3 symbolAbiMem1 (UInt256.ofNat 8) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov)]
  have h614 := evm_run h596 with [
    dup4,
    raw mload 0 ⟨6⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    swap2, swap3, dup4, swap3, swap1, dup4, add, swap2, dup6, add, swap1,
    dup1, dup4, dup4, push1 ⟨0⟩]
  have h623 := evm_run h614 with [
    jumpdest, dup4, dup2, lt, iszero, push2 ⟨638⟩, jumpiNT (by decide)]
  have h637 := evm_run h623 with [
    dup2, dup2, add,
    raw mload 0 symbolLiteralWord (UInt256.ofNat 8) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    dup4, dup3, add,
    raw mstore 3 symbolAbiMem2 (UInt256.ofNat 9) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨614⟩, jump (by jump_dest)]
  have h638 := evm_run h637 with [
    jumpdest, dup4, dup2, lt, iszero, push2 ⟨638⟩, jumpiT (by decide) (by jump_dest)]
  have h658 := evm_run h638 with [
    jumpdest, pop, pop, pop, pop, swap1, pop, swap1, dup2, add, swap1,
    push1 ⟨31⟩, and, dup1, iszero, push2 ⟨683⟩, jumpiNT (by decide)]
  have h683 := evm_run h658 with [
    dup1, dup3, sub, dup1,
    raw mload 0 symbolLiteralWord (UInt256.ofNat 9) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    push1 ⟨1⟩, dup4, push1 ⟨32⟩, sub, push2 ⟨256⟩, exp, sub, not, and, dup2,
    raw mstore 0 symbolAbiMem3 (UInt256.ofNat 9) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, swap2, pop]
  have h696 := evm_run h683 with [
    jumpdest, pop, swap3, pop, pop, pop, push1 ⟨64⟩,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  exact evm_run h696 with [
    raw ret 0 symbolReturnBytes (by native_decide)
      mem_cost symbolReturnRead (by evm_ov)]

/-- `symbol()` body core, parameterized by dispatcher/decode facts owned by `Correct`. -/
theorem uniswapSymbolBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some symbolTransition)
    (hdecode :
      decodeCalldata (symbolTransition.params.map Param.name)
        (transitionSignature symbolTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1226⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ symbolTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.bytes symbolBytes))) := by
    exact uniswapSymbolBodyReturns
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
      (by simp only [initState]; exact hwv)
  have henc :
      returnEquiv symbolReturnBytes (some (.bytes symbolBytes)) symbolTransition.returnType := by
    rw [symbolTransition]
    exact returnEquiv_of_encode symbolReturnEncoding
  exact (uniswapX_symbol (g := Sat256.ofUInt256 g) hreach).reEquivExecutionTransport
    hcode hdispatch hdecode hbody rfl hAccounts henc

theorem uniswapSymbolBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x95, 0xd8, 0x9b, 0x41]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some symbolTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x95, 0xd8, 0x9b, 0x41]⟩ rfl hsel
  exact uniswapSymbolBodyCore hcode hwv hdispatch (uniswapDecode_symbol hsz)
    (uniswapReachSymbolBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
    hAccounts

end UniswapV2Pair
