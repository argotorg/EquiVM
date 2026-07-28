import Examples.UniswapV2Pair.StringReturn
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `name()` dynamic string getter -/

def nameReturnBytes : ByteArray :=
  (encodeReturnValue? .string (.bytes nameBytes)).getD ByteArray.empty

theorem nameReturnEncoding :
    encodeReturnValue? .string (.bytes nameBytes) = some nameReturnBytes := by
  native_decide

/-- The Solm `name()` body returns `"Uniswap V2"` as a dynamic string value. -/
theorem uniswapNameBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm locals nameTransition.body
      (.returned { contract := contract, locals := locals } evm (some [(.bytes nameBytes)])) := by
  simpa [nameTransition] using uniswapBytesLiteralBodyReturns evm locals nameBytes h

private def nameLiteralWord : UInt256 :=
  UInt256.shiftLeft ⟨201718945720142287350553⟩ ⟨177⟩

private def nameObjectMem0 : ByteArray :=
  (UInt256.toByteArray ⟨192⟩).write 0 solcFreePtrMem 64 32

private def nameObjectMem1 : ByteArray :=
  (UInt256.toByteArray ⟨10⟩).write 0 nameObjectMem0 128 32

private def nameObjectMem : ByteArray :=
  (UInt256.toByteArray nameLiteralWord).write 0 nameObjectMem1 160 32

private def nameAbiMem0 : ByteArray :=
  (UInt256.toByteArray ⟨32⟩).write 0 nameObjectMem 192 32

private def nameAbiMem1 : ByteArray :=
  (UInt256.toByteArray ⟨10⟩).write 0 nameAbiMem0 224 32

private def nameAbiMem2 : ByteArray :=
  (UInt256.toByteArray nameLiteralWord).write 0 nameAbiMem1 256 32

private def nameTailMask : UInt256 :=
  UInt256.lnot (UInt256.sub (UInt256.exp ⟨256⟩ (UInt256.sub ⟨32⟩ ⟨10⟩)) ⟨1⟩)

private def nameCleanWord : UInt256 :=
  UInt256.land nameTailMask nameLiteralWord

private def nameAbiMem3 : ByteArray :=
  (UInt256.toByteArray nameCleanWord).write 0 nameAbiMem2 256 32

private theorem nameReturnRead :
    nameAbiMem3.readWithPadding 192 96 = nameReturnBytes := by
  native_decide

/-- Runtime-only `name()` slice from selector dispatch through dynamic string return. -/
theorem uniswapX_name {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨572⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      nameReturnBytes := by
  obtain ⟨_, _, h572⟩ := hreach
  have h2814 := evm_run h572 with [jumpdest, push2 ⟨580⟩, push2 ⟨2814⟩, jump (by jump_dest)]
  have h2825 := evm_run h2814 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    dup1, push1 ⟨64⟩, add, push1 ⟨64⟩]
  have h2825store := evm_run h2825 with [
    raw mstore 0 nameObjectMem0 (UInt256.ofNat 3) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov)]
  have h2830 := evm_run h2825store with [dup1, push1 ⟨10⟩, dup2]
  have h2830store := evm_run h2830 with [
    raw mstore 6 nameObjectMem1 (UInt256.ofNat 5) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov)]
  have h2849a := evm_run h2830store with [push1 ⟨32⟩, add]
  have h2844 := h2849a.pushConst (⟨201718945720142287350553⟩ : UInt256)
    (width := 10) (op := .PUSH10) (by decide) (by native_decide) (by evm_ov)
  have h2849 := evm_run h2844 with [push1 ⟨177⟩, shl, dup2]
  have h2849store := evm_run h2849 with [
    raw mstore 3 nameObjectMem (UInt256.ofNat 6) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov)]
  have h580 := evm_run h2849store with [pop, dup2, jump (by jump_dest)]
  have h590 := evm_run h580 with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    push1 ⟨32⟩, dup1, dup3,
    raw mstore 3 nameAbiMem0 (UInt256.ofNat 7) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov)]
  have h596 := evm_run h590 with [
    dup4,
    raw mload 0 ⟨10⟩ (UInt256.ofNat 7) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    dup2, dup4, add,
    raw mstore 3 nameAbiMem1 (UInt256.ofNat 8) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov)]
  have h614 := evm_run h596 with [
    dup4,
    raw mload 0 ⟨10⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    swap2, swap3, dup4, swap3, swap1, dup4, add, swap2, dup6, add, swap1,
    dup1, dup4, dup4, push1 ⟨0⟩]
  have h623 := evm_run h614 with [
    jumpdest, dup4, dup2, lt, iszero, push2 ⟨638⟩, jumpiNT (by decide)]
  have h637 := evm_run h623 with [
    dup2, dup2, add,
    raw mload 0 nameLiteralWord (UInt256.ofNat 8) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    dup4, dup3, add,
    raw mstore 3 nameAbiMem2 (UInt256.ofNat 9) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨614⟩, jump (by jump_dest)]
  have h638 := evm_run h637 with [
    jumpdest, dup4, dup2, lt, iszero, push2 ⟨638⟩, jumpiT (by decide) (by jump_dest)]
  have h658 := evm_run h638 with [
    jumpdest, pop, pop, pop, pop, swap1, pop, swap1, dup2, add, swap1,
    push1 ⟨31⟩, and, dup1, iszero, push2 ⟨683⟩, jumpiNT (by decide)]
  have h683 := evm_run h658 with [
    dup1, dup3, sub, dup1,
    raw mload 0 nameLiteralWord (UInt256.ofNat 9) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    push1 ⟨1⟩, dup4, push1 ⟨32⟩, sub, push2 ⟨256⟩, exp, sub, not, and, dup2,
    raw mstore 0 nameAbiMem3 (UInt256.ofNat 9) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, swap2, pop]
  have h696 := evm_run h683 with [
    jumpdest, pop, swap3, pop, pop, pop, push1 ⟨64⟩,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  exact evm_run h696 with [
    raw ret 0 nameReturnBytes (by native_decide)
      mem_cost nameReturnRead (by evm_ov)]

/-- `name()` body core, parameterized by dispatcher/decode facts owned by `Correct`. -/
theorem uniswapNameBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some nameTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (nameTransition.params.map Param.name)
        (transitionSignature nameTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨572⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ nameTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.bytes nameBytes)])) := by
    exact uniswapNameBodyReturns
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
      (by simp only [initState]; exact hwv)
  have henc :
      returnEquiv nameReturnBytes (some [.bytes nameBytes]) nameTransition.returnType := by
    rw [nameTransition]
    exact returnEquiv_of_encode nameReturnEncoding
  exact (uniswapX_name (g := Sat256.ofUInt256 g) hreach).reEquivExecutionTransport
    hcode hdispatch hdecode hbody rfl hAccounts henc

theorem uniswapNameBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x06, 0xfd, 0xde, 0x03]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some nameTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x06, 0xfd, 0xde, 0x03]⟩ rfl hsel
  exact uniswapNameBodyCore hcode hwv hdispatch (uniswapDecode_name hsz)
    (uniswapReachNameBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
    hAccounts

end UniswapV2Pair
