import Examples.Precompiles.Identity.Bytecode
import Examples.Precompiles.Identity.Model
import Reasoning.Bytecode

/-!
# Identity bytecode correctness

Direct bytecode-to-pure-model correctness with an exact bytecode gas expression and OOG boundary.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Identity

/-- Number of calldata words copied by the implementation. -/
def calldataWords (I : ExecutionEnv) : Nat :=
  (I.calldata.size + 31) / 32

/-- Active memory words after copying all calldata to address zero. -/
def copiedActiveWords (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (MachineState.M 0 0 I.calldata.size)

/-- Memory after `CALLDATACOPY(0, 0, calldatasize())`. -/
def copiedMemory (I : ExecutionEnv) : ByteArray :=
  I.calldata.write 0 ByteArray.empty 0 I.calldata.size

/-- Memory expansion charged by `CALLDATACOPY`. -/
def copyMemoryGas (I : ExecutionEnv) : Nat :=
  Cₘ (copiedActiveWords I) - Cₘ (UInt256.ofNat 0)

/-- Memory expansion charged by the final `RETURN`.

The preceding copy already covers the returned region, so this reduces to zero for accepted calls.
Retaining the semantic expression keeps the exact trace independent of that normalization lemma.
-/
def returnMemoryGas (I : ExecutionEnv) : Nat :=
  Cₘ (UInt256.ofNat
    (MachineState.M (copiedActiveWords I).toNat 0 I.calldata.size)) -
      Cₘ (copiedActiveWords I)

/-- Exact gas consumed by the seven-byte implementation. -/
def gasCost (I : ExecutionEnv) : Nat :=
  13 + 3 * calldataWords I + copyMemoryGas I + returnMemoryGas I

/-- The model is defined for calldata lengths supported by EVMLean's padded byte-array reader. -/
def accepts (ctx : BytecodeContext) : Prop :=
  ctx.executionEnv.calldata.size < 2 ^ 64

/-- Functional output and exact gas behavior at the caller-visible boundary. -/
def ensures (ctx : BytecodeContext) (result : BytecodeResult) : Prop :=
  ExactGasPost ctx (model ctx.executionEnv.calldata)
    (gasCost ctx.executionEnv) result

private theorem calldataSize_lt_uint256 {I : ExecutionEnv}
    (hsize : I.calldata.size < 2 ^ 64) : I.calldata.size < UInt256.size := by
  rw [show UInt256.size = 2 ^ 256 from by decide]
  exact lt_trans hsize (by norm_num)

private theorem copiedMemory_read (I : ExecutionEnv)
    (hsize : I.calldata.size < 2 ^ 64) :
    (copiedMemory I).readWithPadding 0 I.calldata.size = model I.calldata := by
  by_cases hempty : I.calldata.size = 0
  · have hdata : I.calldata = ByteArray.empty :=
      byteArray_eq_empty_of_size_eq_zero I.calldata hempty
    simp [copiedMemory, model, hdata, ByteArray.write, ByteArray.readWithPadding,
      ByteArray.readWithoutPadding, zeroes_zero]
  · rw [copiedMemory, model,
      write0_read_back_gen I.calldata ByteArray.empty I.calldata.size hempty
        (le_refl _) hsize,
      byteArray_extract_self]

/-- Exact threshold-preserving execution trace for the Identity bytecode. -/
theorem successExactGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hsize : I.calldata.size < 2 ^ 64) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ) (model I.calldata) (gasCost I) := by
  have hsize256 := calldataSize_lt_uint256 hsize
  have rd0 := RDx.initState
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hcode
  have rd1 := RDx.calldatasize rd0 (by decide) (by simp)
  have rd2 := RDx.push0 rd1 (by decide) (by simp)
  have rd3 := RDx.push0 rd2 (by decide) (by simp)
  have rd4 := RDx.calldatacopy
    (copyMemoryGas I) (copiedMemory I) (copiedActiveWords I)
    rd3 (by decide)
    (by
      intro s haw hstk
      simp [copyMemoryGas, copiedActiveWords, memoryExpansionCost,
        memoryExpansionCost.μᵢ', haw, hstk]
      rw [show (UInt256.ofNat 0).toNat = 0 from rfl,
        ulit_toNat' I.calldata.size hsize256])
    (by
      simp [copiedMemory]
      rw [ulit_toNat' I.calldata.size hsize256])
    (by
      simp [copiedActiveWords]
      rw [show (UInt256.ofNat 0).toNat = 0 from rfl,
        ulit_toNat' I.calldata.size hsize256])
    (by decide)
  have rd5 := RDx.calldatasize rd4 (by decide) (by simp)
  have rd6 := RDx.push0 rd5 (by decide) (by simp)
  have rdret := RDx.ret (returnMemoryGas I) (model I.calldata)
    rd6 (by decide)
    (by
      intro s haw hstk
      simp [returnMemoryGas, memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      rw [ulit_toNat' I.calldata.size hsize256])
    (by
      rw [ulit_toNat' I.calldata.size hsize256]
      exact copiedMemory_read I hsize)
    (by decide)
  convert rdret using 1
  simp [gasCost, calldataWords, GasConstants.Gverylow, GasConstants.Gcopy,
    ulit_toNat' I.calldata.size hsize256]
  omega

/-- Final `BytecodeSpec`: the implementation returns its input unchanged, consumes exactly
`gasCost`, and fails with the common exceptional observation precisely below that threshold. -/
theorem bytecodeSpec : BytecodeSpec runtimeBytecode accepts ensures := by
  simpa [accepts, ensures] using
    (ExactGasSpec.ofRDxRet (code := runtimeBytecode)
      (accepts := accepts)
      (output := fun ctx => model ctx.executionEnv.calldata)
      (gasCost := fun ctx => gasCost ctx.executionEnv)
      (fun ctx hcode hsize =>
        successExactGas
          (cA := ctx.createdAccounts) (gh := ctx.genesisBlockHeader) (bl := ctx.blocks)
          (σ := ctx.accountMap) (σ₀ := ctx.originalAccountMap) (A := ctx.substate)
          (I := ctx.executionEnv) (g := ctx.gas) hcode hsize))

end Identity
