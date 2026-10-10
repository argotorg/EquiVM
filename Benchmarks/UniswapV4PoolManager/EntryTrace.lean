import Benchmarks.UniswapV4PoolManager.Common
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_005

/-! Memory and the shared empty revert at PoolManager ABI entries. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager

def entryMemory : ByteArray := writeWord .empty 64 ⟨160⟩

theorem entryMemory_load64 : memLoad ⟨64⟩ entryMemory = ⟨160⟩ := by native_decide

theorem entryMemory_returnWord (value : UInt256) :
    (value.toByteArray.write 0 entryMemory (memLoad ⟨64⟩ entryMemory).toNat 32).readWithPadding
      (memLoad ⟨64⟩ entryMemory).toNat 32 = value.toByteArray := by
  rw [entryMemory_load64]
  exact writeWord_read_back entryMemory 160 value (by native_decide)

theorem emptyRevert {I : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 2 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨816⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 :=
  poolManagerBlocks.poolManager_block_816 hstack h

-- LIBRARY CANDIDATE: a selected entry that reverts for every decoded argument store.
theorem selectedRevert {cfg : Config} {C : ContractDecl} {t : TransitionDecl}
    {imms : Store} {σ σ₀ A I} {g : Sat256} {code : ByteArray}
    (hcode : I.code = code) (h : RDrev code g (initState σ σ₀ g A I))
    (hd : dispatchMsg C I.calldata = some t)
    (hbody : ∀ args, ExecTransitionBody cfg C (initState σ σ₀ g A I)
      args t.body .reverted imms)
    (hfallback : C.fallback = none := by rfl) (hreceive : C.receive = none := by rfl) :
    runtimeRefinementFor cfg C σ σ₀ g.toUInt256 A I imms := by
  cases hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata with
  | none => exact h.reEquivDecodingFailed hcode hd hdec hfallback hreceive
  | some args => exact h.reEquivExecutionRevert hcode hd hdec (hbody args) hfallback hreceive

-- GENERALIZES Reasoning.Theory.wordAt0Mem_read0 to the raw memory expression.
theorem returnWordAtZero (word : UInt256) (mem : ByteArray) :
    (word.toByteArray.write 0 mem 0 32).readWithPadding 0 32 = word.toByteArray :=
  wordAt0Mem_read0 word mem

theorem deployedRuntime_jumps (v : PoolManagerImmutables) :
    D_J (deployedRuntime v) 0 = D_J poolManagerBytecode 0 :=
  poolManagerPatchedValidJumpsRuntime v

end Benchmarks.UniswapV4PoolManager
