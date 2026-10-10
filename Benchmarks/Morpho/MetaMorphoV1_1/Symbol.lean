import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.StringCopyRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.StringAllocatedReturn
import Benchmarks.Morpho.MetaMorphoV1_1.StringViewSource

/-!
# MetaMorphoV1_1 `symbol()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 4587; reach lemma `metaMorphoV1_1ReachSymbolBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

/-- `symbol()`: the theorem `Correct.lean` routes selector 44 to. -/
theorem metaMorphoV1_1SymbolBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 44)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 44) rfl hsel
  have hd : dispatchMsg contract I.calldata = some symbolTransition := by
    apply metaMorphoV1_1Dispatch_symbol <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (symbolTransition.params.map Param.name)
      (transitionSignature symbolTransition).paramTypes I.calldata = some ∅ :=
    decodeCalldata_empty_ok hsz
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachSymbolBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · obtain ⟨aw1, k1, C1, h1⟩ := stringViewReachDecoder v true (by simp) hwv hsz hhi hsize rd
      have hfree : memLoad ⟨64⟩
          ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty
            (UInt256.ofNat 64).toNat 32) = ⟨128⟩ := solcFreePtrMem_mload64
      rw [hfree] at h1
      by_cases hvalid : storageStringValid (storageStringHeader evm ⟨25⟩)
      · obtain ⟨aw2, k2, C2, h2⟩ := storageStringDecoderReturn v (by simp)
          hvalid (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
        obtain ⟨aw3, k3, C3, h3⟩ := stringCopyToAllocation v true (by simp) hvalid h2
        have hlen := storageStringLength_lt (storageStringHeader evm ⟨25⟩)
        by_cases hfit : allocationFits ⟨128⟩
            (stringCopySize (storageStringLength (storageStringHeader evm ⟨25⟩)))
        · have hsrc : allocationFits ⟨128⟩
              (UInt256.ofNat ((storageStringBytes evm ⟨25⟩).size + 32)) := by
            rw [storageStringBytes_size]
            exact (stringAllocationFits _ hlen).mp hfit
          have hret := stringAllocatedReturn (evm := evm) v ⟨25⟩ (by simp) hvalid hfit h3
          exact hret.reEquivExecutionGen hcode hd hdec
            (stringViewBodyReturns true evm (immStore v) hwv hhi hvalid hsrc) rfl
            (returnEquiv_of_encode (stringReturnEncoding _))
        · have hsrc : ¬ allocationFits ⟨128⟩
              (UInt256.ofNat ((storageStringBytes evm ⟨25⟩).size + 32)) := by
            rw [storageStringBytes_size]
            exact fun h ↦ hfit ((stringAllocationFits _ hlen).mpr h)
          exact (allocateRoundedRevert v (by simp) hfit h3).reEquivExecutionRevert
            hcode hd hdec (stringViewRevertsAllocation true evm (immStore v)
              hwv hhi hvalid hsrc)
      · exact (storageStringDecoderRevert v (by simp) hvalid h1).reEquivExecutionRevert
          hcode hd hdec (stringViewRevertsHeader true evm (immStore v) hwv hhi hvalid)
    · exact (stringViewRevertHuge v true (by simp) hwv (by omega) hsize rd).reEquivExecutionRevert
        hcode hd hdec
        (bodyReverts_calldataBound "__calldata" (2 ^ 255 + 4) hwv (Nat.le_of_not_gt hhi))
  · exact (stringViewRevertNonPayable v true (by simp) hwv rd).reEquivExecutionRevert
      hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1
