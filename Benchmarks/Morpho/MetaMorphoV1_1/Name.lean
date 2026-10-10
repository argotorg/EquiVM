import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.StringCopyRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.StringAllocatedReturn
import Benchmarks.Morpho.MetaMorphoV1_1.StringViewSource

/-!
# MetaMorphoV1_1 `name()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 10884; reach lemma `metaMorphoV1_1ReachNameBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

/-- `name()`: the theorem `Correct.lean` routes selector 1 to. -/
theorem metaMorphoV1_1NameBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 1)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 1) rfl hsel
  have hd : dispatchMsg contract I.calldata = some nameTransition := by
    apply metaMorphoV1_1Dispatch_name <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (nameTransition.params.map Param.name)
      (transitionSignature nameTransition).paramTypes I.calldata = some ∅ :=
    decodeCalldata_empty_ok hsz
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachNameBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · obtain ⟨aw1, k1, C1, h1⟩ := stringViewReachDecoder v false (by simp) hwv hsz hhi hsize rd
      have hfree : memLoad ⟨64⟩
          ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty
            (UInt256.ofNat 64).toNat 32) = ⟨128⟩ := solcFreePtrMem_mload64
      rw [hfree] at h1
      by_cases hvalid : storageStringValid (storageStringHeader evm ⟨24⟩)
      · obtain ⟨aw2, k2, C2, h2⟩ := storageStringDecoderReturn v (by simp)
          hvalid (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
        obtain ⟨aw3, k3, C3, h3⟩ := stringCopyToAllocation v false (by simp) hvalid h2
        have hlen := storageStringLength_lt (storageStringHeader evm ⟨24⟩)
        by_cases hfit : allocationFits ⟨128⟩
            (stringCopySize (storageStringLength (storageStringHeader evm ⟨24⟩)))
        · have hsrc : allocationFits ⟨128⟩
              (UInt256.ofNat ((storageStringBytes evm ⟨24⟩).size + 32)) := by
            rw [storageStringBytes_size]
            exact (stringAllocationFits _ hlen).mp hfit
          have hret := stringAllocatedReturn (evm := evm) v ⟨24⟩ (by simp) hvalid hfit h3
          exact hret.reEquivExecutionGen hcode hd hdec
            (stringViewBodyReturns false evm (immStore v) hwv hhi hvalid hsrc) rfl
            (returnEquiv_of_encode (stringReturnEncoding _))
        · have hsrc : ¬ allocationFits ⟨128⟩
              (UInt256.ofNat ((storageStringBytes evm ⟨24⟩).size + 32)) := by
            rw [storageStringBytes_size]
            exact fun h ↦ hfit ((stringAllocationFits _ hlen).mpr h)
          exact (allocateRoundedRevert v (by simp) hfit h3).reEquivExecutionRevert
            hcode hd hdec (stringViewRevertsAllocation false evm (immStore v)
              hwv hhi hvalid hsrc)
      · exact (storageStringDecoderRevert v (by simp) hvalid h1).reEquivExecutionRevert
          hcode hd hdec (stringViewRevertsHeader false evm (immStore v) hwv hhi hvalid)
    · exact (stringViewRevertHuge v false (by simp) hwv (by omega) hsize rd).reEquivExecutionRevert
        hcode hd hdec
        (bodyReverts_calldataBound "__calldata" (2 ^ 255 + 4) hwv (Nat.le_of_not_gt hhi))
  · exact (stringViewRevertNonPayable v false (by simp) hwv rd).reEquivExecutionRevert
      hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1
