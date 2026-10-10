import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.Eip712Entry
import Benchmarks.Morpho.MetaMorphoV1_1.Eip712ExtensionsRoutines

/-!
# MetaMorphoV1_1 `eip712Domain()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 4948; reach lemma `metaMorphoV1_1ReachEip712DomainBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

/-- `eip712Domain()`: the theorem `Correct.lean` routes selector 40 to. -/
theorem metaMorphoV1_1Eip712DomainBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 40)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 40) rfl hsel
  have hd : dispatchMsg contract I.calldata = some eip712DomainTransition := by
    apply metaMorphoV1_1Dispatch_eip712Domain <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (eip712DomainTransition.params.map Param.name)
      (transitionSignature eip712DomainTransition).paramTypes I.calldata = some ∅ :=
    decodeCalldata_empty_ok hsz
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachEip712DomainBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  by_cases hwv : I.weiValue = ⟨0⟩
  case neg =>
    exact (eip712RevertNonPayable v (by simp) hwv rd).reEquivExecutionRevert
      hcode hd hdec (bodyReverts_nonPayable hwv)
  by_cases hhi : I.calldata.size < 2 ^ 255 + 4
  case neg =>
    exact (eip712RevertHuge v (by simp) hwv (by omega) hsize rd).reEquivExecutionRevert
      hcode hd hdec
      (bodyReverts_calldataBound "__calldata" (2 ^ 255 + 4) hwv (Nat.le_of_not_gt hhi))
  obtain ⟨aw1, k1, C1, h1⟩ := eip712ReachName v (by simp) hwv hsz hhi hsize rd
  by_cases hname : domainStringValid v false evm
  case neg =>
    exact (domainStringRevertsInvalid (evm := evm) v false 128 (by simp)
      solcFreePtrMem_mload64 hname h1).reEquivExecutionRevert hcode hd hdec
        (eip712RevertsName evm v hwv hhi hname)
  by_cases hnameFit : eip712NameEnd evm v < 2 ^ 64
  case neg =>
    exact (domainStringRevertsAllocation (evm := evm) v false 128 (by simp) (by decide)
      solcFreePtrMem_mload64 hname hnameFit h1).reEquivExecutionRevert hcode hd hdec
        (eip712RevertsNameAllocation evm v hwv hhi hname hnameFit)
  obtain ⟨mem1, aw2, k2, C2, h2, hnameBuffer1, _, hptr1, _⟩ :=
    domainStringReturn (evm := evm) v false 128 (by simp) (by decide) (by decide) hsize
      solcFreePtrMem_mload64 hname hnameFit
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  have hnlo : 96 ≤ eip712NameEnd evm v := by
    have hlow : 128 + 32 ≤ eip712NameEnd evm v := domainStringEnd_ge evm v false 128
    omega
  obtain ⟨aw3, k3, C3, h3⟩ := eip712ReachVersion v (by simp) h2
  by_cases hversion : domainStringValid v true evm
  case neg =>
    exact (domainStringRevertsInvalid (evm := evm) v true (eip712NameEnd evm v) (by simp)
      hptr1 hversion h3).reEquivExecutionRevert hcode hd hdec
        (eip712RevertsVersion evm v hwv hhi hname hnameFit hversion)
  by_cases hversionFit : eip712VersionEnd evm v < 2 ^ 64
  case neg =>
    exact (domainStringRevertsAllocation (evm := evm) v true (eip712NameEnd evm v) (by simp)
      hnameFit hptr1 hversion hversionFit h3).reEquivExecutionRevert hcode hd hdec
        (eip712RevertsVersionAllocation evm v hwv hhi hname hnameFit hversion hversionFit)
  obtain ⟨mem2, aw4, k4, C4, h4, hversionBuffer2, hprefix2, hptr2, _⟩ :=
    domainStringReturn (evm := evm) v true (eip712NameEnd evm v) (by simp) hnlo hnameFit hsize
      hptr1 hversion hversionFit
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h3
  obtain ⟨aw5, k5, C5, h5⟩ := eip712ReachExtensionsAllocation v (eip712VersionEnd evm v)
    (by simp) hptr2 h4
  by_cases hextensionsFit : eip712VersionEnd evm v + 32 < 2 ^ 64
  case neg =>
    have hbad : ¬ allocationFits (UInt256.ofNat (eip712VersionEnd evm v)) ⟨32⟩ :=
      fun hfit ↦ hextensionsFit ((eip712ExtensionsAllocationFits evm v hversionFit).mp hfit)
    exact (allocateRoundedRevert v (by simp) hbad h5).reEquivExecutionRevert hcode hd hdec
      (eip712RevertsExtensions evm v hwv hhi hname hnameFit hversion hversionFit hextensionsFit)
  have hnameCover : 128 + 32 + paddedSize (domainStringBytes v false evm).size ≤
      eip712NameEnd evm v := domainStringEnd_covers evm v false 128 hname
  have hversionCover : eip712NameEnd evm v + 32 + paddedSize (domainStringBytes v true evm).size ≤
      eip712VersionEnd evm v := domainStringEnd_covers evm v true (eip712NameEnd evm v) hversion
  have hvlo : 96 ≤ eip712VersionEnd evm v := by omega
  have hnameBuffer2 := hnameBuffer1.preserve hprefix2 (by decide) (by decide) hnameCover
  obtain ⟨aw6, k6, C6, h6⟩ := eip712ExtensionsReachEncoder v (eip712VersionEnd evm v)
    (by simp) hvlo hextensionsFit h5
  have hp := eip712ExtensionsMemory_prefix mem2 (eip712VersionEnd evm v)
  have hnameBuffer3 := hnameBuffer2.preserve hp (by decide) (by decide) (by omega)
  have hversionBuffer3 := hversionBuffer2.preserve hp hnlo
    (lt_trans hnameFit (by decide)) hversionCover
  have hret := eip712EncodeReturn v (domainStringBytes v false evm) (domainStringBytes v true evm)
    128 (eip712NameEnd evm v) (eip712VersionEnd evm v) (eip712VersionEnd evm v + 32)
    (by simp) (domainStringBytes_bound evm v false) (domainStringBytes_bound evm v true)
    (by change _ < 2 ^ 256; omega) (by decide) hnlo hvlo (by omega) (by omega) (le_refl _)
    (eip712ExtensionsMemory_size mem2 _) hnameBuffer3 hversionBuffer3
    (eip712ExtensionsMemory_length mem2 _ (lt_trans hversionFit (by decide))) h6
  exact hret.reEquivExecutionGen hcode hd hdec
    (eip712BodyReturns evm v hwv hhi hname hnameFit hversion hversionFit hextensionsFit) rfl
    (returnEquiv.returned rfl (eip712ReturnEncoding evm v))

end Benchmarks.Morpho.MetaMorphoV1_1
