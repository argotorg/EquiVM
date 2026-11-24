import Benchmarks.EAS.EAS.MultiDelegatedAttestFieldsSource
import Benchmarks.EAS.EAS.DelegatedAttestationBatch

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

set_option maxHeartbeats 500000 in
theorem multiDelegatedAttestFieldsReadySource {L imms : Store} {evm : EVM.State} {cd : ByteArray} {root : UInt256}
    (hr : L.get? "multiDelegatedRequest"=some (delegatedAttestationTuple cd root)) :
    (DelegatedAttestationBatchReady cd root →
      ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm multiDelegatedAttestFields
        (.ok {contract := contract,locals := multiDelegatedAttestFieldLocals L (delegatedAttestationDataList cd root) (delegatedAttestationSigList cd root),immutables := imms} evm)) ∧
    (¬DelegatedAttestationBatchReady cd root →
      ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm multiDelegatedAttestFields .reverted) := by
  have hsrc := multiDelegatedAttestFieldsSource (fork := fork) (imms := imms) (evm := evm)
    (data := delegatedAttestationDataList cd root) (sigs := delegatedAttestationSigList cd root)
    (delegatedAttestationArrayReferenceValid cd root 32 ∧ referencedArrayHeadValid cd (delegatedBatchArray cd root 32) 32)
    (delegatedAttestationArrayReferenceValid cd root 64 ∧ referencedArrayHeadValid cd (delegatedBatchArray cd root 64) 96) hr
  have hiff : ((delegatedAttestationArrayReferenceValid cd root 32 ∧ referencedArrayHeadValid cd (delegatedBatchArray cd root 32) 32) ∧
      0<(delegatedAttestationDataList cd root).length ∧
      (delegatedAttestationArrayReferenceValid cd root 64 ∧ referencedArrayHeadValid cd (delegatedBatchArray cd root 64) 96) ∧
      (delegatedAttestationDataList cd root).length=(delegatedAttestationSigList cd root).length) ↔ DelegatedAttestationBatchReady cd root := by
    rw [← delegatedAttestationRequestAccess,← delegatedAttestationSignatureAccess,delegatedAttestationDataList_length,delegatedAttestationSigList_length]
    constructor
    · rintro ⟨hd,hn,hs,he⟩
      exact ⟨hd,hs,hn,u256_inj he⟩
    · intro h
      exact ⟨h.data,h.nonempty,h.signatures,congrArg UInt256.toNat h.lengths⟩
  constructor
  · intro hv
    simpa only [if_pos (hiff.mpr hv)] using hsrc
  · intro hv
    simpa only [if_neg (fun h => hv (hiff.mp h))] using hsrc

end Benchmarks.EAS.EAS
