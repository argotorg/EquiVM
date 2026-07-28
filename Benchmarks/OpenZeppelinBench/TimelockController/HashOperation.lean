import Benchmarks.OpenZeppelinBench.TimelockController.SolmDispatch
import Benchmarks.OpenZeppelinBench.TimelockController.AbiEncode
import Benchmarks.OpenZeppelinBench.TimelockController.AbiDecode
import Benchmarks.OpenZeppelinBench.TimelockController.Body
import Benchmarks.OpenZeppelinBench.TimelockController.EvmReach
import Benchmarks.OpenZeppelinBench.TimelockController.EvmExec
import Benchmarks.OpenZeppelinBench.TimelockController.EvmReverts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace OpenZeppelinBench.TimelockController

/-- KECCAK round-trip: the Solm `bytes32` result bytes equal the big-endian bytes of the EVM word. -/
theorem tlcHashOp_kec_roundtrip (I : ExecutionEnv) :
    tlcHashOpKecList I = EVM.Word.toBytesBE (tlcHashOpKecWord I) := by
  show (ffi.KEC (tlcHashOpCanonBytes I)).toList
    = EVM.Word.toBytesBE (UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (tlcHashOpCanonBytes I))))
  rw [← uInt256OfByteArray_eq, toBytesBE_uInt256OfByteArray_of_size (keccak_size _)]

/-! ## Refinement (target) -/

/-- Refinement of `hashOperation` (selector index 13).  The EVM decodes
    `(address,uint256,bytes,bytes32,bytes32)`, ABI-re-encodes the canonical tuple, and returns its
    `keccak256`; the Solm body returns the same `keccak256(abi.encode(...))`.  Malformed calldata and
    nonzero callvalue both revert on both sides. -/
theorem tlcHashOperationBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I (tlcSelBytes 13))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (tlcSelBytes 13) (by native_decide) hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hwf : tlcHashOpWF I
    · -- well-formed: execute; both sides return `keccak256(canonical abi.encode)`
      exact tlcReEquivExecTransport hcode
        (tlcHashOperationX_ok (g := Sat256.ofUInt256 g) hcode hwv hsize hsel hwf)
        (tlcSelectorDispatchHashOperation hsel) (tlcDecodeHashOperation_ok hwf)
        (tlcHashOperationBodyReturns (g := Sat256.ofUInt256 g) hwv hwf)
        (by rw [tlcHashOp_kec_roundtrip]) hAccounts
        (returnEquiv_of_encode
          (by simpa [bytes32] using bytes32ReturnEncoding (tlcHashOpKecWord I)))
    · -- malformed calldata: EVM decoder reverts, Solm decode fails
      exact tlcHashOperationDecodeFail hcode hwv hsz hsize hsel hwf hAccounts
  · -- nonzero callvalue: EVM reverts at the per-function non-payable guard, Solm body reverts
    obtain ⟨_, _, h988⟩ := tlcReachHashOperation (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
    have hrev := tlcGuardPeelRev (gt := ⟨999⟩) h988 hwv (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
    exact tlcNonpayableRevert hcode hrev (tlcSelectorDispatchHashOperation hsel)
      (fun callargs _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end OpenZeppelinBench.TimelockController
