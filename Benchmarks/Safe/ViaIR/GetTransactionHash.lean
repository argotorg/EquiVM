import Benchmarks.Safe.ViaIR.Dispatch
import Benchmarks.Safe.ViaIR.TransactionArgsDecoder
import Benchmarks.Safe.ViaIR.TransactionCalldata
import Benchmarks.Safe.ViaIR.TransactionHashTrace
import Benchmarks.Safe.ViaIR.TransactionHashBody
import Benchmarks.Safe.ViaIR.Routines
import Benchmarks.Safe.ViaIR.Blocks.Runtime_011
import Benchmarks.Safe.ViaIR.Blocks.Runtime_012

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

set_option maxRecDepth 2000 in
theorem safeGetTransactionHashTrace (tx : SafeTransaction)
    {I g s0 σ k C aw rdata} {off : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9040⟩
      (UInt256.ofNat tx.target.val :: tx.value :: off :: UInt256.ofNat tx.payload.size ::
        tx.operation :: tx.safeTxGas :: tx.baseGas :: tx.gasPrice ::
        UInt256.ofNat tx.gasToken.val :: UInt256.ofNat tx.refundReceiver.val ::
        tx.nonce :: ⟨1055⟩ :: ⟨32⟩ :: R) solcFreePtrMem aw rdata σ k C)
    (hn : tx.payload.size < UInt256.size)
    (hi : off.toNat + tx.payload.size ≤ I.calldata.size)
    (hd : I.calldata.extract off.toNat (off.toNat + tx.payload.size) = tx.payload)
    (hov : R.length + 21 ≤ 1024) :
    RDret fork safeBytecode g s0 σ (transactionWord I tx).toByteArray := by
  obtain ⟨_, _, _, hr⟩ := safeTransactionHashTrace tx h solcFreePtrMem_mload64
    (by rw [solcFreePtrMem_size]) (by decide) (by decide) hn hi hd (by simp; omega) (by jump_dest)
  let mem := transactionHashMemory solcFreePtrMem 128 I off tx
  have hm : 128 ≤ mem.size := by
    dsimp only [mem, transactionHashMemory]
    rw [transactionFinalMemory_size]
    omega
  have hf : memLoad ⟨64⟩ mem = ⟨128⟩ :=
    transactionHashMemory_free solcFreePtrMem_mload64 (by rw [solcFreePtrMem_size])
      (by decide) hi
  exact safeReturnWordFromMem hr (by omega) hf (toByteArray_write32_read_back _ _ _ hm)

set_option maxRecDepth 2000 in
theorem safeGettransactionhashBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some gettransactionhashTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xd8 0xd1 0x1f 0x78 ⟨0xd8d11f78⟩
    hdispatch gettransactionhashSelectorBytes (by decide)
  obtain ⟨k, C, hentry⟩ := safeReachEntry (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0xd8d11f78⟩ 20 ⟨2246⟩ hcode hsize hlong hword (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  swap
  · have h₁ := safeRuntime_block_2246_taken (by simp) hvalue (by jump_dest) hentry
    have hr := safeRuntime_block_589 (by simp) h₁
    exact reEquivSelectorRevert hcode hdispatch hr fun _ ↦ bodyReverts_nonPayable hvalue
  have hdecode := safeRuntime_block_2246_fallthrough (by simp) hvalue hentry
  let evm := initState σ σ₀ (.ofUInt256 g) A I
  cases hdec : decodeCalldata transactionCalldataNames transactionCalldataTypes I.calldata with
  | none =>
    have hr : RDrev fork safeBytecode (.ofUInt256 g) evm := by
      rcases safeDecodeTransactionArgsEvidence hdecode hlong hsize (by simp) with
        hr | ⟨len, k', C', hh, hs, hc, hoff, hw, hn, hin, ho, hgas, href, hr⟩
      · exact hr
      have hd := decodeTransactionCalldataValid hh hs hc hoff hw hn hin (by omega) hgas href
      rw [hdec] at hd
      cases hd
    exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch hdec hr
  | some args =>
    obtain ⟨len, hh, hs, hc, hoff, hw, hn, hin, hop, hgas, href, rfl⟩ :=
      decodeTransactionCalldataEvidence hlong hdec
    let payload := I.calldata.extract (4 + (calldataWord I.calldata 68).toNat + 32)
      (4 + (calldataWord I.calldata 68).toNat + 32 + len)
    let tx := transactionFromCalldata I.calldata payload
    have hlen : payload.size = len := by
      dsimp only [payload]
      rw [ByteArray.size_extract]; omega
    have hdec' : config.externalABI.decodeCalldata?
        (gettransactionhashTransition.params.map Param.name)
        (transitionSignature gettransactionhashTransition).paramTypes I.calldata =
        some (transactionArgs tx) := hdec
    by_cases ho : (calldataWord I.calldata 100).toNat < 2
    · obtain ⟨k₂, C₂, h₂⟩ := safeDecodeTransactionArgsValid hdecode hh hs hc hoff hw hn hin ho
        hgas href (by simp)
      have ht : UInt256.ofNat tx.target.val = calldataWord I.calldata 4 := by
        exact addressWord_eq_ofNat_address hc
      have hg : UInt256.ofNat tx.gasToken.val = calldataWord I.calldata 228 := by
        exact addressWord_eq_ofNat_address hgas
      have hr : UInt256.ofNat tx.refundReceiver.val = calldataWord I.calldata 260 := by
        exact addressWord_eq_ofNat_address href
      have hnat : (UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat + 32)).toNat =
          4 + (calldataWord I.calldata 68).toNat + 32 :=
        ulit_toNat' _ (by change _ < 2 ^ 256; omega)
      have htrace : RD fork safeBytecode I (.ofUInt256 g) evm ⟨9040⟩
          (UInt256.ofNat tx.target.val :: tx.value ::
            UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat + 32) ::
            UInt256.ofNat tx.payload.size :: tx.operation :: tx.safeTxGas :: tx.baseGas ::
            tx.gasPrice :: UInt256.ofNat tx.gasToken.val ::
            UInt256.ofNat tx.refundReceiver.val :: tx.nonce :: ⟨1055⟩ :: ⟨32⟩ :: ⟨0⟩ ::
            UInt256.ofNat len :: UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat + 32) ::
            calldataWord I.calldata 4 :: calldataWord I.calldata 100 :: [])
          solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k₂ C₂ := by
        rw [ht, hg, hr]
        simpa only [tx, transactionFromCalldata, hlen, transactionArgsStack] using h₂
      have hret := safeGetTransactionHashTrace tx htrace
        (by change payload.size < UInt256.size; rw [hlen]; change len < 2 ^ 256; omega)
        (by change _ + payload.size ≤ _; rw [hnat, hlen]; exact hin)
        (by change I.calldata.extract _ (_ + payload.size) = payload; rw [hnat, hlen])
        (by simp)
      have hbody := safeTransactionHashBody (fork := fork) (evm := evm) (tx := tx) hvalue ho
      exact RDret.reEquivElim hcode hret fun _ _ hΞ ↦
        reEquivSelectorExecution hdispatch hdec' hbody
          (.success hΞ rfl rfl (.abi (returnEquiv_of_encode (bytes32ReturnEncoding _))))
    · have hr : RDrev fork safeBytecode (.ofUInt256 g) evm := by
        rcases safeDecodeTransactionArgsEvidence hdecode hlong hsize (by simp) with
          hr | ⟨len', k', C', hh', hs', hc', hoff', hw', hn', hin', ho', hgas', href', hr⟩
        · exact hr
        exact (ho ho').elim
      exact RDrev.reEquivElim hcode hr fun _ _ hΞ ↦
        reEquivSelectorExecution hdispatch hdec' (safeTransactionHashInvalid ho) (.revert hΞ rfl)

/-- Refinement obligation for `getTransactionHash` (`gettransactionhashTransition`). -/
theorem safeGettransactionhashRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some gettransactionhashTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  exact safeGettransactionhashBodyCore hcode hsize hdispatch

end Benchmarks.Safe.ViaIR
