import Benchmarks.Safe.Dispatch
import Benchmarks.Safe.TransactionArgsDecoder
import Benchmarks.Safe.TransactionCalldata
import Benchmarks.Safe.TransactionHashTrace
import Benchmarks.Safe.TransactionHashBody
import Benchmarks.Safe.Routines
import Benchmarks.Safe.Blocks.Runtime_011

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

set_option maxRecDepth 100000 in
theorem safeGetTransactionHashTrace (tx : SafeTransaction)
    {I g s0 σ k C aw rdata} {off : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨5311⟩
      (tx.nonce :: UInt256.ofNat tx.refundReceiver.val :: UInt256.ofNat tx.gasToken.val ::
        tx.gasPrice :: tx.baseGas :: tx.safeTxGas :: tx.operation ::
        UInt256.ofNat tx.payload.size :: off :: tx.value :: UInt256.ofNat tx.target.val ::
        ⟨974⟩ :: R) solcFreePtrMem aw rdata σ k C)
    (hn : tx.payload.size < UInt256.size)
    (hi : off.toNat + tx.payload.size ≤ I.calldata.size)
    (hd : I.calldata.extract off.toNat (off.toNat + tx.payload.size) = tx.payload)
    (hov : R.length + 20 ≤ 1024) :
    RDret safeBytecode g s0 σ (transactionWord I tx).toByteArray := by
  obtain ⟨_, _, _, hr⟩ := safeTransactionHashTrace tx h solcFreePtrMem_mload64
    (by rw [solcFreePtrMem_size]) (by decide) (by decide) hn hi hd hov (by jump_dest)
  let mem := transactionHashMemory solcFreePtrMem 128 I off tx
  have hm : 128 ≤ mem.size := by
    dsimp only [mem, transactionHashMemory]
    rw [transactionFinalMemory_size]
    omega
  have hf : memLoad ⟨64⟩ mem = ⟨128⟩ :=
    transactionHashMemory_free solcFreePtrMem_mload64 (by rw [solcFreePtrMem_size])
      (by decide) hi
  apply safeReturnWordFromMem hr (by omega) hf
  · change memLoad ⟨64⟩ (writeWord mem 128 (transactionWord I tx)) = ⟨128⟩
    rw [memLoadReadWord, show (⟨64⟩ : UInt256).toNat = 64 by rfl,
      writeWordReadBelow _ _ _ _ _ (by omega) (by decide)]
    exact (memLoadReadWord mem ⟨64⟩).symm.trans hf
  · exact toByteArray_write32_read_back _ _ _ hm

set_option maxRecDepth 100000 in
theorem safeGettransactionhashBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some gettransactionhashTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xd8 0xd1 0x1f 0x78 ⟨0xd8d11f78⟩
    hdispatch gettransactionhashSelectorBytes (by decide)
  obtain ⟨k, C, hentry⟩ := safeReachEntry (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0xd8d11f78⟩ 1 ⟨1346⟩ hcode hsize hlong hword (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  swap
  · have h₁ := safeRuntime_block_1346_fallthrough (by simp) (isZero_eq_zero_of_ne hvalue) hentry
    have hr := safeRuntime_block_1354 (by simp [safeRuntime_block_1346_fallthrough_stack]) h₁
    exact reEquivSelectorRevert hcode hdispatch hr fun _ ↦ bodyReverts_nonPayable hvalue
  have h₁ := safeRuntime_block_1346_taken (by simp) (by rw [hvalue]; decide)
    (by jump_dest) hentry
  have hdecode := safeRuntime_block_1357 (by simp) (by jump_dest) h₁
  let evm := initState σ σ₀ (.ofUInt256 g) A I
  cases hdec : decodeCalldata transactionCalldataNames transactionCalldataTypes I.calldata with
  | none =>
    have hr : RDrev safeBytecode (.ofUInt256 g) evm := by
      rcases safeDecodeTransactionArgsEvidence hdecode hlong hsize (by simp) (by jump_dest) with
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
    have hdec' : decodeCalldataWithMode config.abiDecodeMode
        (gettransactionhashTransition.params.map Param.name)
        (transitionSignature gettransactionhashTransition).paramTypes I.calldata =
        some (transactionArgs tx) := hdec
    by_cases ho : (calldataWord I.calldata 100).toNat < 2
    · obtain ⟨k₂, C₂, h₂⟩ := safeDecodeTransactionArgsValid hdecode hh hs hc hoff hw hn hin ho
        hgas href (by simp) (by jump_dest)
      have h₃ := safeRuntime_block_1372 (by simp) (by jump_dest) h₂
      have ht : UInt256.ofNat tx.target.val = calldataWord I.calldata 4 := by
        exact addressWord_eq_ofNat_address hc
      have hg : UInt256.ofNat tx.gasToken.val = calldataWord I.calldata 228 := by
        exact addressWord_eq_ofNat_address hgas
      have hr : UInt256.ofNat tx.refundReceiver.val = calldataWord I.calldata 260 := by
        exact addressWord_eq_ofNat_address href
      have hnat : (UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat + 32)).toNat =
          4 + (calldataWord I.calldata 68).toNat + 32 :=
        ulit_toNat' _ (by change _ < 2 ^ 256; omega)
      have htrace : RD safeBytecode I (.ofUInt256 g) evm ⟨5311⟩
          (tx.nonce :: UInt256.ofNat tx.refundReceiver.val :: UInt256.ofNat tx.gasToken.val ::
            tx.gasPrice :: tx.baseGas :: tx.safeTxGas :: tx.operation ::
            UInt256.ofNat tx.payload.size ::
            UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat + 32) :: tx.value ::
            UInt256.ofNat tx.target.val :: ⟨974⟩ :: [selWord I]) solcFreePtrMem
          (UInt256.ofNat 3) ByteArray.empty σ (k₂ + 3) (C₂ + 12) := by
        rw [ht, hg, hr]
        simpa only [tx, transactionFromCalldata, hlen] using h₃
      have hret := safeGetTransactionHashTrace tx htrace
        (by change payload.size < UInt256.size; rw [hlen]; change len < 2 ^ 256; omega)
        (by change _ + payload.size ≤ _; rw [hnat, hlen]; exact hin)
        (by change I.calldata.extract _ (_ + payload.size) = payload; rw [hnat, hlen])
        (by simp)
      have hbody := safeTransactionHashBody (evm := evm) (tx := tx) hvalue ho
      exact RDret.reEquivElim hcode hret fun _ _ hΞ ↦
        reEquivSelectorExecution hdispatch hdec' hbody
          (.success hΞ rfl rfl (.abi (returnEquiv_of_encode (bytes32ReturnEncoding _))))
    · have hr : RDrev safeBytecode (.ofUInt256 g) evm := by
        rcases safeDecodeTransactionArgsEvidence hdecode hlong hsize (by simp) (by jump_dest) with
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
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeGettransactionhashBodyCore hcode hsize hdispatch

end Benchmarks.Safe
