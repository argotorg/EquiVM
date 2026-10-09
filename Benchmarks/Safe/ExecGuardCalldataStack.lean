import Benchmarks.Safe.ExecGuardCallPrepare
import Benchmarks.Safe.ExecTransactionHashTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Safe

theorem execTransactionPayloadSize {cd : ByteArray} {dataLen sigLen : Nat}
    (hb : ExecTransactionCalldataBounds cd dataLen sigLen) :
    (execTransactionCalldataInput cd dataLen sigLen).tx.payload.size = dataLen := by
  change (cd.extract (execTransactionDataStart cd)
    (execTransactionDataStart cd + dataLen)).size = dataLen
  rw [ByteArray.size_extract]; have := hb.dataEnd; omega

theorem execTransactionSignaturesSize {cd : ByteArray} {dataLen sigLen : Nat}
    (hb : ExecTransactionCalldataBounds cd dataLen sigLen) :
    (execTransactionCalldataInput cd dataLen sigLen).signatures.size = sigLen := by
  change (cd.extract (execTransactionSignaturesStart cd)
    (execTransactionSignaturesStart cd + sigLen)).size = sigLen
  rw [ByteArray.size_extract]; have := hb.sigEnd; omega

theorem execGuardSaved_calldata {cd : ByteArray} {dataLen sigLen : Nat}
    (hb : ExecTransactionCalldataBounds cd dataLen sigLen) (ptr guard hash : UInt256)
    (R : List UInt256) :
    execGuardSaved (execTransactionCalldataInput cd dataLen sigLen)
      (execTransactionDataStart cd) ptr guard hash R =
      guard :: execSignatureSaved cd dataLen ptr hash R := by
  let p := execTransactionCalldataInput cd dataLen sigLen
  have ht : UInt256.ofNat p.tx.target.val = calldataWord cd 4 :=
    ((canonicalAddress_eq_address_iff _ _ hb.target).mp rfl).symm
  have hk : UInt256.ofNat p.tx.gasToken.val = calldataWord cd 228 :=
    ((canonicalAddress_eq_address_iff _ _ hb.gasToken).mp rfl).symm
  have hr : UInt256.ofNat p.tx.refundReceiver.val = calldataWord cd 260 :=
    ((canonicalAddress_eq_address_iff _ _ hb.refundReceiver).mp rfl).symm
  change execGuardSaved p _ _ _ _ _ = _
  rw [execGuardSaved, ht, hk, hr, execTransactionPayloadSize hb]
  rfl

end Benchmarks.Safe
