import Benchmarks.Midnight.Common
import Reasoning.ExternalCall

/-! Code-storage bytes, including the word-sized length used by EXTCODESIZE. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: code access and prefix evaluation for arbitrary account maps.
def externalCode (accounts : AccountMap) (target : UInt256) : ByteArray :=
  (accounts.get? (AccountAddress.ofUInt256 target)).option .empty (·.code)

def externalCodePrefix (accounts : AccountMap) (target : UInt256) : ByteArray :=
  (externalCode accounts target).extract 0 (extCodeSizeWord accounts target).toNat

theorem extCodeSizeWord_externalCode (accounts : AccountMap) (target : UInt256) :
    extCodeSizeWord accounts target = UInt256.ofNat (externalCode accounts target).size := by
  unfold extCodeSizeWord externalCode
  cases accounts.get? (AccountAddress.ofUInt256 target) <;> rfl

theorem externalCodePrefix_size (accounts : AccountMap) (target : UInt256) :
    (externalCodePrefix accounts target).size = (extCodeSizeWord accounts target).toNat := by
  have hle : (extCodeSizeWord accounts target).toNat ≤ (externalCode accounts target).size := by
    rw [extCodeSizeWord_externalCode]
    exact Nat.mod_le _ _
  simp only [externalCodePrefix, ByteArray.size_extract, Nat.sub_zero, Nat.min_eq_left hle]

theorem evalExternalCodePrefix {cfg : Config} {frame : Frame} {evm : State}
    {expr : Expr} {target : UInt256}
    (h : evalExpr? cfg frame evm expr = .ok (.address (AccountAddress.ofUInt256 target))) :
    evalExpr? cfg frame evm (.extCodePrefix expr (.extCodeSize expr)) =
      .ok (.bytes (externalCodePrefix evm.accountMap target)) := by
  have hs := extCodeSource (σ := evm.accountMap) rfl h
  simp only [evalExpr?, h, hs, bind, EvalResult.bind, pure]
  simp only [Int.ofNat_eq_natCast]
  rw [if_neg (by omega)]
  simp only [Int.toNat_natCast, State.lookupAccount]
  change EvalResult.ok (Value.bytes (externalCodePrefix evm.accountMap target ++
    ByteArray.mk (Array.replicate ((extCodeSizeWord evm.accountMap target).toNat -
      (externalCodePrefix evm.accountMap target).size) 0))) = _
  rw [externalCodePrefix_size, Nat.sub_self]
  change EvalResult.ok (Value.bytes (externalCodePrefix evm.accountMap target ++ ByteArray.empty)) = _
  rw [ByteArray.append_empty]

theorem accountAddress_mask (word : UInt256) :
    AccountAddress.ofUInt256 (UInt256.land solcAddrMask word) = AccountAddress.ofUInt256 word := by
  rw [← accountAddressOfNat_word_eq_mask, accountAddress_roundtrip,
    accountAddress_ofUInt256_eq_ofNat_toNat]

theorem extCodeSizeWord_mask (accounts : AccountMap) (word : UInt256) :
    extCodeSizeWord accounts (UInt256.land solcAddrMask word) = extCodeSizeWord accounts word := by
  simp only [extCodeSizeWord, accountAddress_mask]

theorem externalCode_mask (accounts : AccountMap) (word : UInt256) :
    externalCode accounts (UInt256.land solcAddrMask word) = externalCode accounts word := by
  simp only [externalCode, accountAddress_mask]

end Benchmarks.Midnight
