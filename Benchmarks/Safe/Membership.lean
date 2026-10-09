import Benchmarks.Safe.Storage
import Benchmarks.Safe.Decoders

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def addressMembership (key next : UInt256) : Bool :=
  decide (next ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩)

-- LIBRARY CANDIDATE: a canonical address is nonzero exactly when its word is nonzero.
theorem evalAddressNonzero {cfg : Config} {frame : Frame} {evm : EVM.State}
    {expr : Expr} {w : UInt256} (hcanon : w.toNat < EVM.addressModulus)
    (heval : evalExpr? cfg frame evm expr = .ok (.address (AccountAddress.ofNat w.toNat))) :
    evalExpr? cfg frame evm (neE expr zeroAddr) = .ok (.bool (decide (w ≠ ⟨0⟩))) := by
  rw [neE, evalExpr_binary_nonshort (by decide) (by decide), heval]
  simp [zeroAddr, addrSt, evalExpr?, castValue?, evalBinaryOpNeAddress,
    EvalResult.bind, EvalResult.ofOption, bind, pure]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.address.injEq, decide_eq_true_eq,
    canonicalAddress_eq_zero_iff w hcanon]

-- LIBRARY CANDIDATE: address comparisons in a sentinel-based linked-list mapping.
theorem evalAddressMembership {cfg : Config} {frame : Frame} {evm : EVM.State}
    {keyExpr nextExpr : Expr} {key next : UInt256}
    (hkey : key.toNat < EVM.addressModulus)
    (hnext : next.toNat < EVM.addressModulus)
    (hk : evalExpr? cfg frame evm keyExpr =
      .ok (.address (AccountAddress.ofNat key.toNat)))
    (hn : evalExpr? cfg frame evm nextExpr =
      .ok (.address (AccountAddress.ofNat next.toNat))) :
    evalExpr? cfg frame evm (andE (neE nextExpr zeroAddr) (neE keyExpr sentinelAddr)) =
      .ok (.bool (addressMembership key next)) := by
  have hzero := canonicalAddress_eq_zero_iff next hnext
  have hone : AccountAddress.ofNat key.toNat = AccountAddress.ofNat 1 ↔ key = ⟨1⟩ := by
    simpa only [accountAddress_ofUInt256_eq_ofNat_toNat,
      show (⟨1⟩ : UInt256).toNat = 1 by rfl] using
      accountAddress_ofUInt256_eq_iff_of_canonical (b := ⟨1⟩) hkey (by decide)
  have hn' : evalExpr? cfg frame evm (neE nextExpr zeroAddr) =
      .ok (.bool (decide (next ≠ ⟨0⟩))) := by
    rw [neE, evalExpr_binary_nonshort (by decide) (by decide), hn]
    simp [zeroAddr, addrSt, evalExpr?, castValue?, evalBinaryOpNeAddress,
      EvalResult.bind, EvalResult.ofOption, bind, pure]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, Value.address.injEq, decide_eq_true_eq, hzero]
  have hk' : evalExpr? cfg frame evm (neE keyExpr sentinelAddr) =
      .ok (.bool (decide (key ≠ ⟨1⟩))) := by
    rw [neE, evalExpr_binary_nonshort (by decide) (by decide), hk]
    simp [sentinelAddr, addrSt, evalExpr?, castValue?, evalBinaryOpNeAddress,
      EvalResult.bind, EvalResult.ofOption, bind, pure]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, Value.address.injEq, decide_eq_true_eq, hone]
  unfold andE
  rw [evalExpr?, hn']
  by_cases h : next = ⟨0⟩ <;>
    simp [h, addressMembership, hk', EvalResult.bind, bind, pure]

-- GENERALIZES twoWordHashMemMapSlot to every initial memory size.
theorem twoWordHashMemMapSlotAny (key slot : UInt256) (mem : ByteArray) :
    keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem key slot mem) = mapSlot key slot := by
  simp only [keccakWord, show (⟨0⟩ : UInt256).toNat = 0 by rfl,
    show (UInt256.ofNat 64).toNat = 64 by rfl,
    twoWordHashMem_read0_64_any key slot mem, mapSlot, uInt256OfByteArray_eq]

theorem twoWordHashMemMapSlot (key slot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem key slot mem) = mapSlot key slot :=
  twoWordHashMemMapSlotAny key slot mem

theorem normalizedNonzeroWord (w : UInt256) :
    UInt256.isZero (UInt256.isZero w) = (decide (w ≠ ⟨0⟩)).toUInt256 := by
  by_cases h : w = ⟨0⟩
  · subst w; rfl
  · rw [isZero_eq_zero_of_ne h]
    simp [h]; rfl

end Benchmarks.Safe
