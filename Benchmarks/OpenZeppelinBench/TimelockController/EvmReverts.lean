import Benchmarks.OpenZeppelinBench.TimelockController.EvmReach
import Benchmarks.OpenZeppelinBench.TimelockController.SolmDispatch
import Benchmarks.OpenZeppelinBench.TimelockController.AbiDecode

/-!
# OpenZeppelin TimelockController `hashOperation` EVM revert paths (malformed calldata)

`tlcHashOperationDecodeFail`: when the calldata is not well-formed (`¬ tlcHashOpWF I`) and callvalue
is zero, the EVM external decoder reverts at one of its four checks (short head / dirty address /
bytes-offset > 2^64 / bytes length-or-payload OOB) and the Solm `decodeCalldata` returns `none`
(the `tlcDecodeHashOperation_none_*` lemmas), routed through `tlcReEquivDecodeFailed`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace OpenZeppelinBench.TimelockController

/-! ## Shared decoder reach-checkpoints (from pc 4600, the 5-arg external decoder) -/

/-- Pass the head-length check `SLT(size-4, 160)=0` @4617: reach pc 4621. -/
private theorem tlcHashOpReach4621 {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (rd : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4600⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨1014⟩, ⟨581⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hc1 : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨160⟩ = ⟨0⟩) :
    ∃ k' C', RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4621⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨1014⟩, ⟨581⟩,
        tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push0, push0, push0, push0, push1 ⟨160⟩, dup8, dup10, sub, slt,
    iszero, push2 ⟨4621⟩, jumpiT (by rw [hc1]; decide) (by jump_dest)]⟩

/-- Pass the head check and the address canonicalization subroutine (`EQ(w4, w4∧mask)=1` @4374,
    clean address): reach pc 4630 with the decoded address word on top. -/
private theorem tlcHashOpReach4630 {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (rd : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4600⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨1014⟩, ⟨581⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hc1 : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨160⟩ = ⟨0⟩)
    (hclean : (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    ∃ k' C', RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4630⟩
      [uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32),
        ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨1014⟩, ⟨581⟩,
        tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, h4621⟩ := tlcHashOpReach4621 rd hc1
  have hcleanEq : UInt256.eq (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
      (UInt256.land (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)) ≠ ⟨0⟩ := by
    rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask from by decide,
      solcAddrCanon_eq hclean]
    decide
  exact ⟨_, _, evm_run h4621 with [
    jumpdest, push2 ⟨4630⟩, dup8, push2 ⟨4356⟩, jump (by jump_dest),
    jumpdest, dup1, calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, dup2, eq,
    push2 ⟨4378⟩, jumpiT hcleanEq (by jump_dest),
    jumpdest, swap2, swap1, pop, jump (by jump_dest)]⟩

/-- Pass the head + address + `bytes` offset checks (`GT(off, 2^64-1)=0` @4659, `off ≤ 2^64-1`):
    reach pc 4663 with the offset word on top. -/
private theorem tlcHashOpReach4663 {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (rd : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4600⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨1014⟩, ⟨581⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hc1 : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨160⟩ = ⟨0⟩)
    (hclean : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hoffMax : tlcHashOpArgOff I ≤ solcMaxU64) :
    ∃ k' C', RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4663⟩
      [uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨64⟩).toNat 32),
        ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨32⟩).toNat 32),
        uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32),
        ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨1014⟩, ⟨581⟩,
        tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, h4630⟩ := tlcHashOpReach4630 rd hc1 hclean
  have hgt0 : UInt256.gt (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨64⟩).toNat 32))
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨0⟩ := by
    apply ugt_zero
    rw [show (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩).toNat = solcMaxU64 from
        by decide,
      show ((⟨4⟩ : UInt256) + ⟨64⟩).toNat = 68 from by decide]
    exact hoffMax
  exact ⟨_, _, evm_run h4630 with [
    jumpdest, swap6, pop, push1 ⟨32⟩, dup8, add, calldataload, swap5, pop, push1 ⟨64⟩, dup8, add,
    calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup2, gt, iszero, push2 ⟨4663⟩,
    jumpiT (by rw [hgt0]; decide) (by jump_dest)]⟩

/-- Pass head + address + offset + the `bytes` length-word availability check
    (`SLT(4+off+31, size)=1` @4395, `4+off+32 ≤ size < 2^255`): reach pc 4399, inside the
    length-decoder subroutine, past the availability check. -/
private theorem tlcHashOpReach4399 {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (rd : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4600⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨1014⟩, ⟨581⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hc1 : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨160⟩ = ⟨0⟩)
    (hclean : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hoffMax : tlcHashOpArgOff I ≤ solcMaxU64) (hsmall : I.calldata.size < 2 ^ 255)
    (hlenWord : 4 + tlcHashOpArgOff I + 32 ≤ I.calldata.size) :
    ∃ k' C', RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4399⟩
      [⟨0⟩, ⟨0⟩,
        (⟨4⟩ : UInt256) + uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨64⟩).toNat 32),
        UInt256.ofNat I.calldata.size, ⟨4675⟩,
        uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨64⟩).toNat 32),
        ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨32⟩).toNat 32),
        uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32),
        ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨1014⟩, ⟨581⟩,
        tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, h4663⟩ := tlcHashOpReach4663 rd hc1 hclean hoffMax
  have hw68 : (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨64⟩).toNat 32)).toNat
      = tlcHashOpArgOff I := by
    rw [show ((⟨4⟩ : UInt256) + ⟨64⟩).toNat = 68 from by decide]
  have hbound : ((⟨4⟩ : UInt256)
      + uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨64⟩).toNat 32) + ⟨31⟩).toNat
      = 4 + tlcHashOpArgOff I + 31 := by
    rw [uadd_toNat, uadd_toNat, hw68, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨31⟩ : UInt256).toNat = 31 from by decide]
    have hmax : solcMaxU64 = 18446744073709551615 := by decide
    have hleft : (4 + tlcHashOpArgOff I) % UInt256.size = 4 + tlcHashOpArgOff I :=
      Nat.mod_eq_of_lt (by rw [show UInt256.size = 2 ^ 256 from rfl]; omega)
    rw [hleft]
    exact Nat.mod_eq_of_lt (by rw [show UInt256.size = 2 ^ 256 from rfl]; omega)
  have hslt1 : UInt256.slt ((⟨4⟩ : UInt256)
      + uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨64⟩).toNat 32) + ⟨31⟩)
      (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
    apply slt_lit_one_low hsmall
    rw [hbound]; omega
  exact ⟨_, _, evm_run h4663 with [
    jumpdest, push2 ⟨4675⟩, dup10, dup3, dup11, add, push2 ⟨4383⟩, jump (by jump_dest),
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨4399⟩,
    jumpiT (by rw [hslt1]; decide) (by jump_dest)]⟩

/-! ## Per-case EVM reverts (each fails one decoder check via `jumpiNT` + the `PUSH0 PUSH0 REVERT`) -/

/-- Head-length check @4617 fails (`SLT(size-4,160)=1`): `size < 164` or `2^255+4 ≤ size`. -/
private theorem tlcHashOpRevCheck1 {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (rd : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4600⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨1014⟩, ⟨581⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hc1rev : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨160⟩ = ⟨1⟩) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) :=
  evm_run rd with [
    jumpdest, push0, push0, push0, push0, push0, push0, push1 ⟨160⟩, dup8, dup10, sub, slt,
    iszero, push2 ⟨4621⟩, jumpiNT (by rw [hc1rev]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

/-- Address canonicalization check @4374 fails (`EQ(w4, w4∧mask)=0`): dirty address. -/
private theorem tlcHashOpRevDirtyAddr {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (rd : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4600⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨1014⟩, ⟨581⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hc1 : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨160⟩ = ⟨0⟩)
    (hdirty : EVM.addressModulus ≤ (calldataWord I.calldata 4).toNat) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, h4621⟩ := tlcHashOpReach4621 rd hc1
  have e4 : uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)
      = calldataWord I.calldata 4 := by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]
  have hdirtyEq : UInt256.eq (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
      (UInt256.land (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)) = ⟨0⟩ := by
    rw [e4, show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask from
        by decide]
    apply uInt256_eq_zero_of_ne
    intro hone
    exact absurd (solcAddrCanonical_of_clean hone) (by omega)
  exact evm_run h4621 with [
    jumpdest, push2 ⟨4630⟩, dup8, push2 ⟨4356⟩, jump (by jump_dest),
    jumpdest, dup1, calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, dup2, eq,
    push2 ⟨4378⟩, jumpiNT (by rw [hdirtyEq]),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

/-- `bytes` offset check @4659 fails (`GT(off, 2^64-1)=1`): `off > 2^64-1`. -/
private theorem tlcHashOpRevOffset {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (rd : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4600⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨1014⟩, ⟨581⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hc1 : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨160⟩ = ⟨0⟩)
    (hclean : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hoff : solcMaxU64 < tlcHashOpArgOff I) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, h4630⟩ := tlcHashOpReach4630 rd hc1 hclean
  have hgt1 : UInt256.gt (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨64⟩).toNat 32))
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨1⟩ := by
    apply ugt_one
    rw [show (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩).toNat = solcMaxU64 from
        by decide,
      show ((⟨4⟩ : UInt256) + ⟨64⟩).toNat = 68 from by decide]
    exact hoff
  exact evm_run h4630 with [
    jumpdest, swap6, pop, push1 ⟨32⟩, dup8, add, calldataload, swap5, pop, push1 ⟨64⟩, dup8, add,
    calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup2, gt, iszero, push2 ⟨4663⟩,
    jumpiNT (by rw [hgt1]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

/-- `bytes` length-word availability check @4395 fails (`SLT(4+off+31, size)=0`, unavailable):
    `size < 4 + off + 32` (with `off ≤ 2^64-1`, `size < 2^255`). -/
private theorem tlcHashOpRevLenWord {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (rd : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4600⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨1014⟩, ⟨581⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hc1 : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨160⟩ = ⟨0⟩)
    (hclean : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hoffMax : tlcHashOpArgOff I ≤ solcMaxU64) (hsmall : I.calldata.size < 2 ^ 255)
    (hlenWordRev : I.calldata.size < 4 + tlcHashOpArgOff I + 32) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, h4663⟩ := tlcHashOpReach4663 rd hc1 hclean hoffMax
  have hw68 : (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨64⟩).toNat 32)).toNat
      = tlcHashOpArgOff I := by
    rw [show ((⟨4⟩ : UInt256) + ⟨64⟩).toNat = 68 from by decide]
  have hbound : ((⟨4⟩ : UInt256)
      + uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨64⟩).toNat 32) + ⟨31⟩).toNat
      = 4 + tlcHashOpArgOff I + 31 := by
    rw [uadd_toNat, uadd_toNat, hw68, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨31⟩ : UInt256).toNat = 31 from by decide]
    have hmax : solcMaxU64 = 18446744073709551615 := by decide
    have hleft : (4 + tlcHashOpArgOff I) % UInt256.size = 4 + tlcHashOpArgOff I :=
      Nat.mod_eq_of_lt (by rw [show UInt256.size = 2 ^ 256 from rfl]; omega)
    rw [hleft]
    exact Nat.mod_eq_of_lt (by rw [show UInt256.size = 2 ^ 256 from rfl]; omega)
  have hmax : solcMaxU64 = 18446744073709551615 := by decide
  have hsltRev : UInt256.slt ((⟨4⟩ : UInt256)
      + uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨64⟩).toNat 32) + ⟨31⟩)
      (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
    apply slt_lit_zero hsmall <;> rw [hbound] <;> omega
  exact evm_run h4663 with [
    jumpdest, push2 ⟨4675⟩, dup10, dup3, dup11, add, push2 ⟨4383⟩, jump (by jump_dest),
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨4399⟩, jumpiNT hsltRev,
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

/-- `bytes` length check @4417 fails (`GT(len, 2^64-1)=1`): `len > 2^64-1`. -/
private theorem tlcHashOpRevLenBig {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (rd : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4600⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨1014⟩, ⟨581⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hc1 : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨160⟩ = ⟨0⟩)
    (hclean : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hoffMax : tlcHashOpArgOff I ≤ solcMaxU64) (hsmall : I.calldata.size < 2 ^ 255)
    (hlenWord : 4 + tlcHashOpArgOff I + 32 ≤ I.calldata.size)
    (hlenBig : solcMaxU64 < tlcHashOpArgLen I) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, h4399⟩ := tlcHashOpReach4399 rd hc1 hclean hoffMax hsmall hlenWord
  have hw68 : (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨64⟩).toNat 32)).toNat
      = tlcHashOpArgOff I := by rw [show ((⟨4⟩ : UInt256) + ⟨64⟩).toNat = 68 from by decide]
  have h4off : ((⟨4⟩ : UInt256)
      + uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨64⟩).toNat 32)).toNat
      = 4 + tlcHashOpArgOff I := by
    rw [uadd_toNat, hw68, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    have hmax : solcMaxU64 = 18446744073709551615 := by decide
    exact Nat.mod_eq_of_lt (by rw [show UInt256.size = 2 ^ 256 from rfl]; omega)
  have hgtLen1 : UInt256.gt (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256)
        + uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨64⟩).toNat 32)).toNat 32))
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨1⟩ := by
    apply ugt_one
    rw [show (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩).toNat = solcMaxU64 from
        by decide, h4off]
    exact hlenBig
  exact evm_run h4399 with [
    jumpdest, pop, dup2, calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup2, gt,
    iszero, push2 ⟨4421⟩, jumpiNT (by rw [hgtLen1]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

/-- `bytes` payload availability check @4440 fails (`GT(4+off+32+len, size)=1`, payload OOB):
    `size < 4 + off + 32 + len` (`len ≤ 2^64-1` so the length check @4417 passes). -/
private theorem tlcHashOpRevPayload {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (rd : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4600⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨1014⟩, ⟨581⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hc1 : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨160⟩ = ⟨0⟩)
    (hclean : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hoffMax : tlcHashOpArgOff I ≤ solcMaxU64) (hsmall : I.calldata.size < 2 ^ 255)
    (hlenWord : 4 + tlcHashOpArgOff I + 32 ≤ I.calldata.size)
    (hlenMax : tlcHashOpArgLen I ≤ solcMaxU64)
    (hpay : I.calldata.size < 4 + tlcHashOpArgOff I + 32 + tlcHashOpArgLen I) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, h4399⟩ := tlcHashOpReach4399 rd hc1 hclean hoffMax hsmall hlenWord
  have hw68 : (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨64⟩).toNat 32)).toNat
      = tlcHashOpArgOff I := by rw [show ((⟨4⟩ : UInt256) + ⟨64⟩).toNat = 68 from by decide]
  have h4off : ((⟨4⟩ : UInt256)
      + uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨64⟩).toNat 32)).toNat
      = 4 + tlcHashOpArgOff I := by
    rw [uadd_toNat, hw68, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    have hmax : solcMaxU64 = 18446744073709551615 := by decide
    exact Nat.mod_eq_of_lt (by rw [show UInt256.size = 2 ^ 256 from rfl]; omega)
  have hgtLen0 : UInt256.gt (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256)
        + uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨64⟩).toNat 32)).toNat 32))
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨0⟩ := by
    apply ugt_zero
    rw [show (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩).toNat = solcMaxU64 from
        by decide, h4off]
    exact hlenMax
  have hwlen : (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256)
      + uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨64⟩).toNat 32)).toNat 32)).toNat
      = tlcHashOpArgLen I := by rw [h4off]
  have hpayNat : ((⟨4⟩ : UInt256)
      + uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨64⟩).toNat 32)
      + uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256)
          + uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨64⟩).toNat 32)).toNat 32)
      + ⟨32⟩).toNat = 4 + tlcHashOpArgOff I + tlcHashOpArgLen I + 32 := by
    rw [uadd_toNat, uadd_toNat, hwlen, h4off, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    have hmax : solcMaxU64 = 18446744073709551615 := by decide
    have hinner : (4 + tlcHashOpArgOff I + tlcHashOpArgLen I) % UInt256.size
        = 4 + tlcHashOpArgOff I + tlcHashOpArgLen I :=
      Nat.mod_eq_of_lt (by rw [show UInt256.size = 2 ^ 256 from rfl]; omega)
    rw [hinner]
    exact Nat.mod_eq_of_lt (by rw [show UInt256.size = 2 ^ 256 from rfl]; omega)
  have hpayGt1 : UInt256.gt ((⟨4⟩ : UInt256)
      + uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨64⟩).toNat 32)
      + uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256)
          + uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨64⟩).toNat 32)).toNat 32)
      + ⟨32⟩) (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
    apply ugt_one
    rw [hpayNat, ulit_toNat' I.calldata.size (by rw [show UInt256.size = 2 ^ 256 from rfl]; omega)]
    omega
  have h4421 := evm_run h4399 with [
    jumpdest, pop, dup2, calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup2, gt,
    iszero, push2 ⟨4421⟩, jumpiT (by rw [hgtLen0]; decide) (by jump_dest)]
  exact evm_run h4421 with [
    jumpdest, push1 ⟨32⟩, dup4, add, swap2, pop, dup4, push1 ⟨32⟩, dup3, dup6, add, add, gt,
    iszero, push2 ⟨4444⟩, jumpiNT (by rw [hpayGt1]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

/-- Not-well-formed calldata (with zero callvalue): the EVM external decoder reverts and the Solm
    `decodeCalldata` returns `none`. -/
theorem tlcHashOperationDecodeFail {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tlcSelBytes 13)) (hnwf : ¬ tlcHashOpWF I)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  sorry

end OpenZeppelinBench.TimelockController
