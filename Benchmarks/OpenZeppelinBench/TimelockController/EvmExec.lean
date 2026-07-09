import Benchmarks.OpenZeppelinBench.TimelockController.EvmReach
import Benchmarks.OpenZeppelinBench.TimelockController.Body
import Benchmarks.OpenZeppelinBench.TimelockController.Return

/-!
# OpenZeppelin TimelockController `hashOperation` EVM execute path (@988 → keccak → return)

`tlcHashOperationX_ok`: on well-formed calldata with zero callvalue, the runtime decodes
`(address,uint256,bytes,bytes32,bytes32)`, re-`abi.encode`s the canonical tuple into `mem[0xa0..]`,
`KECCAK256`s `mem[0xa0, 192 + roundUp₃₂ len]`, and `RETURN`s the 32-byte hash —
`= keccak256(tlcHashOpCanonBytes I)`, the same preimage as the Solm side.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace OpenZeppelinBench.TimelockController

/-- The 32-byte `hashOperation` result as an EVM word: `keccak256` of the canonical ABI encoding. -/
abbrev tlcHashOpKecWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (tlcHashOpCanonBytes I)))

/-! ## Decoder trace (988 → 1015): decode `(address,uint256,bytes,bytes32,bytes32)` -/

/-- Decoder checkpoint 4600 → 4630: length availability check + address decode (subroutine 4356). -/
private theorem tlcHashOpDecode4630 {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (hsize : I.calldata.size < UInt256.size) (hwf : tlcHashOpWF I)
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4600⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨1014⟩, ⟨581⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4630⟩
      [calldataWord I.calldata 4, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨1014⟩, ⟨581⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hslt1 : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨160⟩ = ⟨0⟩ := by
    have h := solcCalldataStaticLenCheckOk (sz := I.calldata.size) (words := 5)
      (by have := hwf.head; omega) (by have := hwf.small; omega) hsize
    simpa using h
  have hmaskEq : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by native_decide
  have hAddrCond : UInt256.eq (calldataWord I.calldata 4)
      (UInt256.land (calldataWord I.calldata 4)
        (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩)) ≠ ⟨0⟩ := by
    rw [hmaskEq, solcAddrCanon_eq hwf.clean]; decide
  exact ⟨_, _, evm_run h with [
    jumpdest, push0, push0, push0, push0, push0, push0, push1 ⟨160⟩, dup8, dup10, sub, slt, iszero,
    push2 ⟨4621⟩, jumpiT (by rw [hslt1]; decide) (by jump_dest),
    jumpdest, push2 ⟨4630⟩, dup8, push2 ⟨4356⟩, jump (by jump_dest),
    jumpdest, dup1, calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, dup2, eq,
    push2 ⟨4378⟩, jumpiT hAddrCond (by jump_dest),
    jumpdest, swap2, swap1, pop, jump (by jump_dest)]⟩

/-- Decoder checkpoint 4630 → 4664: decode value (@cd36) and bytes offset (@cd68), offset ≤ 2^64. -/
private theorem tlcHashOpDecode4664 {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (hwf : tlcHashOpWF I)
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4630⟩
      [calldataWord I.calldata 4, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨1014⟩, ⟨581⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4664⟩
      [calldataWord I.calldata 68, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, calldataWord I.calldata 36,
        calldataWord I.calldata 4, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨1014⟩, ⟨581⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hu64 : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨64⟩) ⟨1⟩ = ⟨18446744073709551615⟩ := by native_decide
  have hu64tn : (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 := rfl
  have e68 : ((⟨4⟩ : UInt256) + ⟨64⟩).toNat = 68 := by native_decide
  have hgtOff : UInt256.gt (calldataWord I.calldata 68) ⟨18446744073709551615⟩ = ⟨0⟩ :=
    ugt_zero (by rw [hu64tn]; exact hwf.offMax)
  exact ⟨_, _, evm_run h with [
    jumpdest, swap6, pop, push1 ⟨32⟩, dup8, add, calldataload, swap5, pop, push1 ⟨64⟩, dup8, add,
    calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup2, gt, iszero, push2 ⟨4663⟩,
    jumpiT (by rw [hu64, e68, hgtOff]; decide) (by jump_dest), jumpdest]⟩

/-- Decoder checkpoint 4664 → 4676: decode the dynamic `bytes` (subroutine 4383): length-word
    availability, `len ≤ 2^64`, payload availability.  Length offset normalized via `s4`. -/
private theorem tlcHashOpDecode4676 {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (hsize : I.calldata.size < UInt256.size) (hwf : tlcHashOpWF I)
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4664⟩
      [calldataWord I.calldata 68, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, calldataWord I.calldata 36,
        calldataWord I.calldata 4, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨1014⟩, ⟨581⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4676⟩
      [calldataWord I.calldata (4 + (calldataWord I.calldata 68).toNat),
        ⟨4⟩ + calldataWord I.calldata 68 + ⟨32⟩, calldataWord I.calldata 68,
        ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, calldataWord I.calldata 36, calldataWord I.calldata 4, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨1014⟩, ⟨581⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hu64 : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨64⟩) ⟨1⟩ = ⟨18446744073709551615⟩ := by native_decide
  have hu64tn : (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 := rfl
  have hoffN : (calldataWord I.calldata 68).toNat ≤ 18446744073709551615 := hwf.offMax
  have hlenWordN : 4 + (calldataWord I.calldata 68).toNat + 32 ≤ I.calldata.size := hwf.lenWord
  have hpayN : 4 + (calldataWord I.calldata 68).toNat
      + (calldataWord I.calldata (4 + (calldataWord I.calldata 68).toNat)).toNat + 32
      ≤ I.calldata.size := by
    have h := hwf.payload; simp only [tlcHashOpArgOff, tlcHashOpArgLen] at h; omega
  have s4 : ((⟨4⟩ : UInt256) + calldataWord I.calldata 68).toNat
      = 4 + (calldataWord I.calldata 68).toNat := by
    rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from rfl]
    exact Nat.mod_eq_of_lt (by simp only [UInt256.size]; omega)
  have hslt78 : UInt256.slt (⟨4⟩ + calldataWord I.calldata 68 + ⟨31⟩)
      (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
    apply slt_lit_one_low hwf.small
    rw [uadd_toNat, s4, show (⟨31⟩ : UInt256).toNat = 31 from rfl,
      Nat.mod_eq_of_lt (by simp only [UInt256.size]; omega)]
    omega
  have hgtLen : UInt256.gt (calldataWord I.calldata (4 + (calldataWord I.calldata 68).toNat))
      ⟨18446744073709551615⟩ = ⟨0⟩ := ugt_zero (by rw [hu64tn]; exact hwf.lenMax)
  have sAll : ((⟨4⟩:UInt256) + calldataWord I.calldata 68
        + calldataWord I.calldata (4 + (calldataWord I.calldata 68).toNat) + ⟨32⟩).toNat
      = 4 + (calldataWord I.calldata 68).toNat
        + (calldataWord I.calldata (4 + (calldataWord I.calldata 68).toNat)).toNat + 32 := by
    have hsz2 : I.calldata.size < UInt256.size := hsize
    rw [uadd_toNat, uadd_toNat, s4, show (⟨32⟩:UInt256).toNat = 32 from rfl]
    simp only [UInt256.size] at hsz2 ⊢; omega
  have hgtPay : UInt256.gt (⟨4⟩ + calldataWord I.calldata 68
      + calldataWord I.calldata (4 + (calldataWord I.calldata 68).toNat) + ⟨32⟩)
      (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
    ugt_zero (by rw [sAll, ulit_toNat' _ hsize]; exact hpayN)
  have rd := evm_run h with [
    push2 ⟨4675⟩, dup10, dup3, dup11, add, push2 ⟨4383⟩, jump (by jump_dest),
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨4399⟩,
    jumpiT (by rw [hslt78]; decide) (by jump_dest),
    jumpdest, pop, dup2, calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup2, gt, iszero,
    push2 ⟨4421⟩, jumpiT (by rw [hu64, s4, hgtLen]; decide) (by jump_dest),
    jumpdest, push1 ⟨32⟩, dup4, add, swap2, pop, dup4, push1 ⟨32⟩, dup3, dup6, add, add, gt, iszero,
    push2 ⟨4444⟩, jumpiT (by rw [s4, hgtPay]; decide) (by jump_dest),
    jumpdest, swap3, pop, swap3, swap1, pop, jump (by jump_dest), jumpdest]
  rw [s4] at rd
  exact ⟨_, _, rd⟩

/-- Decoder checkpoint 4676 → 1015: final shuffle, load predecessor (@cd100) and salt (@cd132),
    return to the body dispatcher.  Offsets normalized to 100/132. -/
private theorem tlcHashOpDecode1015 {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4676⟩
      [calldataWord I.calldata (4 + (calldataWord I.calldata 68).toNat),
        ⟨4⟩ + calldataWord I.calldata 68 + ⟨32⟩, calldataWord I.calldata 68,
        ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, calldataWord I.calldata 36, calldataWord I.calldata 4, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨1014⟩, ⟨581⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1015⟩
      [calldataWord I.calldata 132, calldataWord I.calldata 100,
        calldataWord I.calldata (4 + (calldataWord I.calldata 68).toNat),
        ⟨4⟩ + calldataWord I.calldata 68 + ⟨32⟩, calldataWord I.calldata 36,
        calldataWord I.calldata 4, ⟨581⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have e100 : ((⟨4⟩ : UInt256) + ⟨96⟩).toNat = 100 := by native_decide
  have e132 : ((⟨4⟩ : UInt256) + ⟨128⟩).toNat = 132 := by native_decide
  have rd := evm_run h with [
    swap8, swap11, swap7, swap10, pop, swap8, push1 ⟨96⟩, dup2, add, calldataload,
    swap7, push1 ⟨128⟩, swap1, swap2, add, calldataload, swap6, pop, swap4, pop, pop, pop, pop,
    jump (by jump_dest), jumpdest]
  rw [e100, e132] at rd
  exact ⟨_, _, rd⟩

/-! ## Hash driver + encoder (1015 → 5934 → encode → 2354 KECCAK256 → 581) -/

/-- Hash driver 1015 → 5934: build the encoder argument frame, load the free pointer `0x80`,
    push encoder dest `0xa0` and return address `2332`. -/
private theorem tlcHashOpDrive5934 {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1015⟩
      [calldataWord I.calldata 132, calldataWord I.calldata 100,
        calldataWord I.calldata (4 + (calldataWord I.calldata 68).toNat),
        ⟨4⟩ + calldataWord I.calldata 68 + ⟨32⟩, calldataWord I.calldata 36,
        calldataWord I.calldata 4, ⟨581⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5934⟩
      [⟨32⟩ + ⟨128⟩, calldataWord I.calldata 132, calldataWord I.calldata 100,
        calldataWord I.calldata (4 + (calldataWord I.calldata 68).toNat),
        ⟨4⟩ + calldataWord I.calldata 68 + ⟨32⟩, calldataWord I.calldata 36,
        calldataWord I.calldata 4, ⟨2332⟩, ⟨0⟩, calldataWord I.calldata 132,
        calldataWord I.calldata 100, calldataWord I.calldata (4 + (calldataWord I.calldata 68).toNat),
        ⟨4⟩ + calldataWord I.calldata 68 + ⟨32⟩, calldataWord I.calldata 36,
        calldataWord I.calldata 4, ⟨581⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, evm_run h with [
    push2 ⟨2304⟩, jump (by jump_dest), jumpdest, push0, dup7, dup7, dup7, dup7, dup7, dup7,
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨2332⟩, swap7, swap6, swap5, swap4, swap3, swap2, swap1,
    push2 ⟨5933⟩, jump (by jump_dest), jumpdest]⟩

/-- EVM execute path: with zero callvalue and well-formed calldata, `hashOperation` returns
    `keccak256(abi.encode(target,value,data,predecessor,salt))`. -/
theorem tlcHashOperationX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 13))
    (hwf : tlcHashOpWF I) :
    RDret timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (tlcHashOpKecWord I)) := by
  sorry

end OpenZeppelinBench.TimelockController
