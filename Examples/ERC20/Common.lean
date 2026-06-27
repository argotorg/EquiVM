import Examples.ERC20.Bytecode
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.Solc
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace ERC20

/-! ## ERC20-local storage and ABI helpers -/

/-- Loading an ERC20 full-slot `uint256` location is the source-level integer value of the same word. -/
theorem erc20StorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (erc20Uint256Loc slot)
      = .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  simpa [erc20Uint256Loc, uint256Loc] using storageLocLoad_uint256 evm slot

/-- ABI-encoding a Solm `uint256` return value produces exactly the EVM's returned word bytes.
    Re-export of `Reasoning.Theory.uint256ReturnEncoding` (`uint256 ≡ .elem (.int (.uint 256))`). -/
theorem erc20Uint256ReturnEncoding (v : UInt256) :
    encodeReturnValue? uint256 (.int (Int.ofNat v.toNat)) =
      some (UInt256.toByteArray v) := uint256ReturnEncoding v

/-- The shared solc return wrapper computes the fixed one-word return length. -/
theorem erc20SubRet32_toNat :
    (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = 32 := by
  decide

/-- ERC20 jump-destination proof macro. -/
macro "erc20_jd" : term => `(by jump_dest)

/-! ## Address canonicality helpers

These moved to the library — `solcAddrMask` / `solcAddrCanon_eq` / `solcAddrCanonical_of_clean` in
`Reasoning.Solc`, and `uInt256_eq_self` / `uInt256_eq_zero_of_ne` / `land_mask160` in
`Reasoning.EVMWord`.  The `erc20*` names are kept as thin re-exports so ERC20's call sites are
unchanged. -/

/-- Address-mask literal (`PUSH20 0xff…ff`) used by solc address cleanup.  See `solcAddrMask`. -/
def erc20AddrMask : UInt256 := solcAddrMask

theorem erc20Ueq_self (a : UInt256) : UInt256.eq a a = ⟨1⟩ := uInt256_eq_self a

theorem erc20Ueq_zero_of_ne {a b : UInt256} (h : ¬ UInt256.eq a b = ⟨1⟩) :
    UInt256.eq a b = ⟨0⟩ := uInt256_eq_zero_of_ne h

theorem erc20Land_mask160 (n : ℕ) (h : n < 2 ^ 160) : Nat.land n (2 ^ 160 - 1) = n :=
  land_mask160 n h

theorem erc20Canon_eq {w : UInt256} (hcanon : w.toNat < EVM.addressModulus) :
    UInt256.eq w (UInt256.land w erc20AddrMask) = ⟨1⟩ := solcAddrCanon_eq hcanon

theorem erc20Word_canonical_of_clean {w : UInt256}
    (hclean : UInt256.eq w (UInt256.land w erc20AddrMask) = ⟨1⟩) :
    w.toNat < EVM.addressModulus := solcAddrCanonical_of_clean hclean

theorem erc20AddrMask_clean {w : UInt256} (hcanon : w.toNat < EVM.addressModulus) :
    UInt256.land w erc20AddrMask = w := solcAddrMask_clean hcanon

theorem erc20AddrMask_clean_left {w : UInt256} (hcanon : w.toNat < EVM.addressModulus) :
    UInt256.land erc20AddrMask w = w := solcAddrMask_clean_left hcanon

end ERC20

namespace Reasoning.Reach

/-- ERC20's solc `cleanup_t_uint256` identity routine at pc 1894. -/
theorem RD.erc20Routine0766 {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {v ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc20Bytecode ee g s0 ⟨1894⟩ (v :: ret :: R) mem aw rdata acc k C)
    (hret : (D_J erc20Bytecode 0).contains ret = true) (hov : R.length + 4 ≤ 1024) :
    RD erc20Bytecode ee g s0 ret (v :: R) mem aw rdata acc (k + 9) (C + 27) :=
  evm_run h with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop,
    jump hret ]

/-- ERC20's shared solc ABI encoder for one `uint256` word at pc 2073. -/
theorem RD.erc20RoutineEncodeUint256 {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {val ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc20Bytecode ee g s0 ⟨2073⟩ (⟨128⟩ :: val :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hret : (D_J erc20Bytecode 0).contains ret = true) (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD erc20Bytecode ee g s0 ret ((⟨128⟩ + ⟨32⟩) :: R)
      (solcReturnMem val) (UInt256.ofNat 5) rdata acc k' C' := by
  let rd := evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop,
    push2 ⟨2092⟩, push0, dup4, add, dup5, push2 ⟨2058⟩,
    jump (by jump_dest),
    jumpdest, push2 ⟨2067⟩, dup2, push2 ⟨1894⟩,
    jump (by jump_dest),
    raw erc20Routine0766 (by jump_dest) (by evm_ov),
    jumpdest, dup3,
    raw mstore 6 (solcReturnMem val) (UInt256.ofNat 5) (by decide) mem_cost
      (by rw [show ((⟨128⟩ : UInt256) + ⟨0⟩).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    pop, pop,
    jump (by jump_dest),
    jumpdest, swap3, swap2, pop, pop,
    jump hret ]
  exact ⟨_, _, rd⟩

-- A merged routine: ~30 opcode steps in one proof, each generating a `decode erc20Bytecode pc`
-- `decide` over the large bytecode.  The original `dec*` chain spread these across four theorems,
-- each with its own default budget; one lemma collects them, so it needs a raised budget.
set_option maxHeartbeats 1000000 in
/-- ERC20's solc shared `abi_decode_address` load-and-mask routine, entered at pc 1874.

    From `[off, csize, ret] ++ R`, it loads the calldata word at byte-offset `off`, runs the 160-bit
    address-mask subroutine, and arrives at the canonicality check (pc 1861) with the stack
    `[mask(word), word, 1888, word, off, csize, ret] ++ R`.  This is the per-address-argument decoder
    body copied ~14× across the ERC20 function proofs; factoring it here lets each call site supply
    only the offset and overflow bound.  The single following step — the canonicality compare at pc
    1861 — is left to the caller because it branches: canonical addresses jump on to `ret`, while
    non-canonical ones revert.  `csize`, `ret`, and the working scratch are threaded untouched. -/
theorem RD.erc20DecodeAddrMask {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {off csize ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc20Bytecode ee g s0 ⟨1874⟩ (off :: csize :: ret :: R) mem aw rdata acc k C)
    (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD erc20Bytecode ee g s0 ⟨1861⟩
        (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
            ERC20.erc20AddrMask
          :: uInt256OfByteArray (ee.calldata.readBytes off.toNat 32) :: ⟨1888⟩
          :: uInt256OfByteArray (ee.calldata.readBytes off.toNat 32)
          :: off :: csize :: ret :: R) mem aw rdata acc k' C' := by
  -- load the word and step to the validator (pc 1852)
  have h1852 := evm_run h with [
    jumpdest, push0, dup2, calldataload, swap1, pop, push2 ⟨1888⟩, dup2,
    push2 ⟨1852⟩, jump (by jump_dest) ]
  -- enter the mask subroutine dispatch (pc 1835)
  have h1835 := evm_run h1852 with [
    jumpdest, push2 ⟨1861⟩, dup2, push2 ⟨1835⟩, jump (by jump_dest) ]
  -- run the 160-bit mask subroutine, landing at the canonicality check (pc 1861)
  exact ⟨_, _, evm_run h1835 with [
    jumpdest, push0, push2 ⟨1845⟩, dup3, push2 ⟨1804⟩, jump (by jump_dest),
    jumpdest, push0, push20 ERC20.erc20AddrMask, dup3, and, swap1, pop, swap2, swap1, pop,
    jump (by jump_dest),
    jumpdest, swap1, pop, swap2, swap1, pop, jump (by jump_dest) ]⟩

set_option maxHeartbeats 400000 in
/-- Success continuation of the shared address-argument decoder: from pc 1874 with
    `[off, csize, ret] ++ R`, decode a **canonical** address (`hcanon`) and return the decoded word to
    the dynamic return address `ret` as `[word] ++ R`.  Built on `erc20DecodeAddrMask` plus the
    canonicality-pass branch; shared by every successful ERC20 address decode. -/
theorem RD.erc20DecodeAddrOk {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {off csize ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc20Bytecode ee g s0 ⟨1874⟩ (off :: csize :: ret :: R) mem aw rdata acc k C)
    (hcanon : (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32)).toNat
        < EVM.addressModulus)
    (hret : (D_J erc20Bytecode 0).contains ret = true) (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD erc20Bytecode ee g s0 ret
        (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32) :: R) mem aw rdata acc k' C' := by
  obtain ⟨k', C', rd⟩ := RD.erc20DecodeAddrMask h hov
  have hclean : UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
      (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
        ERC20.erc20AddrMask) = ⟨1⟩ :=
    ERC20.erc20Canon_eq hcanon
  exact ⟨_, _, evm_run rd with [
    jumpdest, dup2, eq, push2 ⟨1871⟩, jumpiT (by rw [hclean]; decide) (by jump_dest),
    jumpdest, pop, jump (by jump_dest),
    jumpdest, swap3, swap2, pop, pop, jump hret ]⟩

/-- Revert continuation of the shared address-argument decoder: from pc 1874 with
    `[off, csize, ret] ++ R`, a **non-canonical** address (`hnc`) fails the canonicality check and
    reverts.  Built on `erc20DecodeAddrMask` plus the canonicality-fail branch; shared by every ERC20
    address-decode revert. -/
theorem RD.erc20DecodeAddrRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {off csize ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc20Bytecode ee g s0 ⟨1874⟩ (off :: csize :: ret :: R) mem aw rdata acc k C)
    (hnc : UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
        (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
          ERC20.erc20AddrMask) = ⟨0⟩)
    (hov : R.length + 14 ≤ 1024) :
    RDrev erc20Bytecode g s0 := by
  obtain ⟨k', C', rd⟩ := RD.erc20DecodeAddrMask h hov
  exact (evm_run rd with [
    jumpdest, dup2, eq, push2 ⟨1871⟩, jumpiNT (by rw [hnc]),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ] :
    RDrev erc20Bytecode g s0)

/-- Bytecode shape for the solc mapping-hash suffix used throughout ERC20.

    The suffix starts after the caller-specific key preparation has already left the stack as
    `[key, 0, baseSlot] ++ R`.  It writes `key` at scratch offset `0`, writes `baseSlot` at
    scratch offset `32`, then runs `KECCAK256 0 64`. -/
@[reducible] def erc20MappingHashSuffixWf (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p4 := p2 + UInt256.ofNat 2
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  decode erc20Bytecode pc = some (.DUP2, .none)
  ∧ decode erc20Bytecode p1 = some (.MSTORE, .none)
  ∧ decode erc20Bytecode p2 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode erc20Bytecode p4 = some (.ADD, .none)
  ∧ decode erc20Bytecode p5 = some (.SWAP1, .none)
  ∧ decode erc20Bytecode p6 = some (.DUP2, .none)
  ∧ decode erc20Bytecode p7 = some (.MSTORE, .none)
  ∧ decode erc20Bytecode p8 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode erc20Bytecode p10 = some (.ADD, .none)
  ∧ decode erc20Bytecode p11 = some (.PUSH0, .none)
  ∧ decode erc20Bytecode p12 = some (.KECCAK256, .none)

/-- Discharge an ERC20 mapping-hash suffix bytecode-shape proof at a concrete PC. -/
macro "erc20_mapping_hash_wf" : term =>
  `(by
    unfold Reasoning.Reach.erc20MappingHashSuffixWf
    repeat' first | apply And.intro | native_decide)

/-- End PC for `erc20MappingHashSuffixWf`.  Kept as chained offsets so callers at concrete PCs
    reduce by computation instead of needing UInt256 arithmetic reassociation lemmas. -/
@[reducible] def erc20MappingHashSuffixEndPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p4 := p2 + UInt256.ofNat 2
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  p12 + ⟨1⟩

/-- Shared ERC20 mapping-hash suffix.

    From `[key, 0, baseSlot] ++ R`, this runs the straight-line solc sequence
    `DUP2; MSTORE; PUSH1 32; ADD; SWAP1; DUP2; MSTORE; PUSH1 32; ADD; PUSH0; KECCAK256`,
    producing `[keccak256(key ++ baseSlot)] ++ R`.  The caller supplies the two memory-write
    equalities and the keccak slot identity, so the lemma stays independent of `balanceOf` versus
    `allowance` and of the incoming scratch memory. -/
theorem RD.erc20MappingHashSuffix {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {pc key baseSlot slot : UInt256} {R : List UInt256} {mem memKey memHash : ByteArray}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc20Bytecode ee g s0 pc (key :: ⟨0⟩ :: baseSlot :: R) mem
        (UInt256.ofNat 3) rdata acc k C)
    (hwf : erc20MappingHashSuffixWf pc)
    (hkey : (UInt256.toByteArray key).write 0 mem 0 32 = memKey)
    (hbase : (UInt256.toByteArray baseSlot).write 0 memKey
        ((⟨32⟩ : UInt256) + ⟨0⟩).toNat 32 = memHash)
    (hslot : UInt256.ofNat
        (fromByteArrayBigEndian (ffi.KEC (memHash.readWithPadding 0
          ((⟨32⟩ : UInt256) + ((⟨32⟩ : UInt256) + ⟨0⟩)).toNat))) = slot)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD erc20Bytecode ee g s0 (erc20MappingHashSuffixEndPc pc) (slot :: R)
      memHash (UInt256.ofNat 3) rdata acc k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10⟩
  have rd1 := h.dup2 hd0 (by evm_ov)
  have rd2 := rd1.mstore 0 memKey (UInt256.ofNat 3) hd1 mem_cost hkey
    (by native_decide) (by evm_ov)
  have rd3 := rd2.push1 ⟨32⟩ hd2 (by evm_ov)
  have rd4 := rd3.add hd3 (by evm_ov)
  have rd5 := rd4.swap1 hd4 (by evm_ov)
  have rd6 := rd5.dup2 hd5 (by evm_ov)
  have rd7 := rd6.mstore 0 memHash (UInt256.ofNat 3) hd6 mem_cost hbase
    (by native_decide) (by evm_ov)
  have rd8 := rd7.push1 ⟨32⟩ hd7 (by evm_ov)
  have rd9 := rd8.add hd8 (by evm_ov)
  have rd10 := rd9.push0 hd9 (by evm_ov)
  exact ⟨_, _, rd10.keccak256 0 slot (UInt256.ofNat 3) hd10 mem_cost hslot
    (by native_decide) (by evm_ov)⟩

end Reasoning.Reach

namespace ERC20

/-- ERC20's shared uint256 encoder at pc 2073, generalized to an arbitrary incoming memory. -/
theorem erc20RoutineEncodeUint256FromMem {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {val ret : UInt256} {R : List UInt256} {mem memout : ByteArray}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc20Bytecode ee g s0 ⟨2073⟩ (⟨128⟩ :: val :: ret :: R)
        mem (UInt256.ofNat 3) rdata acc k C)
    (hmemout : (UInt256.toByteArray val).write 0 mem 128 32 = memout)
    (hret : (D_J erc20Bytecode 0).contains ret = true) (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD erc20Bytecode ee g s0 ret ((⟨128⟩ + ⟨32⟩) :: R)
      memout (UInt256.ofNat 5) rdata acc k' C' := by
  let rd := evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop,
    push2 ⟨2092⟩, push0, dup4, add, dup5, push2 ⟨2058⟩,
    jump erc20_jd,
    jumpdest, push2 ⟨2067⟩, dup2, push2 ⟨1894⟩,
    jump erc20_jd,
    raw erc20Routine0766 erc20_jd (by evm_ov),
    jumpdest, dup3,
    raw mstore 6 memout (UInt256.ofNat 5) (by decide) mem_cost
      (by rw [show ((⟨128⟩ : UInt256) + ⟨0⟩).toNat = 128 from by decide]; exact hmemout)
      (by decide) (by evm_ov),
    pop, pop,
    jump erc20_jd,
    jumpdest, swap3, swap2, pop, pop,
    jump hret ]
  exact ⟨_, _, rd⟩

end ERC20
