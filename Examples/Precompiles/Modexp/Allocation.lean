import Examples.Precompiles.Modexp.FastSpec

/-!
# Exact Solidity byte-array allocation helpers

The nontrivial ModExp path allocates three bounded `bytes` objects.  This file begins the shared
allocator proof with the compiler's checked size-rounding subroutine.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option Elab.async false

def bytesAllocationSize (n : Nat) : Nat := 32 + 32 * ((n + 31) / 32)

def bytesAllocationWords (n : Nat) : Nat := 1 + (n + 31) / 32

theorem bytesAllocationSize_eq_words (n : Nat) :
    bytesAllocationSize n = 32 * bytesAllocationWords n := by
  unfold bytesAllocationSize bytesAllocationWords
  omega

private theorem allocationSizeDecodes :
    [decode runtimeBytecode ⟨528⟩, decode runtimeBytecode ⟨529⟩,
      decode runtimeBytecode ⟨538⟩, decode runtimeBytecode ⟨539⟩,
      decode runtimeBytecode ⟨540⟩, decode runtimeBytecode ⟨543⟩,
      decode runtimeBytecode ⟨544⟩, decode runtimeBytecode ⟨546⟩,
      decode runtimeBytecode ⟨547⟩, decode runtimeBytecode ⟨549⟩,
      decode runtimeBytecode ⟨550⟩, decode runtimeBytecode ⟨551⟩,
      decode runtimeBytecode ⟨553⟩, decode runtimeBytecode ⟨554⟩,
      decode runtimeBytecode ⟨555⟩] =
    [some (.JUMPDEST, .none),
      some (.Push .PUSH8, some (⟨18446744073709551615⟩, 8)),
      some (.DUP2, .none), some (.GT, .none),
      some (.Push .PUSH2, some (⟨523⟩, 2)), some (.JUMPI, .none),
      some (.Push .PUSH1, some (⟨31⟩, 1)), some (.ADD, .none),
      some (.Push .PUSH1, some (⟨31⟩, 1)), some (.NOT, .none),
      some (.AND, .none), some (.Push .PUSH1, some (⟨32⟩, 1)),
      some (.ADD, .none), some (.SWAP1, .none), some (.JUMP, .none)] := by
  native_decide

/-- Checked byte-array allocation size: `32 + ceil(n/32)*32`, with exact helper gas. -/
theorem allocationSizeExact {cA gh bl σ σ₀ A I} {g : Sat256}
    {n ret : Nat} {tail : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} (hn : n ≤ 1024) (htail : tail.length ≤ 1019)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨528⟩
      (UInt256.ofNat n :: UInt256.ofNat ret :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      (UInt256.ofNat (bytesAllocationSize n) :: tail) mem aw rdata acc
      (k + 15) (C + 55) := by
  have hd := allocationSizeDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10,
    hd11, hd12, hd13, hd14⟩
  have hnWord : n < UInt256.size :=
    lt_trans (lt_of_le_of_lt hn (by decide : 1024 < 2 ^ 64)) (by decide)
  have hgt : UInt256.gt (UInt256.ofNat n) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [UInt256.toNat_ofNat_of_lt hnWord,
      show (⟨18446744073709551615⟩ : UInt256).toNat = 18446744073709551615 by
        native_decide]
    omega
  have rd529 := evm_run rd0 with [known jumpdest hd0]
  have rd538 := RDx.pushConst rd529 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) hd1 (by evm_ov)
  have rd := evm_run rd538 with [
    known dup2 hd2, known gt hd3, known push2 hd4 ⟨523⟩,
    known jumpiNT hd5 hgt,
    known push1 hd6 ⟨31⟩, known add hd7, known push1 hd8 ⟨31⟩,
    known not hd9, known and hd10, known push1 hd11 ⟨32⟩,
    known add hd12, known swap1 hd13, known jump hd14 hret ]
  have halloc := bytesAllocationSize_ofNat n (by omega)
  have hstack :
      (⟨32⟩ : UInt256) + UInt256.land (UInt256.lnot ⟨31⟩)
          ((⟨31⟩ : UInt256) + UInt256.ofNat n) =
        UInt256.ofNat (bytesAllocationSize n) := by
    calc
      _ = UInt256.land (UInt256.ofNat n + ⟨31⟩) (UInt256.lnot ⟨31⟩) + ⟨32⟩ := by
        rw [u256_add_comm (⟨32⟩ : UInt256), u256_land_comm,
          u256_add_comm (⟨31⟩ : UInt256)]
      _ = UInt256.ofNat (bytesAllocationSize n) := by
        simpa [bytesAllocationSize] using halloc
  rw [hstack] at rd
  exact rd.withIndices (by omega) (by omega)

def setFreePtr (mem : ByteArray) (fp : Nat) : ByteArray :=
  (UInt256.toByteArray (UInt256.ofNat fp)).write 0 mem 64 32

private theorem allocateMemoryDecodes :
    [decode runtimeBytecode ⟨485⟩, decode runtimeBytecode ⟨486⟩,
      decode runtimeBytecode ⟨487⟩, decode runtimeBytecode ⟨489⟩,
      decode runtimeBytecode ⟨490⟩, decode runtimeBytecode ⟨492⟩,
      decode runtimeBytecode ⟨494⟩, decode runtimeBytecode ⟨495⟩,
      decode runtimeBytecode ⟨496⟩, decode runtimeBytecode ⟨497⟩,
      decode runtimeBytecode ⟨498⟩, decode runtimeBytecode ⟨499⟩,
      decode runtimeBytecode ⟨500⟩, decode runtimeBytecode ⟨501⟩,
      decode runtimeBytecode ⟨502⟩, decode runtimeBytecode ⟨503⟩,
      decode runtimeBytecode ⟨512⟩, decode runtimeBytecode ⟨513⟩,
      decode runtimeBytecode ⟨514⟩, decode runtimeBytecode ⟨515⟩,
      decode runtimeBytecode ⟨518⟩, decode runtimeBytecode ⟨519⟩,
      decode runtimeBytecode ⟨521⟩, decode runtimeBytecode ⟨522⟩] =
    [some (.JUMPDEST, .none), some (.SWAP1, .none),
      some (.Push .PUSH1, some (⟨31⟩, 1)), some (.NOT, .none),
      some (.Push .PUSH1, some (⟨31⟩, 1)),
      some (.Push .PUSH1, some (⟨64⟩, 1)), some (.MLOAD, .none),
      some (.SWAP4, .none), some (.ADD, .none), some (.AND, .none),
      some (.DUP3, .none), some (.ADD, .none), some (.DUP3, .none),
      some (.DUP2, .none), some (.LT, .none),
      some (.Push .PUSH8, some (⟨18446744073709551615⟩, 8)),
      some (.DUP3, .none), some (.GT, .none), some (.OR, .none),
      some (.Push .PUSH2, some (⟨523⟩, 2)), some (.JUMPI, .none),
      some (.Push .PUSH1, some (⟨64⟩, 1)), some (.MSTORE, .none),
      some (.JUMP, .none)] := by
  native_decide

/-- Exact checked free-memory-pointer allocation for an already aligned byte-array allocation
size.  The returned word is the old free pointer and `mem[0x40]` contains the advanced pointer. -/
theorem allocateMemoryExact {cA gh bl σ σ₀ A I} {g : Sat256}
    {n fp ret : Nat} {tail : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hn : n ≤ 1024) (hfp : 96 ≤ fp) (hbound : fp + bytesAllocationSize n < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (haw3 : 3 ≤ aw.toNat)
    (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (htail : tail.length ≤ 1017)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨485⟩
      (UInt256.ofNat (bytesAllocationSize n) :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      (UInt256.ofNat fp :: tail) (setFreePtr mem (fp + bytesAllocationSize n))
      aw rdata acc (k + 24) (C + 82) := by
  have hd := allocateMemoryDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10,
    hd11, hd12, hd13, hd14, hd15, hd16, hd17, hd18, hd19, hd20, hd21, hd22, hd23⟩
  have hallocBound : bytesAllocationSize n ≤ 1088 := by
    unfold bytesAllocationSize
    omega
  have hallocWord : bytesAllocationSize n < UInt256.size :=
    lt_trans (lt_of_le_of_lt hallocBound (by decide : 1088 < 2 ^ 64)) (by decide)
  have hfpWord : fp < UInt256.size :=
    lt_trans (by omega : fp < 2 ^ 64) (by decide)
  have hnewWord : fp + bytesAllocationSize n < UInt256.size :=
    lt_trans hbound (by decide)
  have hallocAligned : bytesAllocationSize n =
      32 * (1 + ((n + 31) / 32)) := by unfold bytesAllocationSize; omega
  have hround : UInt256.land (UInt256.lnot ⟨31⟩)
      (UInt256.ofNat (bytesAllocationSize n) + ⟨31⟩) =
      UInt256.ofNat (bytesAllocationSize n) := by
    apply roundAligned32 _ (1 + ((n + 31) / 32))
    · rw [UInt256.toNat_ofNat_of_lt hallocWord, hallocAligned]
    · rw [UInt256.toNat_ofNat_of_lt hallocWord]
      omega
  have hround' :
      (UInt256.ofNat (bytesAllocationSize n) + ⟨31⟩).land (UInt256.lnot ⟨31⟩) =
        UInt256.ofNat (bytesAllocationSize n) := by
    simpa only [u256_land_comm] using hround
  have hsum : UInt256.ofNat fp + UInt256.ofNat (bytesAllocationSize n) =
      UInt256.ofNat (fp + bytesAllocationSize n) := by
    apply u256_inj
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hfpWord,
      UInt256.toNat_ofNat_of_lt hallocWord,
      UInt256.toNat_ofNat_of_lt hnewWord, Nat.mod_eq_of_lt hnewWord]
  have rd494 := evm_run rd0 with [
    known jumpdest hd0, known swap1 hd1, known push1 hd2 ⟨31⟩,
    known not hd3, known push1 hd4 ⟨31⟩, known push1 hd5 ⟨64⟩ ]
  have rd495 := RDx.mload 0 (UInt256.ofNat fp) aw rd494 hd6
    (by
      intro s hsaw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', MachineState.M, hsaw, hstk]
      rw [show (⟨64⟩ : UInt256).toNat = 64 by decide]
      have hawOfNat : UInt256.ofNat aw.toNat = aw := u256_ofNat_toNat aw
      rw [show max aw.toNat ((64 + 32 + 31) / 32) = aw.toNat by omega, hawOfNat]
      omega)
    (mloadWordValue_of_readWithPadding
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 by decide]; omega)
      haw64 hread)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 by decide]
      simp [MachineState.M]
      have hawOfNat : UInt256.ofNat aw.toNat = aw := u256_ofNat_toNat aw
      rw [show max aw.toNat ((64 + 32 + 31) / 32) = aw.toNat by omega, hawOfNat])
    (by simp only [List.length_cons]; omega)
  have rd503raw := evm_run rd495 with [
    known swap4 hd7, known add hd8, known and hd9, known dup3 hd10,
    known add hd11, known dup3 hd12, known dup2 hd13, known lt hd14 ]
  rw [hround', hsum] at rd503raw
  have rd512 := RDx.pushConst rd503raw ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) hd15 (by evm_ov)
  have hlt : UInt256.lt (UInt256.ofNat (fp + bytesAllocationSize n))
      (UInt256.ofNat fp) = ⟨0⟩ := by
    apply ult_zero
    rw [UInt256.toNat_ofNat_of_lt hnewWord, UInt256.toNat_ofNat_of_lt hfpWord]
    omega
  have hgt : UInt256.gt (UInt256.ofNat (fp + bytesAllocationSize n))
      ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [UInt256.toNat_ofNat_of_lt hnewWord,
      show (⟨18446744073709551615⟩ : UInt256).toNat = 18446744073709551615 by
        native_decide]
    omega
  have rd519 := evm_run rd512 with [
    known dup3 hd16, known gt hd17, known or hd18,
    known push2 hd19 ⟨523⟩,
    known jumpiNT hd20 (by rw [hgt, hlt]; native_decide),
    known push1 hd21 ⟨64⟩ ]
  have rd522 := RDx.mstore 0 (setFreePtr mem (fp + bytesAllocationSize n)) aw
    rd519 hd22
    (by
      intro s hsaw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', MachineState.M, hsaw, hstk]
      rw [show (⟨64⟩ : UInt256).toNat = 64 by decide]
      have hawOfNat : UInt256.ofNat aw.toNat = aw := u256_ofNat_toNat aw
      rw [show max aw.toNat ((64 + 32 + 31) / 32) = aw.toNat by omega, hawOfNat]
      omega)
    (by simp [setFreePtr, show (⟨64⟩ : UInt256).toNat = 64 by decide])
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 by decide]
      simp [MachineState.M]
      have hawOfNat : UInt256.ofNat aw.toNat = aw := u256_ofNat_toNat aw
      rw [show max aw.toNat ((64 + 32 + 31) / 32) = aw.toNat by omega, hawOfNat])
    (by simp only [List.length_cons]; omega)
  have rd := evm_run rd522 with [known jump hd23 hret]
  exact rd.withIndices (by omega) (by omega)

def bytesPayloadSize (n : Nat) : Nat := 32 * ((n + 31) / 32)

theorem le_bytesPayloadSize (n : Nat) : n ≤ bytesPayloadSize n := by
  unfold bytesPayloadSize
  omega

theorem add_le_bytesAllocationSize (n : Nat) : n + 32 ≤ bytesAllocationSize n := by
  unfold bytesAllocationSize
  omega

def storeBytesLength (mem : ByteArray) (fp n : Nat) : ByteArray :=
  (UInt256.toByteArray (UInt256.ofNat n)).write 0 mem fp 32

/-- Reading the header written by `storeBytesLength` returns the declared byte length. -/
theorem storeBytesLength_read_self {mem : ByteArray} {fp n : Nat}
    (hgap : fp - mem.size < USize.size) :
    (storeBytesLength mem fp n).readWithPadding fp 32 =
      UInt256.toByteArray (UInt256.ofNat n) := by
  unfold storeBytesLength
  exact toByteArray_write_read_back_of_gap (UInt256.ofNat n) mem fp hgap

/-- A later bytes header does not alter an earlier, in-bounds 32-byte word. -/
theorem storeBytesLength_read_below {mem : ByteArray} {fp n read : Nat}
    (hread : read + 32 ≤ mem.size) (hbelow : read + 32 ≤ fp)
    (hgap : fp - mem.size < USize.size) :
    (storeBytesLength mem fp n).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  unfold storeBytesLength
  exact toByteArray_write_read_below_of_gap (UInt256.ofNat n) mem fp read
    hread hbelow hgap

/-- A later bytes header preserves an earlier padded word.  Unlike
`storeBytesLength_read_below`, the earlier word may straddle the concrete end of memory; the
allocation gap merely makes the same EVM zero padding concrete. -/
theorem storeBytesLength_read_below_padded {mem : ByteArray} {fp n read : Nat}
    (hmem32 : 32 ≤ mem.size) (hbelow : read + 32 ≤ fp)
    (hgap : fp - mem.size < USize.size) :
    (storeBytesLength mem fp n).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  unfold storeBytesLength
  exact toByteArray_write_read_below_padded_of_gap (UInt256.ofNat n) mem fp read
    hmem32 hbelow hgap

/-- A later bytes header preserves an earlier arbitrary-width in-bounds read. -/
theorem storeBytesLength_read_below_len {mem : ByteArray} {fp n read len : Nat}
    (hread : read + len ≤ mem.size) (hbelow : read + len ≤ fp)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hgap : fp - mem.size < USize.size) :
    (storeBytesLength mem fp n).readWithPadding read len =
      mem.readWithPadding read len := by
  unfold storeBytesLength
  exact toByteArray_write_read_below_len_of_gap (UInt256.ofNat n) mem fp read len
    hread hbelow hpos hlen64 hgap

/-- A later bytes header preserves an earlier arbitrary-width padded read.  The earlier read may
extend into the old implicit zero padding below the new header. -/
theorem storeBytesLength_read_below_len_padded {mem : ByteArray} {fp n read len : Nat}
    (hbelow : read + len ≤ fp) (hpos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hgap : fp - mem.size < USize.size) :
    (storeBytesLength mem fp n).readWithPadding read len =
      mem.readWithPadding read len := by
  unfold storeBytesLength
  exact toByteArray_write_read_below_len_padded_of_gap (UInt256.ofNat n) mem fp read len
    hbelow hpos hlen64 hgap

/-- Updating Solidity's free-memory pointer at `0x40` leaves every in-bounds word starting at
`0x60` or above unchanged. -/
theorem setFreePtr_read_above {mem : ByteArray} {fp read : Nat}
    (hmem : 96 ≤ mem.size) (hread : 96 ≤ read) (hin : read + 32 ≤ mem.size) :
    (setFreePtr mem fp).readWithPadding read 32 = mem.readWithPadding read 32 := by
  unfold setFreePtr
  exact write32_read_above _ _ 64 read (by rw [toByteArray_size]) (by omega)
    (by omega) hin

/-- Updating Solidity's free-memory pointer leaves padded reads at `0x60` and above unchanged,
including reads which extend beyond the concrete byte-array representation. -/
theorem setFreePtr_read_above_padded {mem : ByteArray} {fp read : Nat}
    (hmem : 96 ≤ mem.size) (hread : 96 ≤ read) :
    (setFreePtr mem fp).readWithPadding read 32 = mem.readWithPadding read 32 := by
  unfold setFreePtr
  exact write32_read_above_padded _ _ 64 read (by rw [toByteArray_size])
    (by omega) (by omega)

/-- Updating Solidity's free-memory pointer leaves every in-bounds read at `0x60` and above
unchanged. -/
theorem setFreePtr_read_above_len {mem : ByteArray} {fp read len : Nat}
    (hmem : 96 ≤ mem.size) (hread : 96 ≤ read)
    (hin : read + len ≤ mem.size) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (setFreePtr mem fp).readWithPadding read len = mem.readWithPadding read len := by
  unfold setFreePtr
  exact write32_read_above_len _ _ 64 read len (by rw [toByteArray_size])
    (by omega) (by omega) hin hpos hlen64

/-- Updating Solidity's free-memory pointer leaves padded reads at `0x60` and above unchanged,
including arbitrary-width reads which extend beyond the concrete byte-array representation. -/
theorem setFreePtr_read_above_len_padded {mem : ByteArray} {fp read len : Nat}
    (hmem : 96 ≤ mem.size) (hread : 96 ≤ read)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (setFreePtr mem fp).readWithPadding read len = mem.readWithPadding read len := by
  unfold setFreePtr
  exact write32_read_above_len_padded _ _ 64 read len (by rw [toByteArray_size])
    (by omega) (by omega) hpos hlen64

theorem setFreePtr_size {mem : ByteArray} {fp : Nat} (hmem : 96 ≤ mem.size) :
    (setFreePtr mem fp).size = mem.size := by
  unfold setFreePtr
  apply toByteArray_write32_size_of_le mem _ 64 mem.size mem.size rfl (by omega)
  omega

theorem setFreePtr_read64 {mem : ByteArray} {fp : Nat} (hmem : 96 ≤ mem.size) :
    (setFreePtr mem fp).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat fp) := by
  unfold setFreePtr
  exact toByteArray_write32_read_back mem (UInt256.ofNat fp) 64 (by omega)

theorem storeBytesLength_size {mem : ByteArray} {fp n : Nat}
    (hmem : mem.size ≤ fp) (hgap : fp - mem.size < USize.size) :
    (storeBytesLength mem fp n).size = fp + 32 := by
  unfold storeBytesLength
  apply toByteArray_write32_size_of_ge mem _ fp mem.size (fp + 32) rfl hmem hgap rfl

theorem storeBytesLength_read64 {mem : ByteArray} {fp n : Nat}
    (hmem : 96 ≤ mem.size) (hfp : 96 ≤ fp)
    (hgap : fp - mem.size < USize.size) :
    (storeBytesLength mem fp n).readWithPadding 64 32 = mem.readWithPadding 64 32 := by
  unfold storeBytesLength
  exact toByteArray_write_read_below_of_gap _ mem fp 64 (by omega) (by omega) hgap

def newBytesStoreWords (aw : UInt256) (fp : Nat) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat fp 32)

def newBytesWords (aw : UInt256) (fp n : Nat) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (newBytesStoreWords aw fp).toNat (fp + 32) (bytesPayloadSize n))

def newBytesStoreExpansionGas (aw : UInt256) (fp : Nat) : Nat :=
  Cₘ (newBytesStoreWords aw fp) - Cₘ aw

def newBytesCopyExpansionGas (aw : UInt256) (fp n : Nat) : Nat :=
  Cₘ (newBytesWords aw fp n) - Cₘ (newBytesStoreWords aw fp)

theorem firstNewBytesWords {n : Nat} (hn : n ≤ 1024) :
    newBytesWords (UInt256.ofNat 3) 128 n =
      UInt256.ofNat ((128 + bytesAllocationSize n) / 32) := by
  unfold newBytesWords newBytesStoreWords MachineState.M
  rw [show (UInt256.ofNat 3).toNat = 3 by native_decide]
  simp only [Nat.reduceAdd, Nat.reduceDiv]
  rw [show max 3 5 = 5 by decide]
  rw [show (UInt256.ofNat 5).toNat = 5 by native_decide]
  unfold bytesAllocationSize bytesPayloadSize
  by_cases hz : 32 * ((n + 31) / 32) = 0
  · simp [hz]
  · simp [hz]
    apply congrArg UInt256.ofNat
    omega

/-- At an aligned free pointer whose word index is the current active-word count, allocating a
bounded byte array advances that count by exactly the allocation's word count. -/
theorem newBytesWords_aligned {q n : Nat}
    (hq : q + bytesAllocationWords n < UInt256.size) :
    newBytesWords (UInt256.ofNat q) (32 * q) n =
      UInt256.ofNat (q + bytesAllocationWords n) := by
  have hq0 : q < UInt256.size := by
    have hpos : 0 < bytesAllocationWords n := by unfold bytesAllocationWords; omega
    omega
  have hq1 : q + 1 < UInt256.size := by
    have hwords : 1 ≤ bytesAllocationWords n := by unfold bytesAllocationWords; omega
    omega
  unfold newBytesWords newBytesStoreWords MachineState.M
  rw [UInt256.toNat_ofNat_of_lt hq0]
  simp only [Nat.reduceAdd, Nat.reduceDiv]
  rw [show max q ((32 * q + 32 + 31) / 32) = q + 1 by
    have : (32 * q + 32 + 31) / 32 = q + 1 := by omega
    rw [this]
    omega]
  rw [UInt256.toNat_ofNat_of_lt hq1]
  unfold bytesPayloadSize bytesAllocationWords
  by_cases hz : 32 * ((n + 31) / 32) = 0
  · have hc : (n + 31) / 32 = 0 := by omega
    simp [hc]
  · simp [hz]
    apply congrArg UInt256.ofNat
    omega

/-- Exact cost of solc's bounded `new bytes(n)` helper, including both checked-allocation
subroutines, the length store, zero initialization, and both memory-expansion charges. -/
def newBytesGas (aw : UInt256) (fp n : Nat) : Nat :=
  293 + newBytesStoreExpansionGas aw fp + newBytesCopyExpansionGas aw fp n +
    3 * ((bytesPayloadSize n + 31) / 32)

def wordArrayPayloadSize (n : Nat) : Nat := 32 * n

def wordArrayAllocationSize (n : Nat) : Nat := 32 + wordArrayPayloadSize n

theorem wordArrayAllocationSize_eq_bytesAllocationSize_mul32 (n : Nat) :
    wordArrayAllocationSize n = bytesAllocationSize (32 * n) := by
  unfold wordArrayAllocationSize wordArrayPayloadSize bytesAllocationSize
  have hdiv : (32 * n + 31) / 32 = n := by omega
  rw [hdiv]

theorem wordArrayPayloadSize_eq_bytesPayloadSize_mul32 (n : Nat) :
    wordArrayPayloadSize n = bytesPayloadSize (32 * n) := by
  unfold wordArrayPayloadSize bytesPayloadSize
  have hdiv : (32 * n + 31) / 32 = n := by omega
  rw [hdiv]

def newWordArrayWords (aw : UInt256) (fp n : Nat) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (newBytesStoreWords aw fp).toNat (fp + 32) (wordArrayPayloadSize n))

def newWordArrayCopyExpansionGas (aw : UInt256) (fp n : Nat) : Nat :=
  Cₘ (newWordArrayWords aw fp n) - Cₘ (newBytesStoreWords aw fp)

def newWordArrayGas (aw : UInt256) (fp n : Nat) : Nat :=
  275 + newBytesStoreExpansionGas aw fp + newWordArrayCopyExpansionGas aw fp n + 3 * n

private theorem wordArraySizeDecodes :
    [decode runtimeBytecode ⟨1434⟩, decode runtimeBytecode ⟨1435⟩,
      decode runtimeBytecode ⟨1444⟩, decode runtimeBytecode ⟨1445⟩,
      decode runtimeBytecode ⟨1446⟩, decode runtimeBytecode ⟨1449⟩,
      decode runtimeBytecode ⟨1450⟩, decode runtimeBytecode ⟨1452⟩,
      decode runtimeBytecode ⟨1453⟩, decode runtimeBytecode ⟨1455⟩,
      decode runtimeBytecode ⟨1456⟩, decode runtimeBytecode ⟨1457⟩] =
    [some (.JUMPDEST, .none),
      some (.Push .PUSH8, some (⟨18446744073709551615⟩, 8)),
      some (.DUP2, .none), some (.GT, .none),
      some (.Push .PUSH2, some (⟨523⟩, 2)), some (.JUMPI, .none),
      some (.Push .PUSH1, some (⟨5⟩, 1)), some (.SHL, .none),
      some (.Push .PUSH1, some (⟨32⟩, 1)), some (.ADD, .none),
      some (.SWAP1, .none), some (.JUMP, .none)] := by
  native_decide

private theorem jumpDest_1434 :
    (D_J runtimeBytecode 0).contains ⟨1434⟩ = true := by native_decide

/-- Checked dynamic word-array allocation size: `32 + 32*n`, with exact helper gas. -/
theorem wordArraySizeExact {cA gh bl σ σ₀ A I} {g : Sat256}
    {n ret : Nat} {tail : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} (hn : n ≤ 32) (htail : tail.length ≤ 1019)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1434⟩
      (UInt256.ofNat n :: UInt256.ofNat ret :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      (UInt256.ofNat (wordArrayAllocationSize n) :: tail) mem aw rdata acc
      (k + 12) (C + 46) := by
  have hd := wordArraySizeDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11⟩
  have hnWord : n < UInt256.size :=
    lt_trans (lt_of_le_of_lt hn (by decide : 32 < 2 ^ 64)) (by decide)
  have hpayloadWord : wordArrayPayloadSize n < UInt256.size := by
    apply lt_of_le_of_lt (show wordArrayPayloadSize n ≤ 1024 by
      unfold wordArrayPayloadSize
      omega) (by decide)
  have hallocWord : wordArrayAllocationSize n < UInt256.size := by
    apply lt_of_le_of_lt (show wordArrayAllocationSize n ≤ 1056 by
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega) (by decide)
  have hgt : UInt256.gt (UInt256.ofNat n) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [UInt256.toNat_ofNat_of_lt hnWord,
      show (⟨18446744073709551615⟩ : UInt256).toNat = 18446744073709551615 by
        native_decide]
    omega
  have hshl : UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩ =
      UInt256.ofNat (wordArrayPayloadSize n) := by
    simpa [wordArrayPayloadSize] using
      (shiftLeft5_ofNat_eq (n := n) (by
        simpa [wordArrayPayloadSize] using hpayloadWord))
  have hstack : (⟨32⟩ : UInt256) + UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩ =
      UInt256.ofNat (wordArrayAllocationSize n) := by
    rw [hshl]
    apply u256_inj
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 by decide,
      UInt256.toNat_ofNat_of_lt hpayloadWord,
      UInt256.toNat_ofNat_of_lt hallocWord]
    rw [Nat.mod_eq_of_lt (by simpa [wordArrayAllocationSize] using hallocWord)]
    unfold wordArrayAllocationSize
    omega
  have rd1435 := evm_run rd0 with [known jumpdest hd0]
  have rd1444 := RDx.pushConst rd1435 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) hd1 (by evm_ov)
  have rd := evm_run rd1444 with [
    known dup2 hd2,
    known gt hd3,
    known push2 hd4 ⟨523⟩,
    known jumpiNT hd5 hgt,
    known push1 hd6 ⟨5⟩,
    known shl hd7,
    known push1 hd8 ⟨32⟩,
    known add hd9,
    known swap1 hd10,
    known jump hd11 hret]
  rw [hstack] at rd
  exact rd.withIndices (by omega) (by omega)

private theorem newBytesDecodes :
    [decode runtimeBytecode ⟨581⟩, decode runtimeBytecode ⟨582⟩,
      decode runtimeBytecode ⟨583⟩, decode runtimeBytecode ⟨586⟩,
      decode runtimeBytecode ⟨589⟩, decode runtimeBytecode ⟨590⟩,
      decode runtimeBytecode ⟨593⟩, decode runtimeBytecode ⟨594⟩,
      decode runtimeBytecode ⟨595⟩, decode runtimeBytecode ⟨598⟩,
      decode runtimeBytecode ⟨599⟩, decode runtimeBytecode ⟨600⟩,
      decode runtimeBytecode ⟨601⟩, decode runtimeBytecode ⟨602⟩,
      decode runtimeBytecode ⟨603⟩, decode runtimeBytecode ⟨605⟩,
      decode runtimeBytecode ⟨606⟩, decode runtimeBytecode ⟨609⟩,
      decode runtimeBytecode ⟨610⟩, decode runtimeBytecode ⟨611⟩,
      decode runtimeBytecode ⟨614⟩, decode runtimeBytecode ⟨615⟩,
      decode runtimeBytecode ⟨616⟩, decode runtimeBytecode ⟨617⟩,
      decode runtimeBytecode ⟨618⟩, decode runtimeBytecode ⟨620⟩,
      decode runtimeBytecode ⟨621⟩, decode runtimeBytecode ⟨622⟩,
      decode runtimeBytecode ⟨623⟩, decode runtimeBytecode ⟨624⟩] =
    [some (.JUMPDEST, .none), some (.SWAP1, .none),
      some (.Push .PUSH2, some (⟨599⟩, 2)),
      some (.Push .PUSH2, some (⟨594⟩, 2)), some (.DUP4, .none),
      some (.Push .PUSH2, some (⟨528⟩, 2)), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.Push .PUSH2, some (⟨485⟩, 2)),
      some (.JUMP, .none), some (.JUMPDEST, .none), some (.DUP3, .none),
      some (.DUP2, .none), some (.MSTORE, .none),
      some (.Push .PUSH1, some (⟨31⟩, 1)), some (.NOT, .none),
      some (.Push .PUSH2, some (⟨615⟩, 2)), some (.DUP3, .none),
      some (.SWAP5, .none), some (.Push .PUSH2, some (⟨528⟩, 2)),
      some (.JUMP, .none), some (.JUMPDEST, .none), some (.ADD, .none),
      some (.SWAP1, .none), some (.Push .PUSH1, some (⟨32⟩, 1)),
      some (.CALLDATASIZE, .none), some (.SWAP2, .none), some (.ADD, .none),
      some (.CALLDATACOPY, .none), some (.JUMP, .none)] := by
  native_decide

private theorem allocationHeader_cancel {n : Nat} (hn : n ≤ 1024) :
    UInt256.lnot ⟨31⟩ + UInt256.ofNat (bytesAllocationSize n) =
      UInt256.ofNat (bytesPayloadSize n) := by
  have hp : bytesPayloadSize n ≤ 1024 := by unfold bytesPayloadSize; omega
  have ha : bytesAllocationSize n < UInt256.size := by
    have : bytesAllocationSize n ≤ 1088 := by unfold bytesAllocationSize; omega
    exact lt_of_le_of_lt this (by decide)
  have hpw : bytesPayloadSize n < UInt256.size := lt_of_le_of_lt hp (by decide)
  apply u256_inj
  rw [uadd_toNat, lnot31_toNat, UInt256.toNat_ofNat_of_lt ha,
    UInt256.toNat_ofNat_of_lt hpw]
  rw [show bytesAllocationSize n = 32 + bytesPayloadSize n by
    unfold bytesAllocationSize bytesPayloadSize; rfl]
  have hsize : UInt256.size = 2 ^ 256 := by decide
  rw [hsize]
  have heq : 2 ^ 256 - 32 + (32 + bytesPayloadSize n) =
      2 ^ 256 + bytesPayloadSize n := by omega
  rw [heq, Nat.add_mod, Nat.mod_self]
  simp only [zero_add]
  have hp256 : bytesPayloadSize n < 2 ^ 256 := by simpa [hsize] using hpw
  have hmod : bytesPayloadSize n % 2 ^ 256 = bytesPayloadSize n :=
    Nat.mod_eq_of_lt hp256
  rw [hmod, Nat.mod_eq_of_lt hp256]

/-- Exact execution of the compiler's `new bytes(n)` helper.  The concrete memory stores the
length word and leaves the zero payload implicit; `newBytesWords` records the full logical EVM
memory extent, so later reads of that payload are zero exactly as required. -/
theorem newBytesExact {cA gh bl σ σ₀ A I} {g : Sat256}
    {n fp ret : Nat} {tail : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hn : n ≤ 1024) (hfp : 96 ≤ fp)
    (hbound : fp + bytesAllocationSize n < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64) (htail : tail.length ≤ 1014)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨581⟩
      (UInt256.ofNat n :: UInt256.ofNat ret :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      (UInt256.ofNat fp :: tail)
      (storeBytesLength (setFreePtr mem (fp + bytesAllocationSize n)) fp n)
      (newBytesWords aw fp n) rdata acc (k + 84) (C + newBytesGas aw fp n) := by
  have hd := newBytesDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9,
    hd10, hd11, hd12, hd13, hd14, hd15, hd16, hd17, hd18, hd19,
    hd20, hd21, hd22, hd23, hd24, hd25, hd26, hd27, hd28, hd29⟩
  have hnWord : n < UInt256.size :=
    lt_trans (lt_of_le_of_lt hn (by decide : 1024 < 2 ^ 64)) (by decide)
  have hfpWord : fp < UInt256.size := lt_trans (by omega : fp < 2 ^ 64) (by decide)
  have hpBound : bytesPayloadSize n ≤ 1024 := by unfold bytesPayloadSize; omega
  have hpWord : bytesPayloadSize n < UInt256.size :=
    lt_trans (lt_of_le_of_lt hpBound (by decide : 1024 < 2 ^ 64)) (by decide)
  have hfp32Word : fp + 32 < UInt256.size := by
    have : 32 ≤ bytesAllocationSize n := by unfold bytesAllocationSize; omega
    exact lt_trans (by omega : fp + 32 < 2 ^ 64) (by decide)
  have hsetSize : (setFreePtr mem (fp + bytesAllocationSize n)).size = mem.size := by
    unfold setFreePtr
    apply toByteArray_write32_size_of_le mem _ 64 mem.size mem.size rfl (by omega)
    omega
  have hstoreSize :
      (storeBytesLength (setFreePtr mem (fp + bytesAllocationSize n)) fp n).size =
        fp + 32 := by
    unfold storeBytesLength
    apply toByteArray_write32_size_of_ge _ _ fp mem.size (fp + 32) hsetSize hmemLe
      hgap rfl
  have rd528raw := evm_run rd0 with [
    known jumpdest hd0, known swap1 hd1, known push2 hd2 ⟨599⟩,
    known push2 hd3 ⟨594⟩, known dup4 hd4, known push2 hd5 ⟨528⟩,
    known jump hd6 jumpDest_528 ]
  have rd528 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨528⟩
      (UInt256.ofNat n :: ⟨594⟩ :: ⟨599⟩ :: UInt256.ofNat ret ::
        UInt256.ofNat n :: tail) mem aw rdata acc (k + 7) (C + 24) :=
    (rd528raw.withPC (by native_decide)).withIndices (by omega) (by omega)
  have rd594 := allocationSizeExact hn (by simp only [List.length_cons]; omega)
    jumpDest_594 rd528
  have rd485raw := evm_run rd594 with [
    known jumpdest hd7, known push2 hd8 ⟨485⟩, known jump hd9 (by native_decide) ]
  have rd485 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨485⟩
      (UInt256.ofNat (bytesAllocationSize n) :: ⟨599⟩ ::
        UInt256.ofNat ret :: UInt256.ofNat n :: tail)
      mem aw rdata acc (k + 25) (C + 91) :=
    (rd485raw.withPC (by native_decide)).withIndices (by omega) (by omega)
  have rd599 := allocateMemoryExact hn hfp hbound hmemSize haw3 haw64 hread
    (by simp only [List.length_cons]; omega) jumpDest_599 rd485
  have rd602 := evm_run rd599 with [known jumpdest hd10, known dup3 hd11, known dup2 hd12]
  have rd603 := RDx.mstore (newBytesStoreExpansionGas aw fp)
    (storeBytesLength (setFreePtr mem (fp + bytesAllocationSize n)) fp n)
    (newBytesStoreWords aw fp) rd602 hd13
    (by
      intro s hsaw hstk
      simp [newBytesStoreExpansionGas, newBytesStoreWords,
        memoryExpansionCost, memoryExpansionCost.μᵢ', hsaw, hstk]
      rw [UInt256.toNat_ofNat_of_lt hfpWord])
    (by simp [storeBytesLength, UInt256.toNat_ofNat_of_lt hfpWord])
    (by simp [newBytesStoreWords, UInt256.toNat_ofNat_of_lt hfpWord])
    (by simp only [List.length_cons]; omega)
  have rd528bRaw := evm_run rd603 with [
    known push1 hd14 ⟨31⟩, known not hd15, known push2 hd16 ⟨615⟩,
    known dup3 hd17, known swap5 hd18, known push2 hd19 ⟨528⟩,
    known jump hd20 jumpDest_528 ]
  have rd528b : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨528⟩
      (UInt256.ofNat n :: ⟨615⟩ :: UInt256.lnot ⟨31⟩ :: UInt256.ofNat fp ::
        UInt256.ofNat ret :: UInt256.ofNat fp :: tail)
      (storeBytesLength (setFreePtr mem (fp + bytesAllocationSize n)) fp n)
      (newBytesStoreWords aw fp) rdata acc (k + 60)
      (C + 209 + newBytesStoreExpansionGas aw fp) :=
    (rd528bRaw.withPC (by native_decide)).withIndices (by omega) (by omega)
  have rd615raw := allocationSizeExact hn
    (by simp only [List.length_cons]; omega) jumpDest_615 rd528b
  have rd616 := evm_run rd615raw with [known jumpdest hd21, known add hd22]
  have hcancel : UInt256.ofNat (bytesAllocationSize n) + UInt256.lnot ⟨31⟩ =
      UInt256.ofNat (bytesPayloadSize n) := by
    rw [u256_add_comm, allocationHeader_cancel hn]
  rw [hcancel] at rd616
  have rd623raw := evm_run rd616 with [known swap1 hd23,
    known push1 hd24 ⟨32⟩, known calldatasize hd25, known swap2 hd26, known add hd27 ]
  have hfp32 : UInt256.ofNat fp + ⟨32⟩ = UInt256.ofNat (fp + 32) := by
    apply u256_inj
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hfpWord,
      show (⟨32⟩ : UInt256).toNat = 32 by decide,
      UInt256.toNat_ofNat_of_lt hfp32Word, Nat.mod_eq_of_lt hfp32Word]
  rw [hfp32] at rd623raw
  have rd624 := RDx.calldatacopy (newBytesCopyExpansionGas aw fp n)
    (storeBytesLength (setFreePtr mem (fp + bytesAllocationSize n)) fp n)
    (newBytesWords aw fp n) rd623raw hd28
    (by
      intro s hsaw hstk
      simp [newBytesCopyExpansionGas, newBytesWords,
        memoryExpansionCost, memoryExpansionCost.μᵢ', hsaw, hstk]
      rw [UInt256.toNat_ofNat_of_lt hfp32Word,
        UInt256.toNat_ofNat_of_lt hpWord])
    (by
      rw [UInt256.toNat_ofNat_of_lt hfp32Word,
        UInt256.toNat_ofNat_of_lt hpWord,
        UInt256.toNat_ofNat_of_lt
          (lt_trans hcalldata (by decide) : I.calldata.size < UInt256.size)]
      exact write_from_source_end_past_dest I.calldata
        (storeBytesLength (setFreePtr mem (fp + bytesAllocationSize n)) fp n)
        I.calldata.size (fp + 32) (bytesPayloadSize n) (le_refl _)
        (by rw [hstoreSize]))
    (by simp [newBytesWords, UInt256.toNat_ofNat_of_lt hfp32Word,
      UInt256.toNat_ofNat_of_lt hpWord])
    (by simp only [List.length_cons]; omega)
  have rd := evm_run rd624 with [known jump hd29 hret]
  exact rd.withIndices (by omega) (by
    simp [newBytesGas, GasConstants.Gverylow, GasConstants.Gcopy,
      UInt256.toNat_ofNat_of_lt hpWord]
    omega)

private theorem wordArrayDecodes :
    [decode runtimeBytecode ⟨1487⟩, decode runtimeBytecode ⟨1488⟩,
      decode runtimeBytecode ⟨1489⟩, decode runtimeBytecode ⟨1492⟩,
      decode runtimeBytecode ⟨1495⟩, decode runtimeBytecode ⟨1496⟩,
      decode runtimeBytecode ⟨1499⟩, decode runtimeBytecode ⟨1500⟩,
      decode runtimeBytecode ⟨1501⟩, decode runtimeBytecode ⟨1502⟩,
      decode runtimeBytecode ⟨1503⟩, decode runtimeBytecode ⟨1504⟩,
      decode runtimeBytecode ⟨1506⟩, decode runtimeBytecode ⟨1507⟩,
      decode runtimeBytecode ⟨1510⟩, decode runtimeBytecode ⟨1511⟩,
      decode runtimeBytecode ⟨1512⟩, decode runtimeBytecode ⟨1515⟩] =
    [some (.JUMPDEST, .none), some (.SWAP1, .none),
      some (.Push .PUSH2, some (⟨1500⟩, 2)),
      some (.Push .PUSH2, some (⟨594⟩, 2)), some (.DUP4, .none),
      some (.Push .PUSH2, some (⟨1434⟩, 2)), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.DUP3, .none), some (.DUP2, .none),
      some (.MSTORE, .none), some (.Push .PUSH1, some (⟨31⟩, 1)),
      some (.NOT, .none), some (.Push .PUSH2, some (⟨615⟩, 2)),
      some (.DUP3, .none), some (.SWAP5, .none),
      some (.Push .PUSH2, some (⟨1434⟩, 2)), some (.JUMP, .none)] := by
  native_decide

/-- Exact execution of the compiler's dynamic word-array allocation helper at PC 1487.

The helper allocates a Solidity dynamic array with `n` 32-byte payload words, writes the length word
`n`, zero-initializes the payload by copying from `calldatasize`, and returns the old free pointer.
-/
theorem newWordArrayExact {cA gh bl σ σ₀ A I} {g : Sat256}
    {n fp ret : Nat} {tail : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hn : n ≤ 32) (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize n < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64) (htail : tail.length ≤ 1014)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1487⟩
      (UInt256.ofNat n :: UInt256.ofNat ret :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      (UInt256.ofNat fp :: tail)
      (storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize n)) fp n)
      (newWordArrayWords aw fp n) rdata acc (k + 78) (C + newWordArrayGas aw fp n) := by
  have hdw := wordArrayDecodes
  simp only [List.cons.injEq, and_true] at hdw
  rcases hdw with ⟨hw0,hw1,hw2,hw3,hw4,hw5,hw6,hw7,hw8,hw9,hw10,
    hw11,hw12,hw13,hw14,hw15,hw16,hw17⟩
  have hd := newBytesDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨_hd0,_hd1,_hd2,_hd3,_hd4,_hd5,_hd6,hd7,hd8,hd9,
    _hd10,_hd11,_hd12,_hd13,hd14,hd15,hd16,hd17,hd18,hd19,
    hd20,hd21,hd22,hd23,hd24,hd25,hd26,hd27,hd28,hd29⟩
  have hn32 : 32 * n ≤ 1024 := by omega
  have hn32Word : 32 * n < UInt256.size :=
    lt_trans (lt_of_le_of_lt hn32 (by decide : 1024 < 2 ^ 64)) (by decide)
  have hsizeEq : wordArrayAllocationSize n = bytesAllocationSize (32 * n) :=
    wordArrayAllocationSize_eq_bytesAllocationSize_mul32 n
  have hpayloadEq : wordArrayPayloadSize n = bytesPayloadSize (32 * n) :=
    wordArrayPayloadSize_eq_bytesPayloadSize_mul32 n
  have hnWord : n < UInt256.size :=
    lt_trans (lt_of_le_of_lt hn (by decide : 32 < 2 ^ 64)) (by decide)
  have hfpWord : fp < UInt256.size := lt_trans (by omega : fp < 2 ^ 64) (by decide)
  have hpBound : wordArrayPayloadSize n ≤ 1024 := by
    unfold wordArrayPayloadSize
    omega
  have hpWord : wordArrayPayloadSize n < UInt256.size :=
    lt_trans (lt_of_le_of_lt hpBound (by decide : 1024 < 2 ^ 64)) (by decide)
  have hfp32Word : fp + 32 < UInt256.size := by
    have : 32 ≤ wordArrayAllocationSize n := by
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega
    exact lt_trans (by omega : fp + 32 < 2 ^ 64) (by decide)
  have hsetSize : (setFreePtr mem (fp + wordArrayAllocationSize n)).size = mem.size := by
    unfold setFreePtr
    apply toByteArray_write32_size_of_le mem _ 64 mem.size mem.size rfl (by omega)
    omega
  have hstoreSize :
      (storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize n)) fp n).size =
        fp + 32 := by
    unfold storeBytesLength
    apply toByteArray_write32_size_of_ge _ _ fp mem.size (fp + 32) hsetSize hmemLe
      hgap rfl
  have rd1434raw := evm_run rd0 with [
    known jumpdest hw0, known swap1 hw1, known push2 hw2 ⟨1500⟩,
    known push2 hw3 ⟨594⟩, known dup4 hw4, known push2 hw5 ⟨1434⟩,
    known jump hw6 jumpDest_1434]
  have rd1434 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1434⟩
      (UInt256.ofNat n :: ⟨594⟩ :: ⟨1500⟩ :: UInt256.ofNat ret ::
        UInt256.ofNat n :: tail) mem aw rdata acc (k + 7) (C + 24) :=
    (rd1434raw.withPC (by native_decide)).withIndices (by omega) (by omega)
  have rd594 := wordArraySizeExact hn (by simp only [List.length_cons]; omega)
    jumpDest_594 rd1434
  have rd485raw := evm_run rd594 with [
    known jumpdest hd7, known push2 hd8 ⟨485⟩, known jump hd9 (by native_decide) ]
  have rd485 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨485⟩
      (UInt256.ofNat (bytesAllocationSize (32 * n)) :: ⟨1500⟩ ::
        UInt256.ofNat ret :: UInt256.ofNat n :: tail)
      mem aw rdata acc (k + 22) (C + 82) := by
    simpa [hsizeEq] using
      ((rd485raw.withPC (by native_decide)).withIndices (by omega) (by omega))
  have rd1500 := allocateMemoryExact hn32 hfp (by simpa [← hsizeEq] using hbound)
    hmemSize haw3 haw64 hread
    (by simp only [List.length_cons]; omega) (by native_decide) rd485
  have rd1503 := evm_run rd1500 with [known jumpdest hw7, known dup3 hw8, known dup2 hw9]
  have rd1504 := RDx.mstore (newBytesStoreExpansionGas aw fp)
    (storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize n)) fp n)
    (newBytesStoreWords aw fp) rd1503 hw10
    (by
      intro s hsaw hstk
      simp [newBytesStoreExpansionGas, newBytesStoreWords,
        memoryExpansionCost, memoryExpansionCost.μᵢ', hsaw, hstk]
      rw [UInt256.toNat_ofNat_of_lt hfpWord])
    (by
      simpa [storeBytesLength, hsizeEq, UInt256.toNat_ofNat_of_lt hfpWord] using
        (by simp [storeBytesLength, UInt256.toNat_ofNat_of_lt hfpWord] :
          UInt256.toByteArray (UInt256.ofNat n) =
            UInt256.toByteArray (UInt256.ofNat n)))
    (by simp [newBytesStoreWords, UInt256.toNat_ofNat_of_lt hfpWord])
    (by simp only [List.length_cons]; omega)
  have rd1434bRaw := evm_run rd1504 with [
    known push1 hw11 ⟨31⟩, known not hw12, known push2 hw13 ⟨615⟩,
    known dup3 hw14, known swap5 hw15, known push2 hw16 ⟨1434⟩,
    known jump hw17 jumpDest_1434]
  have rd615raw := wordArraySizeExact hn
    (by simp only [List.length_cons]; omega) jumpDest_615
    (rd1434bRaw.withPC (by native_decide))
  have rd616 := evm_run rd615raw with [known jumpdest hd21, known add hd22]
  have hcancel : UInt256.ofNat (wordArrayAllocationSize n) + UInt256.lnot ⟨31⟩ =
      UInt256.ofNat (wordArrayPayloadSize n) := by
    have h := allocationHeader_cancel (n := 32 * n) hn32
    rw [u256_add_comm]
    simpa [hsizeEq, hpayloadEq] using h
  rw [hcancel] at rd616
  have rd623raw := evm_run rd616 with [known swap1 hd23,
    known push1 hd24 ⟨32⟩, known calldatasize hd25, known swap2 hd26, known add hd27]
  have hfp32 : UInt256.ofNat fp + ⟨32⟩ = UInt256.ofNat (fp + 32) := by
    apply u256_inj
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hfpWord,
      show (⟨32⟩ : UInt256).toNat = 32 by decide,
      UInt256.toNat_ofNat_of_lt hfp32Word, Nat.mod_eq_of_lt hfp32Word]
  rw [hfp32] at rd623raw
  have rd624 := RDx.calldatacopy (newWordArrayCopyExpansionGas aw fp n)
    (storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize n)) fp n)
    (newWordArrayWords aw fp n) rd623raw hd28
    (by
      intro s hsaw hstk
      simp [newWordArrayCopyExpansionGas, newWordArrayWords,
        memoryExpansionCost, memoryExpansionCost.μᵢ', hsaw, hstk]
      rw [UInt256.toNat_ofNat_of_lt hfp32Word,
        UInt256.toNat_ofNat_of_lt hpWord])
    (by
      rw [UInt256.toNat_ofNat_of_lt hfp32Word,
        UInt256.toNat_ofNat_of_lt hpWord,
        UInt256.toNat_ofNat_of_lt
          (lt_trans hcalldata (by decide) : I.calldata.size < UInt256.size)]
      exact write_from_source_end_past_dest I.calldata
        (storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize n)) fp n)
        I.calldata.size (fp + 32) (wordArrayPayloadSize n) (le_refl _)
        (by rw [hstoreSize]))
    (by simp [newWordArrayWords, UInt256.toNat_ofNat_of_lt hfp32Word,
      UInt256.toNat_ofNat_of_lt hpWord])
    (by simp only [List.length_cons]; omega)
  have rd := evm_run rd624 with [known jump hd29 hret]
  exact rd.withIndices (by omega) (by
    simp [newWordArrayGas, newWordArrayCopyExpansionGas, GasConstants.Gverylow,
      GasConstants.Gcopy, UInt256.toNat_ofNat_of_lt hn32Word, wordArrayPayloadSize]
    omega)

end Modexp
