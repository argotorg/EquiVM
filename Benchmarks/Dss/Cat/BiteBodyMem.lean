import Benchmarks.Dss.Cat.BiteConnect
import Benchmarks.Dss.Cat.BiteTrace
import Benchmarks.Dss.Cat.BiteEVM
import Benchmarks.Dss.Cat.BiteCallKick
import Benchmarks.Dss.Cat.BiteConnectMem
import Benchmarks.Dss.Cat.BiteConnectDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Dss.Cat

/-! # Cat `bite` — reach-walk seam prerequisites (`catBiteBody` support)

The public `catBiteReach*` wrappers (BiteConnect) are generic over an abstract post-call memory and
expose the return-data reads as deferred hypotheses (`hRate`/`hInk`/`hFree64`/…). This file
discharges those hypotheses from the *concrete* return-data-copy memory each wrapper outputs — the
step `catBiteBody` performs at every wrapper seam. Cloned from the worked Jug template
`Benchmarks/Dss/Jug/DripBase.lean:189–318` using Cat's `writeReturnCopy_read32` /
`readWithPadding_eq_toByteArray_ofNat` (BiteConnectMem) building blocks.

Plus the missing `catBiteReach2383to2532` kick-gap wrapper. -/

/-! ## Seam 1 — `ilks` STATICCALL return copy (`catBiteReachPostIlks` output → `catBiteReachPostUrns`)

The `ilks` call copies its 5-word return `o` (Art@0, rate@32, spot@64, line@96, dust@128) into memory
at offset `0x80`. `catBiteReachPostUrns` needs `hFree64`@64, `hRate`@160, `hSpot`@192, `hDust`@256. -/

/-- The concrete memory `catBiteReachPostIlks` outputs at pc 1249: the `ilks` return `o` copied at
`0x80` over the pre-call calldata scratch. -/
noncomputable def catBiteIlksPostCallMem (I : ExecutionEnv) (o : ByteArray) : ByteArray :=
  o.write 0 (catBiteIlksCalldataMem (biteIlkWord I) solcFreePtrMem) catBiteIlksOutPtr.toNat
    (min catBiteIlksOutSize (UInt256.ofNat o.size)).toNat

private theorem ilksBase_size : (catBiteIlksCalldataMem (biteIlkWord I) solcFreePtrMem).size = 164 :=
  catBiteIlksCalldataMem_size (biteIlkWord I) solcFreePtrMem_size

private theorem ilksBase_read64 :
    (catBiteIlksCalldataMem (biteIlkWord I) solcFreePtrMem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ :=
  catBiteIlksCalldataMem_read64 (biteIlkWord I) solcFreePtrMem_size solcFreePtrMem_read64

private theorem ilks_hlen (o : ByteArray) (hlo : 160 ≤ o.size) (hout : o.size < UInt256.size) :
    (min catBiteIlksOutSize (UInt256.ofNat o.size)).toNat = 160 :=
  umin_ofNat_right_toNat_of_ge (c := 160) (n := o.size) (by decide) hlo hout

theorem catBiteIlksPostCallMem_size (I : ExecutionEnv) (o : ByteArray)
    (hlo : 160 ≤ o.size) (hout : o.size < UInt256.size) :
    (catBiteIlksPostCallMem I o).size = 288 := by
  unfold catBiteIlksPostCallMem
  rw [ilks_hlen o hlo hout, show catBiteIlksOutPtr.toNat = 128 from by native_decide,
    write_eq_gen_extend o (catBiteIlksCalldataMem (biteIlkWord I) solcFreePtrMem) 128 160
      (by decide) (by omega) (by rw [ilksBase_size]; omega) (by rw [ilksBase_size]; omega),
    ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract, ilksBase_size]
  omega

theorem catBiteIlksPostCallMem_read64 (I : ExecutionEnv) (o : ByteArray)
    (hlo : 160 ≤ o.size) (hout : o.size < UInt256.size) :
    (catBiteIlksPostCallMem I o).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold catBiteIlksPostCallMem
  rw [ilks_hlen o hlo hout, show catBiteIlksOutPtr.toNat = 128 from by native_decide,
    write_read_below_gen_extend o (catBiteIlksCalldataMem (biteIlkWord I) solcFreePtrMem) 128 160 64
      (by decide) (by omega) (by rw [ilksBase_size]; omega) (by omega)]
  exact ilksBase_read64

/-- The in-region read at `128 + 32·i` returns word `i` of the return buffer `o` (`o.extract 32i 32i+32`). -/
private theorem ilks_read_window (I : ExecutionEnv) (o : ByteArray) (readAddr : ℕ)
    (hlo : 160 ≤ o.size) (hout : o.size < UInt256.size)
    (h128 : 128 ≤ readAddr) (hhi : readAddr + 32 ≤ 288) :
    (catBiteIlksPostCallMem I o).readWithPadding readAddr 32 =
      o.extract (readAddr - 128) (readAddr - 128 + 32) := by
  unfold catBiteIlksPostCallMem
  rw [ilks_hlen o hlo hout, show catBiteIlksOutPtr.toNat = 128 from by native_decide]
  exact writeReturnCopy_read32 o (catBiteIlksCalldataMem (biteIlkWord I) solcFreePtrMem)
    128 160 readAddr (by omega) (by rw [ilksBase_size]; omega) h128 (by omega)

/-- Word form of an in-region read: `readWithPadding = toByteArray (decoded word)`. -/
private theorem ilks_read_word (I : ExecutionEnv) (o : ByteArray) (readAddr : ℕ)
    (hlo : 160 ≤ o.size) (hout : o.size < UInt256.size)
    (h128 : 128 ≤ readAddr) (hhi : readAddr + 32 ≤ 288) :
    (catBiteIlksPostCallMem I o).readWithPadding readAddr 32 =
      UInt256.toByteArray (UInt256.ofNat (fromByteArrayBigEndian
        (o.extract (readAddr - 128) (readAddr - 128 + 32)))) := by
  rw [ilks_read_window I o readAddr hlo hout h128 hhi]
  have hw := readWithPadding_eq_toByteArray_ofNat o (readAddr - 128) (by omega)
  rw [readWithPadding_eq_extract o (readAddr - 128) (by omega)] at hw
  exact hw

/-- `iRate` = word 1 of the `ilks` return (`o.extract 32 64`), read at memory `0xA0`. -/
theorem catBiteIlksPostCallMem_read160 (I : ExecutionEnv) (o : ByteArray)
    (hlo : 160 ≤ o.size) (hout : o.size < UInt256.size) :
    (catBiteIlksPostCallMem I o).readWithPadding 160 32 =
      UInt256.toByteArray (UInt256.ofNat (fromByteArrayBigEndian (o.extract 32 64))) := by
  simpa using ilks_read_word I o 160 hlo hout (by omega) (by omega)

/-- `iSpot` = word 2 of the `ilks` return (`o.extract 64 96`), read at memory `0xC0`. -/
theorem catBiteIlksPostCallMem_read192 (I : ExecutionEnv) (o : ByteArray)
    (hlo : 160 ≤ o.size) (hout : o.size < UInt256.size) :
    (catBiteIlksPostCallMem I o).readWithPadding 192 32 =
      UInt256.toByteArray (UInt256.ofNat (fromByteArrayBigEndian (o.extract 64 96))) := by
  simpa using ilks_read_word I o 192 hlo hout (by omega) (by omega)

/-- `iDust` = word 4 of the `ilks` return (`o.extract 128 160`), read at memory `0x100`. -/
theorem catBiteIlksPostCallMem_read256 (I : ExecutionEnv) (o : ByteArray)
    (hlo : 160 ≤ o.size) (hout : o.size < UInt256.size) :
    (catBiteIlksPostCallMem I o).readWithPadding 256 32 =
      UInt256.toByteArray (UInt256.ofNat (fromByteArrayBigEndian (o.extract 128 160))) := by
  simpa using ilks_read_word I o 256 hlo hout (by omega) (by omega)

/-! ## Seam 2 — `urns` STATICCALL return copy (`catBiteReachPostUrns` output → `catBiteReach1399to1521`)

The `urns` call copies its 2-word return `o` (ink@0, art@32) into memory at offset `0x80` over the
post-ilks scratch `mem` (`196 ≤ mem.size`, free-ptr `0x80`). `catBiteReach1399to1521` needs
`hFree64`@64, `hInk`@128, `hArt`@160. -/

/-- The concrete memory `catBiteReachPostUrns` outputs at pc 1399. -/
noncomputable def catBiteUrnsPostCallMem (I : ExecutionEnv) (mem o : ByteArray) : ByteArray :=
  o.write 0 (biteUrnsCalldataMem (biteIlkWord I) (biteUrnWord I) mem) (⟨128⟩ : UInt256).toNat
    (min (⟨64⟩ : UInt256) (UInt256.ofNat o.size)).toNat

private theorem urns_hlen (o : ByteArray) (hlo : 64 ≤ o.size) (hout : o.size < UInt256.size) :
    (min (⟨64⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 64 :=
  umin_ofNat_right_toNat_of_ge (c := 64) (n := o.size) (by decide) hlo hout

theorem catBiteUrnsPostCallMem_read64 (I : ExecutionEnv) {mem : ByteArray} (o : ByteArray)
    (hmem : 196 ≤ mem.size) (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlo : 64 ≤ o.size) (hout : o.size < UInt256.size) :
    (catBiteUrnsPostCallMem I mem o).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold catBiteUrnsPostCallMem
  rw [urns_hlen o hlo hout, show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
    write_read_below_gen_extend o (biteUrnsCalldataMem (biteIlkWord I) (biteUrnWord I) mem) 128 64 64
      (by decide) (by omega) (by rw [biteUrnsCalldataMem_size hmem]; omega) (by omega)]
  exact biteUrnsCalldataMem_read64 hmem hread64

private theorem urns_read_word (I : ExecutionEnv) {mem : ByteArray} (o : ByteArray) (readAddr : ℕ)
    (hmem : 196 ≤ mem.size) (hlo : 64 ≤ o.size) (hout : o.size < UInt256.size)
    (h128 : 128 ≤ readAddr) (hhi : readAddr + 32 ≤ 192) :
    (catBiteUrnsPostCallMem I mem o).readWithPadding readAddr 32 =
      UInt256.toByteArray (UInt256.ofNat (fromByteArrayBigEndian
        (o.extract (readAddr - 128) (readAddr - 128 + 32)))) := by
  unfold catBiteUrnsPostCallMem
  rw [urns_hlen o hlo hout, show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
    writeReturnCopy_read32 o (biteUrnsCalldataMem (biteIlkWord I) (biteUrnWord I) mem)
      128 64 readAddr (by omega) (by rw [biteUrnsCalldataMem_size hmem]; omega) h128 (by omega)]
  have hw := readWithPadding_eq_toByteArray_ofNat o (readAddr - 128) (by omega)
  rw [readWithPadding_eq_extract o (readAddr - 128) (by omega)] at hw
  exact hw

/-- `ink` = word 0 of the `urns` return (`o.extract 0 32`), read at memory `0x80`. -/
theorem catBiteUrnsPostCallMem_read128 (I : ExecutionEnv) {mem : ByteArray} (o : ByteArray)
    (hmem : 196 ≤ mem.size) (hlo : 64 ≤ o.size) (hout : o.size < UInt256.size) :
    (catBiteUrnsPostCallMem I mem o).readWithPadding 128 32 =
      UInt256.toByteArray (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))) := by
  simpa using urns_read_word I o 128 hmem hlo hout (by omega) (by omega)

/-- `art` = word 1 of the `urns` return (`o.extract 32 64`), read at memory `0xA0`. -/
theorem catBiteUrnsPostCallMem_read160 (I : ExecutionEnv) {mem : ByteArray} (o : ByteArray)
    (hmem : 196 ≤ mem.size) (hlo : 64 ≤ o.size) (hout : o.size < UInt256.size) :
    (catBiteUrnsPostCallMem I mem o).readWithPadding 160 32 =
      UInt256.toByteArray (UInt256.ofNat (fromByteArrayBigEndian (o.extract 32 64))) := by
  simpa using urns_read_word I o 160 hmem hlo hout (by omega) (by omega)

/-! ## The missing `catBiteReach2383to2532` kick-gap wrapper

pc 2383 (post-litter-`SSTORE`) → 2532 (kick success-guard), assembled from the raw
`catBiteTraceSeg8aCalldata` (2383→2516, kick calldata build), `RD.catBiteKickGuardOk` (2516→2531,
extcodesize guard) and `RD.catBiteKickPostCall` (2531→2532, the `CALL`). Matches the shape of the
other `catBiteReach*` wrappers so `catBiteBody` chains it uniformly into `catBiteReach2532toRet`;
exposes the call status `z` for the by_cases (kick-fail → `catBiteKickCallFailed`). -/
theorem catBiteReach2383to2532 {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAx : Batteries.RBSet AccountAddress compare} {σx : AccountMap}
    {tab dink dart q art ink iDust iSpot iRate urn ilk milkFlip : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2383⟩
      (tab :: dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o (cAx, σx) k C)
    (hFlip : (if q.toNat ≥ mem.size ∨ q ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding q.toNat 32))) = milkFlip)
    (hFree : (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 64 32))) = ⟨128⟩)
    (hawq : q.toNat + 32 ≤ aw.toNat * 32) (haw292 : 292 ≤ aw.toNat * 32)
    (hmemsize : 292 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σx (UInt256.land biteAddrMaskWord milkFlip) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hov : R.length + 40 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool) (o' : ByteArray)
      (aw' : UInt256) (k' C' : ℕ),
      RD catBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2532⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨292⟩ :: ⟨891151872⟩ ::
          UInt256.land biteAddrMaskWord milkFlip ::
          tab :: dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
        (o'.write 0 (kickCalldataMem (UInt256.land biteAddrMaskWord urn)
          (UInt256.land biteAddrMaskWord (UInt256.land biteAddrMaskWord
            (UInt256.div (solcSlotWord σx I ⟨4⟩) (UInt256.exp ⟨256⟩ ⟨0⟩)))) tab dink mem)
          128 (min (⟨32⟩ : UInt256) (UInt256.ofNat o'.size)).toNat)
        aw' o' (cA', σ') k' C'
      ∧ o'.size < UInt256.size := by
  obtain ⟨_, _, rd2516⟩ :=
    catBiteTraceSeg8aCalldata rd hFlip hFree hawq haw292 hmemsize hread64 (by omega)
  obtain ⟨gasWord, _, _, rd2531⟩ :=
    RD.catBiteKickGuardOk rd2516 hcodeSize (by simp only [List.length_cons]; omega)
  obtain ⟨cA', σ', z, o', Ain, callGas, k', C', _hΘ, rd2532, hout⟩ :=
    RD.catBiteKickPostCall rd2531 hdepth (by simp only [List.length_cons]; omega)
  exact ⟨cA', σ', z, o', _, k', C', rd2532, hout⟩

/-! ## Seam 3 — `kick` CALL return copy (`catBiteReach2383to2532` output → `catBiteReach2532toRet`)

The `kick` call copies its 1-word return `o` (id@0) into memory at offset `0x80` over the kick
calldata scratch `mem` (`292 ≤ mem.size`, free-ptr `0x80`). `catBiteReach2532toRet` needs the
MLOAD-value if-forms `hFree8`@64 and `hId8`@128. -/

/-- The concrete memory `catBiteReach2532toRet` receives at pc 2532 (`RD.catBiteKickPostCall` output). -/
noncomputable def catBiteKickPostCallMem (urn vow tab dink : UInt256) (mem o : ByteArray) : ByteArray :=
  o.write 0 (kickCalldataMem urn vow tab dink mem) (⟨128⟩ : UInt256).toNat
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat

private theorem kick_hlen (o : ByteArray) (ho32 : 32 ≤ o.size) (hout : o.size < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 :=
  umin_ofNat_right_toNat_of_ge (c := 32) (n := o.size) (by decide) ho32 hout

theorem catBiteKickPostCallMem_size (urn vow tab dink : UInt256) {mem : ByteArray} (o : ByteArray)
    (hmem : 292 ≤ mem.size) (ho32 : 32 ≤ o.size) (hout : o.size < UInt256.size) :
    (catBiteKickPostCallMem urn vow tab dink mem o).size = mem.size := by
  unfold catBiteKickPostCallMem
  rw [kick_hlen o ho32 hout, show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
    write32_eq o (kickCalldataMem urn vow tab dink mem) 128
      (by omega) (by rw [kickCalldataMem_size urn vow tab dink hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, kickCalldataMem_size urn vow tab dink hmem]
  omega

theorem catBiteKickPostCallMem_read64 (urn vow tab dink : UInt256) {mem : ByteArray} (o : ByteArray)
    (hmem : 292 ≤ mem.size) (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (ho32 : 32 ≤ o.size) (hout : o.size < UInt256.size) :
    (catBiteKickPostCallMem urn vow tab dink mem o).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold catBiteKickPostCallMem
  rw [kick_hlen o ho32 hout, show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
    write_read_below_gen_extend o (kickCalldataMem urn vow tab dink mem) 128 32 64
      (by decide) (by omega) (by rw [kickCalldataMem_size urn vow tab dink hmem]; omega) (by omega)]
  exact kickCalldataMem_read64 urn vow tab dink hmem hread64

theorem catBiteKickPostCallMem_read128 (urn vow tab dink : UInt256) {mem : ByteArray} (o : ByteArray)
    (hmem : 292 ≤ mem.size) (ho32 : 32 ≤ o.size) (hout : o.size < UInt256.size) :
    (catBiteKickPostCallMem urn vow tab dink mem o).readWithPadding 128 32 =
      UInt256.toByteArray (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))) := by
  unfold catBiteKickPostCallMem
  rw [kick_hlen o ho32 hout, show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
    writeReturnCopy_read32 o (kickCalldataMem urn vow tab dink mem) 128 32 128
      (by omega) (by rw [kickCalldataMem_size urn vow tab dink hmem]; omega) (by omega) (by omega)]
  have hw := readWithPadding_eq_toByteArray_ofNat o 0 (by omega)
  rw [readWithPadding_eq_extract o 0 (by omega)] at hw
  simpa using hw

/-- The free-pointer `0x80` (if-form) survives the kick return copy — discharges `catBiteReach2532toRet`'s `hFree8`. -/
theorem catBiteKickPostCallMem_mload64 (urn vow tab dink : UInt256) {mem : ByteArray} (o : ByteArray)
    {aw8 : UInt256} (hmem : 292 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (ho32 : 32 ≤ o.size) (hout : o.size < UInt256.size)
    (haw : 288 ≤ aw8.toNat * 32) (hawsz : aw8.toNat * 32 < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (catBiteKickPostCallMem urn vow tab dink mem o).size
        ∨ (⟨64⟩ : UInt256) ≥ aw8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((catBiteKickPostCallMem urn vow tab dink mem o).readWithPadding 64 32))) = ⟨128⟩ :=
  mloadWordValue_of_readWithPadding (off := ⟨64⟩) (v := ⟨128⟩)
    (by rw [catBiteKickPostCallMem_size urn vow tab dink o hmem ho32 hout]; show (64 : ℕ) < mem.size; omega)
    (by intro hh
        have hle : (aw8 * ⟨32⟩).toNat ≤ (⟨64⟩ : UInt256).toNat := hh
        rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
          Nat.mod_eq_of_lt hawsz, show (⟨64⟩ : UInt256).toNat = 64 from by decide] at hle
        omega)
    (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        exact catBiteKickPostCallMem_read64 urn vow tab dink o hmem hread64 ho32 hout)

/-- `id` (if-form) = the kick return word `o.extract 0 32` — discharges `catBiteReach2532toRet`'s `hId8`. -/
theorem catBiteKickPostCallMem_mload128 (urn vow tab dink : UInt256) {mem : ByteArray} (o : ByteArray)
    {aw8 : UInt256} (hmem : 292 ≤ mem.size)
    (ho32 : 32 ≤ o.size) (hout : o.size < UInt256.size)
    (haw : 288 ≤ aw8.toNat * 32) (hawsz : aw8.toNat * 32 < UInt256.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (catBiteKickPostCallMem urn vow tab dink mem o).size
        ∨ (⟨128⟩ : UInt256) ≥ aw8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((catBiteKickPostCallMem urn vow tab dink mem o).readWithPadding 128 32))) =
      UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) :=
  mloadWordValue_of_readWithPadding (off := ⟨128⟩)
    (v := UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)))
    (by rw [catBiteKickPostCallMem_size urn vow tab dink o hmem ho32 hout]; show (128 : ℕ) < mem.size; omega)
    (by intro hh
        have hle : (aw8 * ⟨32⟩).toNat ≤ (⟨128⟩ : UInt256).toNat := hh
        rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
          Nat.mod_eq_of_lt hawsz, show (⟨128⟩ : UInt256).toNat = 128 from by decide] at hle
        omega)
    (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        exact catBiteKickPostCallMem_read128 urn vow tab dink o hmem ho32 hout)

/-- The `@3818` allocator memory (`catBiteHelperMem`) preserves its base size when the free pointer
`fp` (and its `[fp, fp+96)` zero-init) fits inside `mem`. -/
theorem catBiteHelperMem_size (mem : ByteArray) (fp : UInt256)
    (hfp96 : fp.toNat + 96 ≤ mem.size) (hfpsz : fp.toNat + 96 < UInt256.size) :
    (catBiteHelperMem mem fp).size = mem.size := by
  have e32 : (⟨32⟩ + fp).toNat = fp.toNat + 32 := by
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide, Nat.add_comm,
      Nat.mod_eq_of_lt (by omega)]
  have e64 : (⟨32⟩ + (⟨32⟩ + fp)).toNat = fp.toNat + 64 := by
    rw [uadd_toNat, e32, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      Nat.mod_eq_of_lt (by omega)]; omega
  have h1 := toByteArray_write32_size_of_le mem (⟨96⟩ + fp) 64 mem.size mem.size rfl
    (by omega) (by omega)
  have h2 := toByteArray_write32_size_of_le _ ⟨0⟩ fp.toNat mem.size mem.size h1
    (by rw [h1]; omega) (by omega)
  have h3 := toByteArray_write32_size_of_le _ ⟨0⟩ (⟨32⟩ + fp).toNat mem.size mem.size h2
    (by rw [h2, e32]; omega) (by rw [e32]; omega)
  have h4 := toByteArray_write32_size_of_le _ ⟨0⟩ (⟨32⟩ + (⟨32⟩ + fp)).toNat mem.size mem.size h3
    (by rw [h3, e64]; omega) (by rw [e64]; omega)
  exact h4

/-- The keccak-scratch memory (`catBiteScratchMem`) has the same size as its base `mem`. -/
theorem catBiteScratchMem_size (mem : ByteArray) (fp ilk : UInt256)
    (hfp96 : fp.toNat + 96 ≤ mem.size) (hfpsz : fp.toNat + 96 < UInt256.size) :
    (catBiteScratchMem mem fp ilk).size = mem.size := by
  have hh := catBiteHelperMem_size mem fp hfp96 hfpsz
  have h0 := toByteArray_write32_size_of_le _ ilk 0 mem.size mem.size hh (by rw [hh]; omega)
    (by omega)
  have h1 := toByteArray_write32_size_of_le _ ⟨1⟩ 32 mem.size mem.size h0 (by rw [h0]; omega)
    (by omega)
  exact h1

/-! ## `@3818` allocator + `keccak(ilk‖1)` scratch reads (discharge `catBiteTraceSeg6`'s `hQ`/`hKec`) -/

/-- The free pointer `mem[0x40] = q = 96+fp` survives the allocator's zero-init writes (all at
`fp`/`fp+32`/`fp+64`, above the `[64,96)` free-pointer slot since `fp ≥ 96`). -/
theorem catBiteHelperMem_read64 (mem : ByteArray) (fp : UInt256)
    (hfp96 : fp.toNat + 96 ≤ mem.size) (hfplo : 96 ≤ fp.toNat)
    (hfpsz : fp.toNat + 96 < UInt256.size) :
    (catBiteHelperMem mem fp).readWithPadding 64 32 = UInt256.toByteArray (⟨96⟩ + fp) := by
  have e32 : (⟨32⟩ + fp).toNat = fp.toNat + 32 := uadd_lit32_toNat fp (by omega)
  have e64 : (⟨32⟩ + (⟨32⟩ + fp)).toNat = fp.toNat + 64 := by
    rw [uadd_toNat, e32, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      Nat.mod_eq_of_lt (by omega)]; omega
  have h1 := toByteArray_write32_size_of_le mem (⟨96⟩ + fp) 64 mem.size mem.size rfl
    (by omega) (by omega)
  have h2 := toByteArray_write32_size_of_le _ ⟨0⟩ fp.toNat mem.size mem.size h1
    (by rw [h1]; omega) (by omega)
  have h3 := toByteArray_write32_size_of_le _ ⟨0⟩ (⟨32⟩ + fp).toNat mem.size mem.size h2
    (by rw [h2, e32]; omega) (by rw [e32]; omega)
  unfold catBiteHelperMem
  rw [write32_read_below _ _ (⟨32⟩ + (⟨32⟩ + fp)).toNat 64 (by rw [toByteArray_size])
      (by rw [h3, e64]; omega) (by rw [e64]; omega),
    write32_read_below _ _ (⟨32⟩ + fp).toNat 64 (by rw [toByteArray_size])
      (by rw [h2, e32]; omega) (by rw [e32]; omega),
    write32_read_below _ _ fp.toNat 64 (by rw [toByteArray_size])
      (by rw [h1]; omega) (by omega),
    toByteArray_write32_read_back mem (⟨96⟩ + fp) 64 (by omega)]

/-- The free pointer read survives the `keccak(ilk‖1)` scratch (writes at `[0,32)`/`[32,64)`, below
the free-pointer slot). -/
theorem catBiteScratchMem_read64 (mem : ByteArray) (fp ilk : UInt256)
    (hfp96 : fp.toNat + 96 ≤ mem.size) (hfplo : 96 ≤ fp.toNat)
    (hfpsz : fp.toNat + 96 < UInt256.size) :
    (catBiteScratchMem mem fp ilk).readWithPadding 64 32 = UInt256.toByteArray (⟨96⟩ + fp) := by
  have hhsz := catBiteHelperMem_size mem fp hfp96 hfpsz
  have hi1 := toByteArray_write32_size_of_le _ ilk 0 mem.size mem.size hhsz (by rw [hhsz]; omega)
    (by omega)
  unfold catBiteScratchMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size]) (by rw [hi1]; omega) (by omega)
      (by rw [hi1]; omega),
    write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (Nat.zero_le _) (by omega)
      (by rw [hhsz]; omega)]
  exact catBiteHelperMem_read64 mem fp hfp96 hfplo hfpsz

/-- If-form of the free-pointer read `q := mem[0x40] = 96+fp` — discharges `catBiteTraceSeg6`'s `hQ`. -/
theorem catBiteScratchMem_mload64 (mem : ByteArray) (fp ilk : UInt256) {aw : UInt256}
    (hfp96 : fp.toNat + 96 ≤ mem.size) (hfplo : 96 ≤ fp.toNat)
    (hfpsz : fp.toNat + 96 < UInt256.size)
    (haw : fp.toNat + 96 ≤ aw.toNat * 32) (hawsz : aw.toNat * 32 < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (catBiteScratchMem mem fp ilk).size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
        then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((catBiteScratchMem mem fp ilk).readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨96⟩ + fp :=
  mloadWordValue_of_readWithPadding (off := ⟨64⟩) (v := ⟨96⟩ + fp)
    (by rw [catBiteScratchMem_size mem fp ilk hfp96 hfpsz]; show (64 : ℕ) < mem.size; omega)
    (by intro hh
        have hle : (aw * ⟨32⟩).toNat ≤ (⟨64⟩ : UInt256).toNat := hh
        rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
          Nat.mod_eq_of_lt hawsz, show (⟨64⟩ : UInt256).toNat = 64 from by decide] at hle
        omega)
    (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        exact catBiteScratchMem_read64 mem fp ilk hfp96 hfplo hfpsz)

/-- `keccak` input word 0 (`scratch[0] = ilk`). -/
private theorem catBiteScratchMem_read0 (mem : ByteArray) (fp ilk : UInt256)
    (hfp96 : fp.toNat + 96 ≤ mem.size) (hfpsz : fp.toNat + 96 < UInt256.size) :
    (catBiteScratchMem mem fp ilk).readWithPadding 0 32 = UInt256.toByteArray ilk := by
  have hhsz := catBiteHelperMem_size mem fp hfp96 hfpsz
  have hi1 := toByteArray_write32_size_of_le _ ilk 0 mem.size mem.size hhsz (by rw [hhsz]; omega)
    (by omega)
  unfold catBiteScratchMem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size]) (by rw [hi1]; omega) (by omega),
    toByteArray_write32_read_back (catBiteHelperMem mem fp) ilk 0 (Nat.zero_le _)]

/-- `keccak` input word 1 (`scratch[32] = 1`). -/
private theorem catBiteScratchMem_read32 (mem : ByteArray) (fp ilk : UInt256)
    (hfp96 : fp.toNat + 96 ≤ mem.size) (hfpsz : fp.toNat + 96 < UInt256.size) :
    (catBiteScratchMem mem fp ilk).readWithPadding 32 32 = UInt256.toByteArray ⟨1⟩ := by
  have hhsz := catBiteHelperMem_size mem fp hfp96 hfpsz
  have hi1 := toByteArray_write32_size_of_le _ ilk 0 mem.size mem.size hhsz (by rw [hhsz]; omega)
    (by omega)
  unfold catBiteScratchMem
  rw [toByteArray_write32_read_back _ ⟨1⟩ 32 (by rw [hi1]; omega)]

/-- The `keccak(ilk‖1)` preimage `scratch[0,64) = ilk ‖ 1` — discharges `catBiteTraceSeg6`'s `hKec`. -/
theorem catBiteScratchMem_read0_64 (mem : ByteArray) (fp ilk : UInt256)
    (hfp96 : fp.toNat + 96 ≤ mem.size) (hfpsz : fp.toNat + 96 < UInt256.size) :
    (catBiteScratchMem mem fp ilk).readWithPadding 0 64 =
      UInt256.toByteArray ilk ++ UInt256.toByteArray ⟨1⟩ := by
  have hsz := catBiteScratchMem_size mem fp ilk hfp96 hfpsz
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num) (by rw [hsz]; omega)]
  have hleft : (catBiteScratchMem mem fp ilk).extract 0 32 = UInt256.toByteArray ilk := by
    rw [← readWithPadding_eq_extract _ 0 (by rw [hsz]; omega),
      catBiteScratchMem_read0 mem fp ilk hfp96 hfpsz]
  have hright : (catBiteScratchMem mem fp ilk).extract 32 64 = UInt256.toByteArray ⟨1⟩ := by
    rw [← readWithPadding_eq_extract _ 32 (by rw [hsz]; omega),
      catBiteScratchMem_read32 mem fp ilk hfp96 hfpsz]
  rw [show (catBiteScratchMem mem fp ilk).extract 0 64 =
      (catBiteScratchMem mem fp ilk).extract 0 32 ++
        (catBiteScratchMem mem fp ilk).extract 32 64 by
      rw [ByteArray.extract_append_extract]; norm_num]
  rw [hleft, hright]

/-! ## Final `milk` struct reads (discharge `catBiteReach1708to2073`'s `hChop`/`hDunk`) -/

/-- The `milk` struct memory has size `max mem.size (q+96)` (the `[q, q+96)` fields may extend `mem`). -/
theorem catBiteMilkMem_size (mem : ByteArray) (fp ilk q flip chop dunk : UInt256)
    (hfp96 : fp.toNat + 96 ≤ mem.size) (hqfp : q = ⟨96⟩ + fp)
    (hfpsz : fp.toNat + 96 < UInt256.size) (hqsz : q.toNat + 96 < UInt256.size) :
    (catBiteMilkMem mem fp ilk q flip chop dunk).size = max mem.size (q.toNat + 96) := by
  have hscr := catBiteScratchMem_size mem fp ilk hfp96 hfpsz
  have hq96 : q.toNat = fp.toNat + 96 := by
    rw [hqfp, uadd_toNat, show (⟨96⟩ : UInt256).toNat = 96 from by decide,
      Nat.mod_eq_of_lt (by omega)]; omega
  have eq32 : (q + ⟨32⟩).toNat = q.toNat + 32 := uadd_word_lit32_toNat q (by omega)
  have eq64 : (q + ⟨64⟩).toNat = q.toNat + 64 := by
    rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 from by decide, Nat.mod_eq_of_lt (by omega)]
  have h1 := toByteArray_write32_size_of_le _ (q + ⟨96⟩) 64 mem.size mem.size hscr
    (by rw [hscr]; omega) (by omega)
  have h2 := toByteArray_write32_size_of_le _ flip q.toNat mem.size (max mem.size (q.toNat + 32)) h1
    (by rw [h1]; omega) rfl
  have h3 := toByteArray_write32_size_of_le _ chop (q + ⟨32⟩).toNat (max mem.size (q.toNat + 32))
    (max mem.size (q.toNat + 64)) h2 (by rw [h2, eq32]; omega) (by rw [eq32]; omega)
  have h4 := toByteArray_write32_size_of_le _ dunk (q + ⟨64⟩).toNat (max mem.size (q.toNat + 64))
    (max mem.size (q.toNat + 96)) h3 (by rw [h3, eq64]; omega) (by rw [eq64]; omega)
  exact h4

/-- Raw read of the `milk.chop` field at `q+32`. -/
private theorem catBiteMilkMem_readchop (mem : ByteArray) (fp ilk q flip chop dunk : UInt256)
    (hfp96 : fp.toNat + 96 ≤ mem.size) (hqfp : q = ⟨96⟩ + fp)
    (hfpsz : fp.toNat + 96 < UInt256.size) (hqsz : q.toNat + 96 < UInt256.size) :
    (catBiteMilkMem mem fp ilk q flip chop dunk).readWithPadding (q + ⟨32⟩).toNat 32 =
      UInt256.toByteArray chop := by
  have hscr := catBiteScratchMem_size mem fp ilk hfp96 hfpsz
  have hq96 : q.toNat = fp.toNat + 96 := by
    rw [hqfp, uadd_toNat, show (⟨96⟩ : UInt256).toNat = 96 from by decide,
      Nat.mod_eq_of_lt (by omega)]; omega
  have eq32 : (q + ⟨32⟩).toNat = q.toNat + 32 := uadd_word_lit32_toNat q (by omega)
  have eq64 : (q + ⟨64⟩).toNat = q.toNat + 64 := by
    rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 from by decide, Nat.mod_eq_of_lt (by omega)]
  have h1 := toByteArray_write32_size_of_le _ (q + ⟨96⟩) 64 mem.size mem.size hscr
    (by rw [hscr]; omega) (by omega)
  have h2 := toByteArray_write32_size_of_le _ flip q.toNat mem.size (max mem.size (q.toNat + 32)) h1
    (by rw [h1]; omega) rfl
  have h3 := toByteArray_write32_size_of_le _ chop (q + ⟨32⟩).toNat (max mem.size (q.toNat + 32))
    (max mem.size (q.toNat + 64)) h2 (by rw [h2, eq32]; omega) (by rw [eq32]; omega)
  unfold catBiteMilkMem
  rw [write32_read_below _ _ (q + ⟨64⟩).toNat (q + ⟨32⟩).toNat (by rw [toByteArray_size])
      (by rw [h3, eq64]; omega) (by rw [eq64, eq32]),
    toByteArray_write32_read_back _ chop (q + ⟨32⟩).toNat (by rw [h2, eq32]; omega)]

/-- Raw read of the `milk.dunk` field at `q+64`. -/
private theorem catBiteMilkMem_readdunk (mem : ByteArray) (fp ilk q flip chop dunk : UInt256)
    (hfp96 : fp.toNat + 96 ≤ mem.size) (hqfp : q = ⟨96⟩ + fp)
    (hfpsz : fp.toNat + 96 < UInt256.size) (hqsz : q.toNat + 96 < UInt256.size) :
    (catBiteMilkMem mem fp ilk q flip chop dunk).readWithPadding (q + ⟨64⟩).toNat 32 =
      UInt256.toByteArray dunk := by
  have hscr := catBiteScratchMem_size mem fp ilk hfp96 hfpsz
  have hq96 : q.toNat = fp.toNat + 96 := by
    rw [hqfp, uadd_toNat, show (⟨96⟩ : UInt256).toNat = 96 from by decide,
      Nat.mod_eq_of_lt (by omega)]; omega
  have eq32 : (q + ⟨32⟩).toNat = q.toNat + 32 := uadd_word_lit32_toNat q (by omega)
  have eq64 : (q + ⟨64⟩).toNat = q.toNat + 64 := by
    rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 from by decide, Nat.mod_eq_of_lt (by omega)]
  have h1 := toByteArray_write32_size_of_le _ (q + ⟨96⟩) 64 mem.size mem.size hscr
    (by rw [hscr]; omega) (by omega)
  have h2 := toByteArray_write32_size_of_le _ flip q.toNat mem.size (max mem.size (q.toNat + 32)) h1
    (by rw [h1]; omega) rfl
  have h3 := toByteArray_write32_size_of_le _ chop (q + ⟨32⟩).toNat (max mem.size (q.toNat + 32))
    (max mem.size (q.toNat + 64)) h2 (by rw [h2, eq32]; omega) (by rw [eq32]; omega)
  unfold catBiteMilkMem
  rw [toByteArray_write32_read_back _ dunk (q + ⟨64⟩).toNat (by rw [h3, eq64]; omega)]

/-- If-form of the `milk.chop` field read — discharges `catBiteReach1708to2073`'s `hChop`. -/
theorem catBiteMilkMem_mload_chop (mem : ByteArray) (fp ilk q flip chop dunk : UInt256) {aw : UInt256}
    (hfp96 : fp.toNat + 96 ≤ mem.size) (hqfp : q = ⟨96⟩ + fp)
    (hfpsz : fp.toNat + 96 < UInt256.size) (hqsz : q.toNat + 96 < UInt256.size)
    (haw : q.toNat + 96 ≤ aw.toNat * 32) (hawsz : aw.toNat * 32 < UInt256.size) :
    (if (⟨32⟩ + q).toNat ≥ (catBiteMilkMem mem fp ilk q flip chop dunk).size
        ∨ (⟨32⟩ + q) ≥ aw * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((catBiteMilkMem mem fp ilk q flip chop dunk).readWithPadding (⟨32⟩ + q).toNat 32))) = chop := by
  have eq32 : (q + ⟨32⟩).toNat = q.toNat + 32 := uadd_word_lit32_toNat q (by omega)
  have ez32 : (⟨32⟩ + q).toNat = q.toNat + 32 := uadd_lit32_toNat q (by omega)
  have hmsz := catBiteMilkMem_size mem fp ilk q flip chop dunk hfp96 hqfp hfpsz hqsz
  exact mloadWordValue_of_readWithPadding (off := ⟨32⟩ + q) (v := chop)
    (by rw [hmsz, ez32]; omega)
    (by intro hh
        have hle : (aw * ⟨32⟩).toNat ≤ (⟨32⟩ + q).toNat := hh
        rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
          Nat.mod_eq_of_lt hawsz, ez32] at hle
        omega)
    (by rw [ez32, ← eq32]
        exact catBiteMilkMem_readchop mem fp ilk q flip chop dunk hfp96 hqfp hfpsz hqsz)

/-- If-form of the `milk.dunk` field read — discharges `catBiteReach1708to2073`'s `hDunk`. -/
theorem catBiteMilkMem_mload_dunk (mem : ByteArray) (fp ilk q flip chop dunk : UInt256) {aw : UInt256}
    (hfp96 : fp.toNat + 96 ≤ mem.size) (hqfp : q = ⟨96⟩ + fp)
    (hfpsz : fp.toNat + 96 < UInt256.size) (hqsz : q.toNat + 96 < UInt256.size)
    (haw : q.toNat + 96 ≤ aw.toNat * 32) (hawsz : aw.toNat * 32 < UInt256.size) :
    (if (⟨64⟩ + q).toNat ≥ (catBiteMilkMem mem fp ilk q flip chop dunk).size
        ∨ (⟨64⟩ + q) ≥ aw * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((catBiteMilkMem mem fp ilk q flip chop dunk).readWithPadding (⟨64⟩ + q).toNat 32))) = dunk := by
  have eq64 : (q + ⟨64⟩).toNat = q.toNat + 64 := by
    rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 from by decide, Nat.mod_eq_of_lt (by omega)]
  have ez64 : (⟨64⟩ + q).toNat = q.toNat + 64 := by
    rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      Nat.mod_eq_of_lt (show 64 + q.toNat < UInt256.size by omega)]; omega
  have hmsz := catBiteMilkMem_size mem fp ilk q flip chop dunk hfp96 hqfp hfpsz hqsz
  exact mloadWordValue_of_readWithPadding (off := ⟨64⟩ + q) (v := dunk)
    (by rw [hmsz, ez64]; omega)
    (by intro hh
        have hle : (aw * ⟨32⟩).toNat ≤ (⟨64⟩ + q).toNat := hh
        rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
          Nat.mod_eq_of_lt hawsz, ez64] at hle
        omega)
    (by rw [ez64, ← eq64]
        exact catBiteMilkMem_readdunk mem fp ilk q flip chop dunk hfp96 hqfp hfpsz hqsz)

end Benchmarks.Dss.Cat
