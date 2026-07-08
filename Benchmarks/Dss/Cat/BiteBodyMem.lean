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

end Benchmarks.Dss.Cat
