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

end Benchmarks.Dss.Cat
