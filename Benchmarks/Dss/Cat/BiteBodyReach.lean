import Benchmarks.Dss.Cat.BiteConnect
import Benchmarks.Dss.Cat.BiteBodyMem

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Dss.Cat

/-! # Cat `bite` — concrete-memory grab/fess/kick reach path (`catBiteBody` support)

The frozen `catBiteReach{Grab,Fess}Region` wrappers abstract their post-call memory (`∃ mem'`), so a
carried memory word (the `milk.chop` field re-read at pc 2349, `catBiteReach2300to2383`'s `hChop`)
cannot be threaded through them.  This file builds the *concrete*-memory grab/fess reach (the void
`CALL`s have `outSize = 0`, so `RD.call`'s return copy is a no-op and the pre-call calldata memory
survives verbatim) plus the "read below the free pointer `p`" seams that recover `milk.chop` from the
`grab`/`fess` calldata overlay (`chop@(q+32) = 256 < p = q+96 = 320`). -/

/-! ## Read-below-`p` seams: `grab`/`fess` calldata writes at `[p, …)` preserve reads at `off + 32 ≤ p` -/

/-- The 7 `grab` calldata writes (at `p, p+4, …, p+164`) leave any word strictly below `p` unchanged
(generic-offset clone of `catBiteGrabCalldataMemP_read64`). -/
theorem catBiteGrabCalldataMemP_readBelow (p ilk urn thisW vowRaw dink dart : UInt256)
    {mem : ByteArray} (off : ℕ) (hoff : off + 32 ≤ p.toNat) (hpmem : p.toNat ≤ mem.size)
    (hpsz : p.toNat + 196 < UInt256.size) :
    (catBiteGrabCalldataMemP p ilk urn thisW vowRaw dink dart mem).readWithPadding off 32
      = mem.readWithPadding off 32 := by
  have e4 : (p + ⟨4⟩).toNat = p.toNat + 4 := by
    rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide, Nat.mod_eq_of_lt (by omega)]
  have e36 : (p + ⟨36⟩).toNat = p.toNat + 36 := by
    rw [uadd_toNat, show (⟨36⟩ : UInt256).toNat = 36 from by decide, Nat.mod_eq_of_lt (by omega)]
  have e68 : (p + ⟨68⟩).toNat = p.toNat + 68 := by
    rw [uadd_toNat, show (⟨68⟩ : UInt256).toNat = 68 from by decide, Nat.mod_eq_of_lt (by omega)]
  have e100 : (p + ⟨100⟩).toNat = p.toNat + 100 := by
    rw [uadd_toNat, show (⟨100⟩ : UInt256).toNat = 100 from by decide, Nat.mod_eq_of_lt (by omega)]
  have e132 : (p + ⟨132⟩).toNat = p.toNat + 132 := by
    rw [uadd_toNat, show (⟨132⟩ : UInt256).toNat = 132 from by decide, Nat.mod_eq_of_lt (by omega)]
  have e164 : (p + ⟨164⟩).toNat = p.toNat + 164 := by
    rw [uadd_toNat, show (⟨164⟩ : UInt256).toNat = 164 from by decide, Nat.mod_eq_of_lt (by omega)]
  have hsSel := catBiteGrabSelMemP_size p hpmem
  have hsIlk := catBiteGrabIlkMemP_size p ilk hpmem hpsz
  have hsUrn := catBiteGrabUrnMemP_size p ilk urn hpmem hpsz
  have hsThis := catBiteGrabThisMemP_size p ilk urn thisW hpmem hpsz
  have hsVow := catBiteGrabVowMemP_size p ilk urn thisW vowRaw hpmem hpsz
  have hsDink := catBiteGrabDinkMemP_size p ilk urn thisW vowRaw dink hpmem hpsz
  unfold catBiteGrabCalldataMemP
  rw [write32_read_below _ _ (p + ⟨164⟩).toNat off (by rw [toByteArray_size]) (by omega) (by omega)]
  unfold catBiteGrabDinkMemP
  rw [write32_read_below _ _ (p + ⟨132⟩).toNat off (by rw [toByteArray_size]) (by omega) (by omega)]
  unfold catBiteGrabVowMemP
  rw [write32_read_below _ _ (p + ⟨100⟩).toNat off (by rw [toByteArray_size]) (by omega) (by omega)]
  unfold catBiteGrabThisMemP
  rw [write32_read_below _ _ (p + ⟨68⟩).toNat off (by rw [toByteArray_size]) (by omega) (by omega)]
  unfold catBiteGrabUrnMemP
  rw [write32_read_below _ _ (p + ⟨36⟩).toNat off (by rw [toByteArray_size]) (by omega) (by omega)]
  unfold catBiteGrabIlkMemP
  rw [write32_read_below _ _ (p + ⟨4⟩).toNat off (by rw [toByteArray_size]) (by omega) (by omega)]
  unfold catBiteGrabSelMemP
  rw [write32_read_below _ _ p.toNat off (by rw [toByteArray_size]) hpmem (by omega)]

/-- The 2 `fess` calldata writes (at `p2, p2+4`) leave any word strictly below `p2` unchanged
(generic-offset clone of `catBiteFessCalldataMemP_read64`). -/
theorem catBiteFessCalldataMemP_readBelow (p2 dartRate : UInt256) {mem : ByteArray}
    (off : ℕ) (hoff : off + 32 ≤ p2.toNat) (hpmem : p2.toNat ≤ mem.size)
    (hpsz : p2.toNat + 36 < UInt256.size) :
    (catBiteFessCalldataMemP p2 dartRate mem).readWithPadding off 32 = mem.readWithPadding off 32 := by
  have e4 : (⟨4⟩ + p2).toNat = p2.toNat + 4 := by
    rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide, Nat.add_comm,
      Nat.mod_eq_of_lt (by omega)]
  have hs := catBiteFessSelMemP_size p2 hpmem
  unfold catBiteFessCalldataMemP
  rw [write32_read_below _ _ (⟨4⟩ + p2).toNat off (by rw [toByteArray_size]) (by omega) (by omega)]
  unfold catBiteFessSelMemP
  rw [write32_read_below _ _ p2.toNat off (by rw [toByteArray_size]) hpmem (by omega)]

/-! ## Concrete-memory `grab`/`fess` reach regions

The frozen `catBiteReach{Grab,Fess}Region` abstract the post-`CALL` memory as `∃ mem'`.  Both calls are
VOID (`outSize = ⟨0⟩`), so `RD.call`'s return copy `o.write 0 mem outOff (min ⟨0⟩ …).toNat` is a no-op
(`min ⟨0⟩ x = ⟨0⟩`, `.toNat = 0`, `o.write 0 base off 0 = base`), and the pre-call calldata memory
survives verbatim.  These variants EXPOSE that concrete memory. -/

/-- `2073` → `2193`, exposing the concrete `grab` calldata memory (`catBiteGrabCalldataMemP`). -/
theorem catBiteReachGrabRegionC {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {dink dart q art ink iDust iSpot iRate urn p : UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2073⟩
      (dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn ::
        biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
      mem aw o (cA', σ') k C)
    (hFree64 : mem.readWithPadding 64 32 = UInt256.toByteArray p)
    (hp96 : 96 ≤ p.toNat) (hpmem : p.toNat ≤ mem.size)
    (hawcov : p.toNat ≤ aw.toNat * 32) (hawsz : aw.toNat * 32 < UInt256.size)
    (hpsz : p.toNat + 256 < UInt256.size)
    (hthisCanon : (UInt256.ofNat I.codeOwner.val).toNat < EVM.addressModulus)
    (hdink : dink.toNat ≤ 2 ^ 255) (hdart : dart.toNat ≤ 2 ^ 255)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σ'
      (UInt256.land (solcSlotWord σ' I ⟨3⟩) biteAddrMaskWord) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap) (z : Bool)
      (o' : ByteArray) (A'' aw' : _) (k' C' : ℕ),
      RD catBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2193⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: (p + ⟨196⟩) :: ⟨2074820416⟩ ::
          UInt256.land (solcSlotWord σ' I ⟨3⟩) biteAddrMaskWord ::
          dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn ::
          biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
        (catBiteGrabCalldataMemP p (biteIlkWord I) urn (UInt256.ofNat I.codeOwner.val)
          (solcSlotWord σ' I ⟨4⟩) dink dart mem)
        aw' o' (cA'', σ'') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 (UInt256.land (solcSlotWord σ' I ⟨3⟩) biteAddrMaskWord))
        "grab" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (biteIlkWord I)),
         .address (AccountAddress.ofNat (UInt256.land biteAddrMaskWord urn).toNat),
         .address (AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat),
         .address (AccountAddress.ofNat
           (UInt256.land biteAddrMaskWord (solcSlotWord σ' I ⟨4⟩)).toNat),
         .int (-(Int.ofNat dink.toNat)), .int (-(Int.ofNat dart.toNat))]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'', substate := A'', createdAccounts := cA'' }, o') I.perm
    ∧ o'.size < UInt256.size := by
  obtain ⟨awF, _, _, rd2177⟩ :=
    catBiteTraceGrabBuild rd hFree64 hp96 hpmem hawcov hawsz hpsz (by simp)
  have hencode := catBiteGrabEncode_eq p (biteIlkWord I) urn (UInt256.ofNat I.codeOwner.val)
    (solcSlotWord σ' I ⟨4⟩) dink dart hp96 hpmem (by omega) hthisCanon hdink hdart
  obtain ⟨gasWord, _, _, rd2192⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨2177⟩) (okPc := ⟨2189⟩) rd2177 hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  obtain ⟨cA'', σ'', z, o', A_in, callGas, k', C', hΘpack, rd2193raw, hosz⟩ :=
    RD.call rd2192 (by native_decide) hdepth (by simp)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  have hpc : ((⟨2189⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = (⟨2193⟩ : UInt256) := by native_decide
  rw [hpc] at rd2193raw
  have hz : (min (⟨0⟩ : UInt256) (UInt256.ofNat o'.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat o'.size := by
      show (0 : Nat) ≤ (UInt256.ofNat o'.size).val.val
      exact Nat.zero_le _
    simp [min, hle]
  rw [hz, byteArray_write_len_zero] at rd2193raw
  refine ⟨cA'', σ'', z, o', A', _, k', C', rd2193raw, ?_, hosz⟩
  refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
    (callPerm := I.perm)
    (targetWord := UInt256.land (solcSlotWord σ' I ⟨3⟩) biteAddrMaskWord)
    (mem := catBiteGrabCalldataMemP p (biteIlkWord I) urn (UInt256.ofNat I.codeOwner.val)
      (solcSlotWord σ' I ⟨4⟩) dink dart mem)
    (inOff := p) (inSize := ⟨196⟩)
    (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
    rfl hencode ?_
  simpa [initState] using hΘ

/-- `2193` → `2300`, exposing the concrete `fess` calldata memory (`catBiteFessCalldataMemP`).  The
guard/rate-recompute (`catBiteTraceSeg7f`) passes `mem` through, then `catBiteTraceFessBuild` writes
the `vow.fess(dartRate)` calldata into `mem`, and the void `CALL` preserves it. -/
theorem catBiteReachFessRegionC {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {status d0 d1 d2 dink dart q art ink iDust iSpot iRate urn dartRate p2 : UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2193⟩
      (status :: d0 :: d1 :: d2 :: dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate ::
        ⟨0⟩ :: urn :: biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
      mem aw o (cA', σ') k C)
    (hstatus : status ≠ ⟨0⟩)
    (hRateFit : iRate.toNat * dart.toNat < UInt256.size)
    (hDartRate : UInt256.mul dart iRate = dartRate)
    (hFree64 : mem.readWithPadding 64 32 = UInt256.toByteArray p2)
    (hp96 : 96 ≤ p2.toNat) (hpmem : p2.toNat ≤ mem.size)
    (hawcov : p2.toNat ≤ aw.toNat * 32) (hawsz : aw.toNat * 32 < UInt256.size)
    (hpsz : p2.toNat + 96 < UInt256.size)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σ'
      (UInt256.land biteAddrMaskWord (solcSlotWord σ' I ⟨4⟩)) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap) (z : Bool)
      (o' : ByteArray) (A'' aw' : _) (k' C' : ℕ),
      RD catBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2300⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: (⟨32⟩ + (⟨4⟩ + p2)) :: ⟨1769929592⟩ ::
          UInt256.land biteAddrMaskWord (solcSlotWord σ' I ⟨4⟩) ::
          dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn ::
          biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
        (catBiteFessCalldataMemP p2 dartRate mem)
        aw' o' (cA'', σ'') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 (UInt256.land biteAddrMaskWord (solcSlotWord σ' I ⟨4⟩)))
        "fess" 0 [.int (Int.ofNat dartRate.toNat)]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'', substate := A'', createdAccounts := cA'' }, o') I.perm
    ∧ o'.size < UInt256.size := by
  obtain ⟨_, _, rd2242⟩ := catBiteTraceSeg7f rd hstatus hRateFit hDartRate (by simp)
  obtain ⟨awF, _, _, rd2284⟩ :=
    catBiteTraceFessBuild rd2242 hFree64 hp96 hpmem hawcov hawsz hpsz (by simp)
  have hencode := catBiteFessEncode_eq p2 dartRate hpmem (by omega)
  obtain ⟨gasWord, _, _, rd2299⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨2284⟩) (okPc := ⟨2296⟩) rd2284 hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  obtain ⟨cA'', σ'', z, o', A_in, callGas, k', C', hΘpack, rd2300, hosz⟩ :=
    RD.call (pc := ⟨2299⟩) rd2299 (by native_decide) hdepth (by simp)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  have hz : (min (⟨0⟩ : UInt256) (UInt256.ofNat o'.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat o'.size := by
      show (0 : Nat) ≤ (UInt256.ofNat o'.size).val.val
      exact Nat.zero_le _
    simp [min, hle]
  rw [hz, byteArray_write_len_zero] at rd2300
  refine ⟨cA'', σ'', z, o', A', _, k', C', rd2300, ?_, hosz⟩
  refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
    (callPerm := I.perm)
    (targetWord := UInt256.land biteAddrMaskWord (solcSlotWord σ' I ⟨4⟩))
    (mem := catBiteFessCalldataMemP p2 dartRate mem) (inOff := p2) (inSize := ⟨36⟩)
    (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
    rfl hencode ?_
  simpa [initState] using hΘ

end Benchmarks.Dss.Cat
