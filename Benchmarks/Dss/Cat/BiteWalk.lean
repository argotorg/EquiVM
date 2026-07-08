import Benchmarks.Dss.Cat.BiteBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Dss.Cat

/-! # Cat `bite` — the integrator walk (`catBiteBodyImpl`)

Fills the vat-has-code spine of `catBiteBody`, chaining the verified reach spine and branching at
each divergence to the imported business/call leaves, feeding the all-success tail to
`catBiteSuccessBranch`. Built incrementally region-core by region-core. -/

set_option maxHeartbeats 4000000 in
theorem catBiteBodyImpl {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = catBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x45, 0xcf, 0x22, 0x30]⟩) (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x45, 0xcf, 0x22, 0x30]⟩ rfl hsel
  by_cases hshort : I.calldata.size < 68
  · exact catBiteShort hcode hsize hwv hsz4 hshort hsel hAccounts
  · rw [not_lt] at hshort
    have hsz68 : 68 ≤ I.calldata.size := hshort
    have hsz36 : 36 ≤ I.calldata.size := by omega
    have hdispatch : dispatchMsg contract I.calldata = some biteTransition := catDispatch_bite hsel
    have hdecode :
        decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
          (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I) :=
      biteDecode_ok hsz68
    by_cases hvatCode :
        Reasoning.Theory.uniswapExtCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩
    · exact catBiteBodyIlksNoCode hcode hsize hwv hsel hsz68 hAccounts hdispatch hdecode hvatCode
    · -- vat has code. Spine walk begins at the ilks STATICCALL.
      by_cases hdepth : I.depth.val < 1024
      · obtain ⟨cA', σ', z, o', A', awout, k', C', rd1249, hIlksCall, hosz, haw288, hawout9⟩ :=
          catBiteReachPostIlksAw hcode hwv hsz68 hsize hsz36 hsel hvatCode hdepth
        cases z with
        | false =>
            -- ilks STATICCALL returned success = 0.
            exact catBiteBodyIlksFailCore hcode hwv hdispatch hdecode hAccounts hvatCode
              hIlksCall rd1249 hosz (by simp)
        | true =>
            by_cases hilkslen : 160 ≤ o'.size
            · -- ilks decoded OK; STATICCALL urns.
              have hurn :
                  UInt256.land biteAddrMaskWord
                    (UInt256.land biteAddrMaskWord (calldataWord I.calldata 36)) = biteUrnWord I := by
                have hmask : biteAddrMaskWord = solcAddrMask := by native_decide
                have h2 : (2 : ℕ) ^ 160 ≤ UInt256.size := by
                  rw [show UInt256.size = 2 ^ 256 from rfl]
                  exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
                have hval : (AccountAddress.ofNat (calldataWord I.calldata 36).toNat).val
                    = (calldataWord I.calldata 36).toNat % 2 ^ 160 := by
                  unfold AccountAddress.ofNat
                  simp only [Fin.val_ofNat]
                  rw [show AccountAddress.size = 2 ^ 160 from rfl]
                simp only [biteUrnWord, biteUrnAddr, hmask]
                rw [solcAddrMask_clean_left
                  (by rw [u256_land_comm]; exact solcAddrMask_result_canonical _)]
                apply u256_inj
                rw [u256_land_toNat, nat_land_comm,
                  show solcAddrMask.toNat = 2 ^ 160 - 1 from by decide, nat_land_mask_eq_mod,
                  Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) h2),
                  UInt256.toNat_ofNat_of_lt
                    (by rw [hval]; exact lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) h2), hval]
              by_cases hUrnsVatCode :
                  Reasoning.Theory.uniswapExtCodeSizeWord σ'
                    (UInt256.land (catSlotWord ⟨3⟩ σ' I) biteAddrMaskWord) = ⟨0⟩
              · -- urns vat has no code (unreachable: same vat as ilks) — divergence leaf.
                sorry
              · obtain ⟨cAu, σu, zu, ou, Au, ku, Cu, rd1399, hUrnsCall, hoszu⟩ :=
                  catBiteReachPostUrnsAw rd1249 (by decide) hsz36 haw288
                    (by rw [hawout9]; native_decide)
                    (catBiteIlksPostCallMem_size I o' hilkslen hosz).ge
                    hilkslen hosz
                    (catBiteIlksPostCallMem_read64 I o' hilkslen hosz)
                    (catBiteIlksPostCallMem_read160 I o' hilkslen hosz)
                    (catBiteIlksPostCallMem_read192 I o' hilkslen hosz)
                    (catBiteIlksPostCallMem_read256 I o' hilkslen hosz)
                    hurn hUrnsVatCode hdepth
                cases zu with
                | false =>
                    -- urns STATICCALL returned success = 0.
                    sorry
                | true =>
                    by_cases hurnslen : 64 ≤ ou.size
                    · by_cases hlive : catSlotWord ⟨2⟩ σu I = ⟨1⟩
                      · -- live: reach pc 1521 (Seg3 urns decode + Seg4 live guard).
                        have hse : accountStorageStateEq σ' σu :=
                          typedCallViaEVM_static_accountStorageStateEq hUrnsCall
                        have hslot3 : catSlotWord ⟨3⟩ σ' I = catSlotWord ⟨3⟩ σu I := by
                          simp only [catSlotWord, solcSlotWord]
                          exact accountStorageStateEq_storage_findD hse I.codeOwner ⟨3⟩ ⟨0⟩
                        rw [hslot3] at rd1399
                        have hmemI : (196 : ℕ) ≤ (catBiteIlksPostCallMem I o').size := by
                          have h := catBiteIlksPostCallMem_size I o' hilkslen hosz; omega
                        have hmemUsz : (224 : ℕ) ≤
                            (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou).size := by
                          have hbaseSz : (biteUrnsCalldataMem (biteIlkWord I) (biteUrnWord I)
                              (catBiteIlksPostCallMem I o')).size = 288 := by
                            rw [biteUrnsCalldataMem_size hmemI,
                              catBiteIlksPostCallMem_size I o' hilkslen hosz]
                          have hlen64 : ((⟨64⟩ : UInt256) ⊓ UInt256.ofNat ou.size).toNat = 64 :=
                            umin_ofNat_right_toNat_of_ge (c := 64) (n := ou.size) (by decide)
                              hurnslen hoszu
                          unfold catBiteUrnsPostCallMem
                          rw [hlen64, show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
                            write_eq_gen ou _ 128 64 (by decide) (by omega)
                              (by rw [hbaseSz]; omega),
                            ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
                            ByteArray.size_extract, ByteArray.size_extract, hbaseSz]
                          omega
                        obtain ⟨_, _, rd1521⟩ :=
                          catBiteReach1399to1521 rd1399 (by decide)
                            (by omega) (by rw [hawout9]; native_decide)
                            (le_trans (by norm_num) hmemUsz)
                            hurnslen hoszu
                            (catBiteUrnsPostCallMem_read64 I ou hmemI
                              (catBiteIlksPostCallMem_read64 I o' hilkslen hosz) hurnslen hoszu)
                            (catBiteUrnsPostCallMem_read128 I ou hmemI hurnslen hoszu)
                            (catBiteUrnsPostCallMem_read160 I ou hmemI hurnslen hoszu)
                            hlive
                        -- Seg5 (1521 → 1620): require(spot > 0 && ink*spot < art*rate).
                        set art := UInt256.ofNat (fromByteArrayBigEndian (ou.extract 32 64)) with hart
                        set ink := UInt256.ofNat (fromByteArrayBigEndian (ou.extract 0 32)) with hink
                        set iSpot := UInt256.ofNat (fromByteArrayBigEndian (o'.extract 64 96)) with hiSpot
                        set iRate := UInt256.ofNat (fromByteArrayBigEndian (o'.extract 32 64)) with hiRate
                        by_cases hfitArtRate : art.toNat * iRate.toNat < UInt256.size
                        · by_cases hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size
                          · by_cases hspotPos : 0 < iSpot.toNat
                            · by_cases hunsafe : (ink * iSpot).toNat < (art * iRate).toNat
                              · obtain ⟨_, _, rd1620⟩ :=
                                  catBiteTraceSeg5 rd1521 hspotPos hfitArtRate hfitInkSpot hunsafe
                                    (by simp)
                                -- Seg6Aw (1620 → 1708): milk-struct alloc + room = box - litter.
                                rw [hawout9] at rd1620
                                have hmf :
                                    (ou.write 0 (biteUrnsCalldataMem (biteIlkWord I) (biteUrnWord I)
                                      (o'.write 0 (catBiteIlksCalldataMem (biteIlkWord I) solcFreePtrMem)
                                        catBiteIlksOutPtr.toNat
                                        (catBiteIlksOutSize ⊓ UInt256.ofNat o'.size).toNat))
                                      (⟨128⟩ : UInt256).toNat
                                      ((⟨64⟩ : UInt256) ⊓ UInt256.ofNat ou.size).toNat)
                                      = catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou := rfl
                                rw [hmf] at rd1620
                                have h64 : (⟨64⟩ : UInt256).toNat = 64 := by native_decide
                                have h128 : (⟨128⟩ : UInt256).toNat = 128 := by native_decide
                                by_cases hle :
                                    (solcSlotWord σu I ⟨6⟩).toNat ≤ (solcSlotWord σu I ⟨5⟩).toNat
                                · obtain ⟨_, _, rd1708⟩ := catBiteReachSeg6Aw (fp := ⟨128⟩) rd1620
                                    (by native_decide)
                                    (mloadWordValue_of_readWithPadding (off := ⟨64⟩) (v := ⟨128⟩)
                                      (by rw [h64]; have := hmemUsz; omega) (by native_decide)
                                      (catBiteUrnsPostCallMem_read64 I ou hmemI
                                        (catBiteIlksPostCallMem_read64 I o' hilkslen hosz)
                                        hurnslen hoszu))
                                    (catBiteScratchMem_mload64
                                      (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou)
                                      ⟨128⟩ (biteIlkWord I)
                                      (by rw [h128]; have := hmemUsz; omega) (by native_decide)
                                      (by native_decide) (by native_decide) (by native_decide))
                                    (catBiteScratchMem_read0_64
                                      (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou)
                                      ⟨128⟩ (biteIlkWord I)
                                      (by rw [h128]; have := hmemUsz; omega) (by native_decide))
                                    (by native_decide) (by native_decide) (by native_decide)
                                    hle (by simp)
                                  -- milk-struct field reads (chop@[32+q], dunk@[64+q]).
                                  have hChop := catBiteMilkMem_mload_chop
                                    (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou)
                                    ⟨128⟩ (biteIlkWord I) (⟨96⟩ + ⟨128⟩)
                                    (biteAddrMaskWord.land
                                      (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I))))
                                    (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨1⟩))
                                    (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨2⟩))
                                    (aw := ⟨10⟩)
                                    (by rw [h128]; have := hmemUsz; omega) rfl
                                    (by native_decide) (by native_decide)
                                    (by native_decide) (by native_decide)
                                  have hDunk := catBiteMilkMem_mload_dunk
                                    (catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou)
                                    ⟨128⟩ (biteIlkWord I) (⟨96⟩ + ⟨128⟩)
                                    (biteAddrMaskWord.land
                                      (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I))))
                                    (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨1⟩))
                                    (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨2⟩))
                                    (aw := ⟨10⟩)
                                    (by rw [h128]; have := hmemUsz; omega) rfl
                                    (by native_decide) (by native_decide)
                                    (by native_decide) (by native_decide)
                                  -- name the DSMath chain so the guards are stateable.
                                  set room := (solcSlotWord σu I ⟨5⟩).sub (solcSlotWord σu I ⟨6⟩)
                                    with hroomDef
                                  set milkDunk :=
                                    solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨2⟩)
                                    with hmilkDunkDef
                                  set milkChop :=
                                    solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨1⟩)
                                    with hmilkChopDef
                                  set iDust := UInt256.ofNat (fromByteArrayBigEndian (o'.extract 128 160))
                                    with hiDustDef
                                  set dunkRoom :=
                                    (if UInt256.gt milkDunk room = ⟨0⟩ then milkDunk else room)
                                    with hdunkRoomDef
                                  set dunkRoomWad := UInt256.mul dunkRoom ⟨1000000000000000000⟩
                                    with hdunkRoomWadDef
                                  set dartDenomRate := UInt256.div dunkRoomWad iRate with hdartDenomDef
                                  set dartCandidate := UInt256.div dartDenomRate milkChop
                                    with hdartCandDef
                                  set dart :=
                                    (if UInt256.gt art dartCandidate = ⟨0⟩ then art else dartCandidate)
                                    with hdartDef
                                  set inkDart := UInt256.mul ink dart with hinkDartDef
                                  set dinkCandidate := UInt256.div inkDart art with hdinkCandDef
                                  set dink :=
                                    (if UInt256.gt ink dinkCandidate = ⟨0⟩ then ink else dinkCandidate)
                                    with hdinkDef
                                  -- Take the all-guards-hold success path; defer each fail branch.
                                  by_cases hlitterbox :
                                      (solcSlotWord σu I ⟨6⟩).toNat < (solcSlotWord σu I ⟨5⟩).toNat
                                  swap
                                  · sorry -- box ≤ litter: room = 0 / room-require branch
                                  by_cases hroomdust : iDust.toNat ≤ room.toNat
                                  swap
                                  · sorry -- dust > room: require(room ≥ dust) fails
                                  by_cases hRatePos : iRate ≠ ⟨0⟩
                                  swap
                                  · sorry -- rate = 0: DSMath div-by-zero guard
                                  by_cases hChopPos : milkChop ≠ ⟨0⟩
                                  swap
                                  · sorry -- chop = 0: DSMath div-by-zero guard
                                  by_cases hFitWad : (⟨1000000000000000000⟩ : UInt256).toNat *
                                    dunkRoom.toNat < UInt256.size
                                  swap
                                  · sorry -- dunkRoom*WAD checkedMul overflow
                                  by_cases hArtPos : art ≠ ⟨0⟩
                                  swap
                                  · sorry -- art = 0: DSMath div-by-zero guard
                                  by_cases hFitInkDart : dart.toNat * ink.toNat < UInt256.size
                                  swap
                                  · sorry -- ink*dart checkedMul overflow
                                  by_cases hDartPos : 0 < dart.toNat
                                  swap
                                  · sorry -- dart = 0: require(dart > 0) fails
                                  by_cases hDinkPos : 0 < dink.toNat
                                  swap
                                  · sorry -- dink = 0: require(dink > 0) fails
                                  by_cases hDartLim :
                                      dart.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat
                                  swap
                                  · sorry -- dart > 2^255: int256 cast bound fails
                                  by_cases hDinkLim :
                                      dink.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat
                                  swap
                                  · sorry -- dink > 2^255: int256 cast bound fails
                                  obtain ⟨_, _, rd2073⟩ :=
                                    catBiteReach1708to2073 rd1708 hlitterbox hroomdust hChop hDunk
                                      (by native_decide) (by native_decide) hRatePos hChopPos
                                      hdunkRoomDef.symm hFitWad hdunkRoomWadDef.symm
                                      hdartDenomDef.symm hdartCandDef.symm hdartDef.symm hArtPos
                                      hFitInkDart hinkDartDef.symm hdinkCandDef.symm hdinkDef.symm
                                      hDartPos hDinkPos hDartLim hDinkLim
                                  -- === STEP 1: grab CALL reach (pc 2073 → 2193) ===
                                  set base := catBiteUrnsPostCallMem I (catBiteIlksPostCallMem I o') ou
                                  clear_value base
                                  set flipW := biteAddrMaskWord.land
                                    (solcSlotWord σu I (solcMappingSlot ⟨1⟩ (biteIlkWord I)))
                                  clear_value flipW
                                  have hthisCanon :
                                      (UInt256.ofNat I.codeOwner.val).toNat < EVM.addressModulus := by
                                    have h2 : (UInt256.ofNat I.codeOwner.val).toNat
                                        = I.codeOwner.val := by
                                      apply UInt256.toNat_ofNat_of_lt
                                      exact lt_of_lt_of_le I.codeOwner.isLt
                                        (show AccountAddress.size ≤ UInt256.size from by decide)
                                    rw [h2]; change I.codeOwner.val < AccountAddress.size
                                    exact I.codeOwner.isLt
                                  -- free pointer of the milk mem: mem[0x40] = q + 96 (q = 96 + 128).
                                  have hMilkFp := catBiteMilkMem_read64 base ⟨128⟩ (biteIlkWord I)
                                    (⟨96⟩ + ⟨128⟩) flipW milkChop milkDunk (by rw [h128]; omega) rfl
                                    (by native_decide) (by native_decide)
                                  have hMilkSz := catBiteMilkMem_size base ⟨128⟩ (biteIlkWord I)
                                    (⟨96⟩ + ⟨128⟩) flipW milkChop milkDunk (by rw [h128]; omega) rfl
                                    (by native_decide) (by native_decide)
                                  have hpmemMilk :
                                      ((⟨96⟩ + ⟨128⟩) + ⟨96⟩ : UInt256).toNat ≤
                                      (catBiteMilkMem base ⟨128⟩ (biteIlkWord I) (⟨96⟩ + ⟨128⟩) flipW
                                        milkChop milkDunk).size := by
                                    rw [hMilkSz,
                                      show ((⟨96⟩ + ⟨128⟩) + ⟨96⟩ : UInt256).toNat = 320 from by
                                        native_decide,
                                      show ((⟨96⟩ + ⟨128⟩ : UInt256).toNat + 96) = 320 from by
                                        native_decide]
                                    exact le_max_right _ _
                                  by_cases hGrabCode :
                                      Reasoning.Theory.uniswapExtCodeSizeWord σu
                                        (UInt256.land (solcSlotWord σu I ⟨3⟩) biteAddrMaskWord) = ⟨0⟩
                                  · sorry -- grab vat has no code → divergence leaf
                                  · obtain ⟨cAg, σg, zg, og, Ag, kg, Cg, rd2193, hGrabCall, hoszg⟩ :=
                                      catBiteReachGrabAw rd2073 hMilkFp (by native_decide) hpmemMilk
                                        (by native_decide) (by native_decide) (by native_decide)
                                        hthisCanon (hDinkLim.trans_eq (by native_decide))
                                        (hDartLim.trans_eq (by native_decide)) hGrabCode hdepth
                                    cases zg with
                                    | false => sorry -- grab CALL failed (success = 0) → divergence
                                    | true =>
                                      -- === STEP 2: fess CALL reach (pc 2193 → 2300) ===
                                      by_cases hRateFit :
                                          iRate.toNat * dart.toNat < UInt256.size
                                      swap
                                      · sorry -- iRate*dart checkedMul overflow → divergence
                                      -- `with_reducible` freezes `MachineState.M` (reducible in this
                                      -- file, unlike BiteBody's section) so the `catBiteAwStepL_toNat`
                                      -- defeq does not unfold M+`UInt256.size` and blow up heartbeats.
                                      have hawF := by
                                        with_reducible
                                          exact catBiteAwStepL_toNat ⟨10⟩
                                            (⟨96⟩ + ⟨128⟩ + ⟨96⟩ + ⟨164⟩ : UInt256).toNat
                                            (catBiteMltL ⟨10⟩
                                              (⟨96⟩ + ⟨128⟩ + ⟨96⟩ + ⟨164⟩ : UInt256).toNat
                                              (by native_decide))
                                      have hGrabSz := catBiteGrabCalldataMemP_size
                                        (⟨96⟩ + ⟨128⟩ + ⟨96⟩) (biteIlkWord I)
                                        (biteAddrMaskWord.land (calldataWord I.calldata 36))
                                        (UInt256.ofNat I.codeOwner.val) (solcSlotWord σu I ⟨4⟩) dink dart
                                        hpmemMilk (by native_decide)
                                      by_cases hFessCode :
                                          Reasoning.Theory.uniswapExtCodeSizeWord σg
                                            (UInt256.land biteAddrMaskWord (solcSlotWord σg I ⟨4⟩)) = ⟨0⟩
                                      · sorry -- fess vow has no code → divergence leaf
                                      · obtain ⟨cAf, σf, zf, ofb, Af, kf, Cf, rd2300, hFessCall, hoszf⟩ :=
                                          catBiteReachFessAw rd2193 (by decide) hRateFit rfl
                                            (by rw [catBiteGrabCalldataMemP_read64 (⟨96⟩ + ⟨128⟩ + ⟨96⟩)
                                                  _ _ _ _ _ _ (by native_decide) hpmemMilk
                                                  (by native_decide)]
                                                exact hMilkFp)
                                            (by native_decide) (le_trans (by native_decide) hGrabSz)
                                            (by rw [hawF]; native_decide) (by rw [hawF]; native_decide)
                                            (by native_decide) hFessCode hdepth
                                        -- STEP A: fess CALL status split.
                                        by_cases hzf : zf = true
                                        swap
                                        · sorry -- fess CALL failed (success = 0) → divergence
                                        subst hzf
                                        -- awF (the 2300 active-words) collapses to ⟨17⟩.
                                        have hinner :
                                            (catBiteAwStepL ⟨10⟩
                                              (⟨96⟩ + ⟨128⟩ + ⟨96⟩ + ⟨164⟩ : UInt256).toNat).toNat = 17 := by
                                          rw [hawF]; native_decide
                                        have hawF17 :
                                            (catBiteAwStepL (catBiteAwStepL ⟨10⟩
                                                (⟨96⟩ + ⟨128⟩ + ⟨96⟩ + ⟨164⟩ : UInt256).toNat)
                                              (⟨4⟩ + (⟨96⟩ + ⟨128⟩ + ⟨96⟩) : UInt256).toNat) = ⟨17⟩ := by
                                          apply u256_inj
                                          with_reducible
                                            rw [catBiteAwStepL_toNat _ _ (catBiteMltL _ _ (by native_decide))]
                                          rw [hinner]; native_decide
                                        rw [hawF17] at rd2300
                                        -- Memory-size facts: the fess overlay never shrinks the grab
                                        -- calldata region, so it keeps the `[0, 484)` window the kick
                                        -- calldata build needs (grab already wrote up to `p+164`).
                                        have hwrite_eq : ∀ (a : ByteArray) (w : UInt256) (off : ℕ),
                                            off ≤ a.size →
                                            ((UInt256.toByteArray w).write 0 a off 32).size
                                              = max a.size (off + 32) := fun a w off hoff =>
                                          toByteArray_write32_size_of_le a w off a.size
                                            (max a.size (off + 32)) rfl hoff rfl
                                        have hfess_ge : ∀ (m : ByteArray) (dr : UInt256),
                                            (⟨96⟩ + ⟨128⟩ + ⟨96⟩ : UInt256).toNat ≤ m.size →
                                            m.size ≤ (catBiteFessCalldataMemP (⟨96⟩ + ⟨128⟩ + ⟨96⟩) dr m).size := by
                                          intro m dr hm
                                          unfold catBiteFessCalldataMemP catBiteFessSelMemP
                                          rw [hwrite_eq _ dr (⟨4⟩ + (⟨96⟩ + ⟨128⟩ + ⟨96⟩) : UInt256).toNat
                                              (by rw [hwrite_eq m _ (⟨96⟩ + ⟨128⟩ + ⟨96⟩ : UInt256).toNat hm]
                                                  exact le_trans (by native_decide) (le_max_right _ _)),
                                            hwrite_eq m _ (⟨96⟩ + ⟨128⟩ + ⟨96⟩ : UInt256).toNat hm]
                                          omega
                                        have hgrab_le :
                                            (⟨96⟩ + ⟨128⟩ + ⟨96⟩ : UInt256).toNat ≤ _ :=
                                          le_trans (show (⟨96⟩ + ⟨128⟩ + ⟨96⟩ : UInt256).toNat
                                            ≤ (⟨96⟩ + ⟨128⟩ + ⟨96⟩ + ⟨164⟩ : UInt256).toNat + 32 from by
                                              native_decide) hGrabSz
                                        have hfess_mono := hfess_ge _ (dart.mul iRate) hgrab_le
                                        have hpmem_kick :
                                            (⟨96⟩ + ⟨128⟩ + ⟨96⟩ : UInt256).toNat + 164 ≤ _ :=
                                          le_trans (le_trans (show (⟨96⟩ + ⟨128⟩ + ⟨96⟩ : UInt256).toNat + 164
                                            ≤ (⟨96⟩ + ⟨128⟩ + ⟨96⟩ + ⟨164⟩ : UInt256).toNat + 32 from by
                                              native_decide) hGrabSz) hfess_mono
                                        -- STEP B: name the DSMath tab chain; split the two overflow guards.
                                        set dartRate := UInt256.mul dart iRate with hdartRateDef
                                        set tabBase := UInt256.mul dartRate milkChop with htabBaseDef
                                        set tab := UInt256.div tabBase ⟨1000000000000000000⟩ with htabDef
                                        set litterNew := solcSlotWord σf I ⟨6⟩ + tab with hlitterNewDef
                                        by_cases hChopFit : milkChop.toNat * dartRate.toNat < UInt256.size
                                        swap
                                        · sorry -- tabBase = dartRate*chop checkedMul overflow → divergence
                                        by_cases hLitFit :
                                            (solcSlotWord σf I ⟨6⟩).toNat + tab.toNat < UInt256.size
                                        swap
                                        · sorry -- litter + tab checkedAdd overflow → divergence
                                        -- 2300 → 2383: fess-success guard + tab arithmetic + litter SSTORE.
                                        obtain ⟨_, _, rd2383⟩ :=
                                          catBiteReach2300to2383 (milkChop := milkChop) rd2300 (by decide)
                                            (by
                                              rw [if_neg (by
                                                    refine not_or.mpr ⟨?_, ?_⟩
                                                    · have e : (⟨32⟩ + (⟨96⟩ + ⟨128⟩) : UInt256).toNat = 256 :=
                                                        by native_decide
                                                      have e2 : (⟨96⟩ + ⟨128⟩ + ⟨96⟩ : UInt256).toNat = 320 :=
                                                        by native_decide
                                                      have := hpmem_kick; omega
                                                    · native_decide),
                                                catBiteFessCalldataMemP_readBelow (⟨96⟩ + ⟨128⟩ + ⟨96⟩) dartRate
                                                  (⟨32⟩ + (⟨96⟩ + ⟨128⟩) : UInt256).toNat (by native_decide)
                                                  hgrab_le (by native_decide),
                                                catBiteGrabCalldataMemP_readBelow (⟨96⟩ + ⟨128⟩ + ⟨96⟩)
                                                  (biteIlkWord I) (biteAddrMaskWord.land (calldataWord I.calldata 36))
                                                  (UInt256.ofNat I.codeOwner.val) (solcSlotWord σu I ⟨4⟩) dink dart
                                                  (⟨32⟩ + (⟨96⟩ + ⟨128⟩) : UInt256).toNat (by native_decide)
                                                  hpmemMilk (by native_decide)]
                                              rw [if_neg (by
                                                    refine not_or.mpr ⟨?_, ?_⟩
                                                    · have e1 : (⟨32⟩ + (⟨96⟩ + ⟨128⟩) : UInt256).toNat = 256 :=
                                                        by native_decide
                                                      have e2 : (⟨96⟩ + ⟨128⟩ + ⟨96⟩ : UInt256).toNat = 320 :=
                                                        by native_decide
                                                      have := hpmemMilk; omega
                                                    · native_decide)] at hChop
                                              exact hChop)
                                            (by native_decide) (by native_decide) hperm hRateFit hChopFit hLitFit
                                            hdartRateDef.symm htabBaseDef.symm htabDef.symm hlitterNewDef.symm
                                        -- STEP C: kick CALL reach (2383 → 2532), all at free ptr `p`.
                                        by_cases hKickCode :
                                            Reasoning.Theory.uniswapExtCodeSizeWord
                                              (sstoreAccountMap I.codeOwner σf ⟨6⟩ litterNew)
                                              (UInt256.land biteAddrMaskWord flipW) = ⟨0⟩
                                        · sorry -- kick flip target has no code → divergence leaf
                                        · -- flip@q and free-ptr@64 reads through the fess/grab overlay.
                                          have hFlipRead :
                                              (catBiteFessCalldataMemP (⟨96⟩ + ⟨128⟩ + ⟨96⟩) dartRate
                                                (catBiteGrabCalldataMemP (⟨96⟩ + ⟨128⟩ + ⟨96⟩) (biteIlkWord I)
                                                  (biteAddrMaskWord.land (calldataWord I.calldata 36))
                                                  (UInt256.ofNat I.codeOwner.val) (solcSlotWord σu I ⟨4⟩) dink dart
                                                  (catBiteMilkMem base ⟨128⟩ (biteIlkWord I) (⟨96⟩ + ⟨128⟩) flipW
                                                    milkChop milkDunk))).readWithPadding
                                                (⟨96⟩ + ⟨128⟩ : UInt256).toNat 32
                                                = (flipW : UInt256).toByteArray := by
                                            rw [catBiteFessCalldataMemP_readBelow (⟨96⟩ + ⟨128⟩ + ⟨96⟩) dartRate
                                                  (⟨96⟩ + ⟨128⟩ : UInt256).toNat (by native_decide) hgrab_le
                                                  (by native_decide),
                                                catBiteGrabCalldataMemP_readBelow (⟨96⟩ + ⟨128⟩ + ⟨96⟩)
                                                  (biteIlkWord I) (biteAddrMaskWord.land (calldataWord I.calldata 36))
                                                  (UInt256.ofNat I.codeOwner.val) (solcSlotWord σu I ⟨4⟩) dink dart
                                                  (⟨96⟩ + ⟨128⟩ : UInt256).toNat (by native_decide) hpmemMilk
                                                  (by native_decide),
                                                catBiteMilkMem_readflip base ⟨128⟩ (biteIlkWord I) (⟨96⟩ + ⟨128⟩)
                                                  flipW milkChop milkDunk (by rw [h128]; have := hmemUsz; omega)
                                                  rfl (by native_decide) (by native_decide)]
                                          have hread64F :
                                              (catBiteFessCalldataMemP (⟨96⟩ + ⟨128⟩ + ⟨96⟩) dartRate
                                                (catBiteGrabCalldataMemP (⟨96⟩ + ⟨128⟩ + ⟨96⟩) (biteIlkWord I)
                                                  (biteAddrMaskWord.land (calldataWord I.calldata 36))
                                                  (UInt256.ofNat I.codeOwner.val) (solcSlotWord σu I ⟨4⟩) dink dart
                                                  (catBiteMilkMem base ⟨128⟩ (biteIlkWord I) (⟨96⟩ + ⟨128⟩) flipW
                                                    milkChop milkDunk))).readWithPadding 64 32
                                                = (⟨96⟩ + ⟨128⟩ + ⟨96⟩ : UInt256).toByteArray := by
                                            rw [catBiteFessCalldataMemP_read64 (⟨96⟩ + ⟨128⟩ + ⟨96⟩) dartRate
                                                  (by native_decide) hgrab_le (by native_decide),
                                                catBiteGrabCalldataMemP_read64 (⟨96⟩ + ⟨128⟩ + ⟨96⟩) (biteIlkWord I)
                                                  (biteAddrMaskWord.land (calldataWord I.calldata 36))
                                                  (UInt256.ofNat I.codeOwner.val) (solcSlotWord σu I ⟨4⟩) dink dart
                                                  (by native_decide) hpmemMilk (by native_decide)]
                                            exact hMilkFp
                                          obtain ⟨cAk, σk, zk, ok, Ak, awk, kk, Ck, rd2532, hKickCall, hoszk,
                                              hRDret⟩ :=
                                            catBiteReachKickC rd2383
                                              (mloadWordValue_of_readWithPadding
                                                (lt_of_lt_of_le (show (⟨96⟩ + ⟨128⟩ : UInt256).toNat
                                                  < (⟨96⟩ + ⟨128⟩ + ⟨96⟩ : UInt256).toNat + 164 from by
                                                    native_decide) hpmem_kick)
                                                (by native_decide) hFlipRead)
                                              (mloadWordValue_of_readWithPadding
                                                (lt_of_lt_of_le (show (⟨64⟩ : UInt256).toNat
                                                  < (⟨96⟩ + ⟨128⟩ + ⟨96⟩ : UInt256).toNat + 164 from by
                                                    native_decide) hpmem_kick)
                                                (by native_decide)
                                                (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by native_decide]
                                                    exact hread64F))
                                              hread64F (by native_decide) (by native_decide) (by native_decide)
                                              (by native_decide) (by native_decide) hpmem_kick (by native_decide)
                                              hperm hRateFit hKickCode hdepth
                                          -- STEP D: take the kick-success / long-enough-return branch.
                                          by_cases hzk : zk = true
                                          swap
                                          · sorry -- kick CALL failed (success = 0) → divergence
                                          by_cases hk32 : 32 ≤ ok.size
                                          swap
                                          · sorry -- kick return decode short (returndatasize < 32) → divergence
                                          have hret := hRDret hzk hk32
                                          sorry -- catBiteSuccessBranch frontier
                                · sorry -- room underflow (box < litter)
                              · sorry -- require(unsafe) fails → revert leaf
                            · sorry -- spot = 0 (short-circuit) → revert leaf
                          · sorry -- inkSpot checkedMul overflow → revert leaf
                        · sorry -- artRate checkedMul overflow → revert leaf
                      · -- require(live == 1) fails → revert leaf.
                        sorry
                    · -- urns return decode short (`returndatasize < 64`).
                      sorry
            · -- ilks return decode short (`returndatasize < 160`).
              sorry
      · -- ilks STATICCALL hits the call-depth limit (depth = 1024).
        sorry

end Benchmarks.Dss.Cat
