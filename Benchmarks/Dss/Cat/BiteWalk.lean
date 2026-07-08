import Benchmarks.Dss.Cat.BiteBody
import Benchmarks.Dss.Cat.BiteRevertBranch

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
                    -- urns STATICCALL returned success = 0 → revert leaf.
                    have hdepthNe : I.depth ≠ 1024 := by omega
                    have hmask : biteAddrMaskWord = solcAddrMask := by native_decide
                    have hposNe : ∀ w : UInt256, w ≠ ⟨0⟩ → 0 < w.toNat :=
                      fun w hw => Nat.pos_of_ne_zero (fun h => hw (uint256_toNat_eq_zero h))
                    have addrId : ∀ a : AccountAddress, EVM.address a.val = a := by
                      intro a; apply Fin.ext
                      show a.val % EVM.addressModulus = a.val
                      rw [show EVM.addressModulus = AccountAddress.size from by decide]
                      exact Nat.mod_eq_of_lt a.isLt
                    have codePos : ∀ (e : EVM.State) (w : UInt256),
                        uniswapExtCodeSizeWord e.accountMap w ≠ ⟨0⟩ →
                        0 < (UInt256.ofNat ((e.lookupAccount
                          (AccountAddress.ofUInt256 w)).option 0 (fun acc => acc.code.size))).toNat := by
                      intro e w hw
                      unfold uniswapExtCodeSizeWord at hw
                      simp only [State.lookupAccount]
                      cases hf : e.accountMap.find? (AccountAddress.ofUInt256 w) with
                      | none => rw [hf] at hw; simp [Option.option] at hw
                      | some acc =>
                          rw [hf] at hw
                          simp only [Option.option, Function.comp] at hw ⊢
                          exact hposNe _ hw
                    obtain ⟨σs, As, hIlksSolm, hEqIlk⟩ := catBiteMapIlksCall hAccounts hIlksCall
                    have htw : catBiteVatTargetWord σ_evm I = catBiteVatTargetWord σ_solm I := by
                      simp only [catBiteVatTargetWord, catAddressReturnWord, catSlotWord, solcSlotWord]
                      rw [accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩]
                    have htgt : (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I))
                        = EVM.address (biteVatAddr (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) := by
                      rw [htw]; exact catBiteVatEvmAddr_eq_target.symm
                    rw [htgt] at hIlksSolm
                    obtain ⟨AU, hUrnsCall'⟩ :=
                      biteTypedCallZeroSetSubstate hUrnsCall (by simpa [initState] using hdepthNe) A'
                    obtain ⟨σus, Aus, hUrnsSolm, hEqUrn⟩ := catBiteMapCall hEqIlk hUrnsCall' hdepthNe
                    have hslot3 : catSlotWord ⟨3⟩ σ' I = catSlotWord ⟨3⟩ σs I := by
                      simp only [catSlotWord, solcSlotWord]
                      rw [accountMapEquiv_storage_findD hEqIlk.accountMap I.codeOwner ⟨3⟩ ⟨0⟩]
                    set eI := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                      accountMap := σs, substate := As, createdAccounts := cA' } with heIdef
                    have heIam : eI.accountMap = σs := rfl
                    have heIee : eI.executionEnv = I := rfl
                    have haddr : EVM.address (biteVatAddr eI).val
                        = AccountAddress.ofUInt256 ((catSlotWord ⟨3⟩ σs I).land biteAddrMaskWord) := by
                      rw [addrId, accountAddress_ofUInt256_eq_ofNat_toNat]
                      simp only [biteVatAddr, catSlotWord, heIam, heIee, hmask]
                    rw [hslot3, ← haddr] at hUrnsSolm
                    have hvatCodeIlk : 0 < (UInt256.ofNat
                        ((eI.lookupAccount (biteVatAddr eI)).option 0 (fun acc => acc.code.size))).toNat := by
                      have hva : biteVatAddr eI
                          = AccountAddress.ofUInt256 (catBiteVatTargetWord σs I) := by
                        rw [accountAddress_ofUInt256_eq_ofNat_toNat]
                        simp only [biteVatAddr, catBiteVatTargetWord, catAddressReturnWord,
                          catSlotWord, heIam, heIee]
                      rw [hva]
                      refine codePos eI (catBiteVatTargetWord σs I) ?_
                      rw [heIam, show catBiteVatTargetWord σs I
                            = (catSlotWord ⟨3⟩ σs I).land biteAddrMaskWord from by
                          simp only [catBiteVatTargetWord, catAddressReturnWord, hmask],
                        ← hslot3, ← uniswapExtCodeSizeWord_accountMapEquiv hEqIlk.accountMap]
                      exact hUrnsVatCode
                    refine catBiteUrnsFailLeaf hcode hdispatch hdecode rd1399 hoszu
                      (by simp only [List.length_cons, List.length_nil]; omega) ?_
                    exact catBiteSourceUrnsFailRevert hwv
                      (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm
                      (catBiteIlksDecode_ok hilkslen) hvatCodeIlk hUrnsSolm
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
                                  · -- rate = 0 unreachable: hunsafe forces art·rate > 0.
                                    exfalso
                                    have hr0 : iRate = ⟨0⟩ := not_not.mp hRatePos
                                    have hz : (art * iRate).toNat = 0 := by
                                      rw [u256_mul_op_toNat, hr0,
                                        show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.mul_zero, Nat.zero_mod]
                                    omega
                                  by_cases hChopPos : milkChop ≠ ⟨0⟩
                                  swap
                                  · sorry -- chop = 0: DSMath div-by-zero guard
                                  by_cases hFitWad : (⟨1000000000000000000⟩ : UInt256).toNat *
                                    dunkRoom.toNat < UInt256.size
                                  swap
                                  · sorry -- dunkRoom*WAD checkedMul overflow
                                  by_cases hArtPos : art ≠ ⟨0⟩
                                  swap
                                  · -- art = 0 unreachable: hunsafe forces art·rate > 0.
                                    exfalso
                                    have ha0 : art = ⟨0⟩ := not_not.mp hArtPos
                                    have hz : (art * iRate).toNat = 0 := by
                                      rw [u256_mul_op_toNat, ha0,
                                        show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.zero_mul, Nat.zero_mod]
                                    omega
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
                                    with hflipWDef
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
                                    | false =>
                                      -- grab CALL failed (success = 0) → revert leaf.
                                      have hdepthNe : I.depth ≠ 1024 := by omega
                                      have hmask : biteAddrMaskWord = solcAddrMask := by native_decide
                                      have hposNe : ∀ w : UInt256, w ≠ ⟨0⟩ → 0 < w.toNat :=
                                        fun w hw => Nat.pos_of_ne_zero (fun h => hw (uint256_toNat_eq_zero h))
                                      have addrId : ∀ a : AccountAddress, EVM.address a.val = a := by
                                        intro a; apply Fin.ext
                                        show a.val % EVM.addressModulus = a.val
                                        rw [show EVM.addressModulus = AccountAddress.size from by decide]
                                        exact Nat.mod_eq_of_lt a.isLt
                                      have codePos : ∀ (e : EVM.State) (w : UInt256),
                                          uniswapExtCodeSizeWord e.accountMap w ≠ ⟨0⟩ →
                                          0 < (UInt256.ofNat ((e.lookupAccount
                                            (AccountAddress.ofUInt256 w)).option 0
                                            (fun acc => acc.code.size))).toNat := by
                                        intro e w hw
                                        unfold uniswapExtCodeSizeWord at hw
                                        simp only [State.lookupAccount]
                                        cases hf : e.accountMap.find? (AccountAddress.ofUInt256 w) with
                                        | none => rw [hf] at hw; simp [Option.option] at hw
                                        | some acc =>
                                            rw [hf] at hw
                                            simp only [Option.option, Function.comp] at hw ⊢
                                            exact hposNe _ hw
                                      have hAddrRT : ∀ a : AccountAddress,
                                          AccountAddress.ofNat (UInt256.ofNat a.val).toNat = a := by
                                        intro a
                                        have h1 : (UInt256.ofNat a.val).toNat = a.val :=
                                          UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le a.isLt
                                            (show AccountAddress.size ≤ UInt256.size from by decide))
                                        rw [h1]; apply Fin.ext
                                        simp only [AccountAddress.ofNat, Fin.ofNat]
                                        exact Nat.mod_eq_of_lt a.isLt
                                      have hbytes : biteIlkBytes I = EVM.Word.toBytesBE (biteIlkWord I) := by
                                        have hlen32 : (biteIlkBytes I).length = 32 := by
                                          simp only [biteIlkBytes, List.length_take, List.length_drop]
                                          have htlen : I.calldata.toList.length = I.calldata.size := by
                                            rw [byteArray_toList_eq, Array.length_toList]; rfl
                                          rw [htlen]; omega
                                        have hword : ABI.bytesToWord (biteIlkBytes I) = biteIlkWord I := by
                                          simpa [biteIlkBytes, biteIlkWord] using
                                            (decode_word_at_eq_any I.calldata 4 (by simpa using hsz36))
                                        have hto := toBytesBE_bytesToWord_of_length (bs := biteIlkBytes I) hlen32
                                        rw [hword] at hto; exact hto.symm
                                      have uminEq : ∀ a b : UInt256,
                                          (if UInt256.gt a b = ⟨0⟩ then a else b) = umin a b := by
                                        intro a b; unfold umin
                                        by_cases h : a.toNat ≤ b.toNat
                                        · rw [if_pos (ugt_zero h), if_pos h]
                                        · rw [if_neg (by rw [ugt_one (by omega)]; decide), if_neg h]
                                      have hwad : wadU = ⟨1000000000000000000⟩ := by native_decide
                                      have hsl : (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat =
                                          57896044618658097711785492504343953926634992332820282019728792003956564819968 := by
                                        native_decide
                                      have hbr : ∀ (o : ByteArray) (k : ℕ), k + 32 ≤ o.size →
                                          ABI.bytesToWord ((o.toList.drop k).take 32) =
                                            UInt256.ofNat (fromByteArrayBigEndian (o.extract k (k + 32))) := by
                                        intro o k h
                                        rw [decode_word_at_eq_any o k h, uInt256OfByteArray_eq]
                                        congr 1; unfold fromByteArrayBigEndian; congr 1
                                        rw [byteArray_toList_eq (o.readBytes k 32),
                                          readBytes_at_toList_any o k h,
                                          byteArray_toList_eq (o.extract k (k + 32)),
                                          ByteArray.data_extract, Array.toList_extract,
                                          List.extract_eq_take_drop]
                                        simp
                                      obtain ⟨σs, As, σus, Aus, hIlksSolm, hUrnsSolm, hAmEq, hvatCodeIlkS⟩ :=
                                        catBiteMapUrns hAccounts hdepthNe hUrnsVatCode hIlksCall hUrnsCall
                                      have slotEqUS : ∀ s : UInt256, solcSlotWord σus I s = solcSlotWord σu I s := by
                                        intro s; simp only [solcSlotWord]
                                        rw [accountMapEquiv_storage_findD hAmEq I.codeOwner s ⟨0⟩]
                                      set eUrnE := { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                                        accountMap := σu, substate := Au, createdAccounts := cAu } with heUrnEdef
                                      set eUrnS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                                        accountMap := σus, substate := Aus, createdAccounts := cAu } with heUrnSdef
                                      have hEqU : EVMStateEquiv eUrnE eUrnS := ⟨rfl, rfl, hAmEq⟩
                                      have heUEam : eUrnE.accountMap = σu := rfl
                                      have heUEee : eUrnE.executionEnv = I := rfl
                                      have heUSam : eUrnS.accountMap = σus := rfl
                                      have heUSee : eUrnS.executionEnv = I := rfl
                                      -- eUrnE-side named quantities (identical to the walk's `set` values).
                                      have hboxB : biteBoxW eUrnE = solcSlotWord σu I ⟨5⟩ := by
                                        simp only [biteBoxW, catSlotWord, heUEam, heUEee]
                                      have hlitB : biteLitW eUrnE = solcSlotWord σu I ⟨6⟩ := by
                                        simp only [biteLitW, catSlotWord, heUEam, heUEee]
                                      have hchopB : biteChopW I eUrnE = milkChop := by
                                        rw [hmilkChopDef]
                                        simp only [biteChopW, catSlotWord, heUEam, heUEee, biteChopSlot,
                                          biteFlipSlot_eq hsz36]
                                      have hdunkB : biteDunkW I eUrnE = milkDunk := by
                                        rw [hmilkDunkDef]
                                        simp only [biteDunkW, catSlotWord, heUEam, heUEee, biteDunkSlot,
                                          biteFlipSlot_eq hsz36]
                                      have hroomB : biteRoomV eUrnE = room := by
                                        rw [hroomDef]
                                        simp only [biteRoomV, biteBoxW, biteLitW, catSlotWord, heUEam, heUEee]
                                      have hdunkroomB : biteDunkRoomV I eUrnE = dunkRoom := by
                                        rw [hdunkRoomDef, uminEq milkDunk room]
                                        simp only [biteDunkRoomV, hdunkB, hroomB]
                                      have hdartvB : biteDartV I eUrnE iRate art = dart := by
                                        have hcand : biteDartCandV I eUrnE iRate = dartCandidate := by
                                          simp only [biteDartCandV, biteDartDenomV, biteDunkRoomWadV,
                                            hchopB, hdunkroomB, hwad, hdartCandDef, hdartDenomDef,
                                            hdunkRoomWadDef]
                                          rfl
                                        rw [hdartDef, uminEq art dartCandidate]
                                        simp only [biteDartV, hcand]
                                      have hdinkvB : biteDinkV I eUrnE iRate art ink = dink := by
                                        have hcand : biteDinkCandV I eUrnE iRate art ink = dinkCandidate := by
                                          simp only [biteDinkCandV, biteInkDartV, hdartvB, hdinkCandDef,
                                            hinkDartDef]
                                          rfl
                                        rw [hdinkDef, uminEq ink dinkCandidate]
                                        simp only [biteDinkV, hcand]
                                      -- ilks / urns decode on the σ_solm side (same output bytes).
                                      have hIlksDec : config.externalABI.decode? "ilks" o' =
                                          some [bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 0 32))),
                                            bw iRate, bw iSpot,
                                            bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 96 128))),
                                            bw iDust] := by
                                        have h := catBiteIlksDecode_ok hilkslen
                                        rw [hbr o' 0 (by omega), hbr o' 32 (by omega), hbr o' 64 (by omega),
                                          hbr o' 96 (by omega), hbr o' 128 (by omega)] at h
                                        exact h
                                      have hUrnsDec : config.externalABI.decode? "urns" ou =
                                          some [bw ink, bw art] := by
                                        have h := catBiteUrnsDecode_ok hurnslen
                                        rw [hbr ou 0 (by omega), hbr ou 32 (by omega)] at h
                                        exact h
                                      -- map the (failed) grab CALL to σ_solm.
                                      obtain ⟨AG, hGrabCall'⟩ :=
                                        biteTypedCallZeroSetSubstate hGrabCall
                                          (by simpa [initState] using hdepthNe) Au
                                      obtain ⟨σgs, Ags, hGrabSolm, _hEqGrab⟩ :=
                                        catBiteMapCall hEqU hGrabCall' hdepthNe
                                      -- reshape target + args of the mapped grab call to source-revert form.
                                      have htgtU : EVM.address (biteVatAddr eUrnS).val =
                                          AccountAddress.ofUInt256 ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord) := by
                                        rw [← biteVatAddr_eq_of_equiv hEqU, addrId,
                                          accountAddress_ofUInt256_eq_ofNat_toNat, hmask]
                                        simp only [biteVatAddr, catSlotWord, heUEam, heUEee]
                                      have h1 : biteIlkVal I =
                                          Value.fixedBytes bytes32Width (EVM.Word.toBytesBE (biteIlkWord I)) := by
                                        simp only [biteIlkVal, hbytes]
                                      have h2 : biteUrnVal I = Value.address (AccountAddress.ofNat
                                          (biteAddrMaskWord.land
                                            (biteAddrMaskWord.land (calldataWord I.calldata 36))).toNat) := by
                                        rw [hurn]
                                        simp only [biteUrnVal, biteUrnWord, biteUrnAddr, hAddrRT]
                                      have h3 : (eUrnS.executionEnv.codeOwner : AccountAddress) =
                                          AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat := by
                                        rw [heUSee]; exact (hAddrRT I.codeOwner).symm
                                      have h4 : biteVowAddrV eUrnS = AccountAddress.ofNat
                                          (biteAddrMaskWord.land (solcSlotWord σu I ⟨4⟩)).toNat := by
                                        rw [← biteVowAddrV_eq_of_equiv hEqU]
                                        simp only [biteVowAddrV, catSlotWord, heUEam, heUEee, hmask]
                                        rw [u256_land_comm]
                                      have hdartvBS : biteDartV I eUrnS iRate art = dart := by
                                        rw [← biteDartV_eq_of_equiv hEqU]; exact hdartvB
                                      have hdinkvBS : biteDinkV I eUrnS iRate art ink = dink := by
                                        rw [← biteDinkV_eq_of_equiv hEqU]; exact hdinkvB
                                      have hGrabCodeS :
                                          ¬ Reasoning.Theory.uniswapExtCodeSizeWord σus
                                            ((solcSlotWord σus I ⟨3⟩).land biteAddrMaskWord) = ⟨0⟩ := by
                                        rw [slotEqUS ⟨3⟩, ← uniswapExtCodeSizeWord_accountMapEquiv hAmEq]
                                        exact hGrabCode
                                      -- reshape the mapped grab call to the source-revert form.
                                      rw [hperm, ← htgtU, ← h1, ← h2, ← h3, ← h4, ← hdinkvBS, ← hdartvBS]
                                        at hGrabSolm
                                      -- feed the leaf + source-revert.
                                      have hlive' : catSlotWord ⟨2⟩ eUrnS.accountMap eUrnS.executionEnv = ⟨1⟩ := by
                                        rw [← biteSlotEqOfEquiv hEqU ⟨2⟩]; exact hlive
                                      refine catBiteGrabFailLeaf hcode hdispatch hdecode (by
                                        simpa using rd2193) hoszg (by
                                        simp only [List.length_cons, List.length_nil]; omega) ?_
                                      refine catBiteSourceGrabFailRevert hwv
                                        (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm hIlksDec
                                        hvatCodeIlkS hUrnsSolm hUrnsDec hlive' hsz36 hfitInkSpot hfitArtRate
                                        hspotPos (hposNe iRate hRatePos) hunsafe ?_ ?_ ?_ ?_ ?_
                                        (hposNe art hArtPos) ?_ ?_ ?_ ?_ ?_ hGrabSolm
                                      · -- hlitLtBox
                                        rw [← biteLitW_eq_of_equiv hEqU, ← biteBoxW_eq_of_equiv hEqU, hlitB, hboxB]
                                        exact hlitterbox
                                      · -- hroomGeDust
                                        rw [← biteRoomV_eq_of_equiv hEqU, hroomB]; exact hroomdust
                                      · -- hfitDunkRoomWad
                                        rw [← biteDunkRoomV_eq_of_equiv hEqU, hdunkroomB, hwad, Nat.mul_comm]
                                        exact hFitWad
                                      · -- hmilkChopPos
                                        rw [← biteChopW_eq_of_equiv hEqU, hchopB]; exact hposNe milkChop hChopPos
                                      · -- hfitInkDart
                                        rw [← biteDartV_eq_of_equiv hEqU, hdartvB, Nat.mul_comm]; exact hFitInkDart
                                      · -- hdartPos
                                        rw [← biteDartV_eq_of_equiv hEqU, hdartvB]; exact hDartPos
                                      · -- hdinkPos
                                        rw [← biteDinkV_eq_of_equiv hEqU, hdinkvB]; exact hDinkPos
                                      · -- hdartLim
                                        rw [← biteDartV_eq_of_equiv hEqU, hdartvB]; simp only [int256Limit]
                                        exact Int.ofNat_le.mpr (hDartLim.trans_eq hsl)
                                      · -- hdinkLim
                                        rw [← biteDinkV_eq_of_equiv hEqU, hdinkvB]; simp only [int256Limit]
                                        exact Int.ofNat_le.mpr (hDinkLim.trans_eq hsl)
                                      · -- hvatCodeMid
                                        have haddr : biteVatAddr eUrnS =
                                            AccountAddress.ofUInt256 (catBiteVatTargetWord σus I) := by
                                          rw [accountAddress_ofUInt256_eq_ofNat_toNat]
                                          simp only [biteVatAddr, catBiteVatTargetWord, catAddressReturnWord,
                                            catSlotWord, heUSam, heUSee]
                                        rw [haddr]
                                        refine codePos eUrnS (catBiteVatTargetWord σus I) ?_
                                        rw [heUSam, show catBiteVatTargetWord σus I =
                                              (solcSlotWord σus I ⟨3⟩).land biteAddrMaskWord from by
                                            simp only [catBiteVatTargetWord, catAddressReturnWord, catSlotWord,
                                              hmask]]
                                        exact hGrabCodeS
                                    | true =>
                                      -- === STEP 2: fess CALL reach (pc 2193 → 2300) ===
                                      by_cases hRateFit :
                                          iRate.toNat * dart.toNat < UInt256.size
                                      swap
                                      · -- iRate·dart overflow unreachable: dart ≤ art ⇒ iRate·dart ≤ art·iRate < size.
                                        have hdart_le : dart.toNat ≤ art.toNat := by
                                          rw [hdartDef]; split
                                          · exact le_refl _
                                          · rename_i h
                                            by_contra hc
                                            exact h (ugt_zero (by omega))
                                        exact absurd
                                          (calc iRate.toNat * dart.toNat
                                                ≤ iRate.toNat * art.toNat :=
                                                  Nat.mul_le_mul (Nat.le_refl _) hdart_le
                                              _ = art.toNat * iRate.toNat := Nat.mul_comm _ _
                                              _ < UInt256.size := hfitArtRate)
                                          hRateFit
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
                                        · -- fess CALL failed (success = 0) → revert leaf.
                                          have hdepthNe : I.depth ≠ 1024 := by omega
                                          have hzff : zf = false := by simpa using hzf
                                          have hmask : biteAddrMaskWord = solcAddrMask := by native_decide
                                          have hposNe : ∀ w : UInt256, w ≠ ⟨0⟩ → 0 < w.toNat :=
                                            fun w hw => Nat.pos_of_ne_zero (fun h => hw (uint256_toNat_eq_zero h))
                                          have codePos : ∀ (e : EVM.State) (w : UInt256),
                                              uniswapExtCodeSizeWord e.accountMap w ≠ ⟨0⟩ →
                                              0 < (UInt256.ofNat ((e.lookupAccount
                                                (AccountAddress.ofUInt256 w)).option 0
                                                (fun acc => acc.code.size))).toNat := by
                                            intro e w hw
                                            unfold uniswapExtCodeSizeWord at hw
                                            simp only [State.lookupAccount]
                                            cases hf : e.accountMap.find? (AccountAddress.ofUInt256 w) with
                                            | none => rw [hf] at hw; simp [Option.option] at hw
                                            | some acc =>
                                                rw [hf] at hw
                                                simp only [Option.option, Function.comp] at hw ⊢
                                                exact hposNe _ hw
                                          have addrId : ∀ a : AccountAddress, EVM.address a.val = a := by
                                            intro a; apply Fin.ext
                                            show a.val % EVM.addressModulus = a.val
                                            rw [show EVM.addressModulus = AccountAddress.size from by decide]
                                            exact Nat.mod_eq_of_lt a.isLt
                                          have hAddrRT : ∀ a : AccountAddress,
                                              AccountAddress.ofNat (UInt256.ofNat a.val).toNat = a := by
                                            intro a
                                            have h1 : (UInt256.ofNat a.val).toNat = a.val :=
                                              UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le a.isLt
                                                (show AccountAddress.size ≤ UInt256.size from by decide))
                                            rw [h1]; apply Fin.ext
                                            simp only [AccountAddress.ofNat, Fin.ofNat]
                                            exact Nat.mod_eq_of_lt a.isLt
                                          have hbytes : biteIlkBytes I = EVM.Word.toBytesBE (biteIlkWord I) := by
                                            have hlen32 : (biteIlkBytes I).length = 32 := by
                                              simp only [biteIlkBytes, List.length_take, List.length_drop]
                                              have htlen : I.calldata.toList.length = I.calldata.size := by
                                                rw [byteArray_toList_eq, Array.length_toList]; rfl
                                              rw [htlen]; omega
                                            have hword : ABI.bytesToWord (biteIlkBytes I) = biteIlkWord I := by
                                              simpa [biteIlkBytes, biteIlkWord] using
                                                (decode_word_at_eq_any I.calldata 4 (by simpa using hsz36))
                                            have hto := toBytesBE_bytesToWord_of_length (bs := biteIlkBytes I) hlen32
                                            rw [hword] at hto; exact hto.symm
                                          have uminEq : ∀ a b : UInt256,
                                              (if UInt256.gt a b = ⟨0⟩ then a else b) = umin a b := by
                                            intro a b; unfold umin
                                            by_cases h : a.toNat ≤ b.toNat
                                            · rw [if_pos (ugt_zero h), if_pos h]
                                            · rw [if_neg (by rw [ugt_one (by omega)]; decide), if_neg h]
                                          have hwad : wadU = ⟨1000000000000000000⟩ := by native_decide
                                          have hsl : (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat =
                                              57896044618658097711785492504343953926634992332820282019728792003956564819968 := by
                                            native_decide
                                          have hbr : ∀ (o : ByteArray) (k : ℕ), k + 32 ≤ o.size →
                                              ABI.bytesToWord ((o.toList.drop k).take 32) =
                                                UInt256.ofNat (fromByteArrayBigEndian (o.extract k (k + 32))) := by
                                            intro o k h
                                            rw [decode_word_at_eq_any o k h, uInt256OfByteArray_eq]
                                            congr 1; unfold fromByteArrayBigEndian; congr 1
                                            rw [byteArray_toList_eq (o.readBytes k 32),
                                              readBytes_at_toList_any o k h,
                                              byteArray_toList_eq (o.extract k (k + 32)),
                                              ByteArray.data_extract, Array.toList_extract,
                                              List.extract_eq_take_drop]
                                            simp
                                          obtain ⟨σs, As, σus, Aus, hIlksSolm, hUrnsSolm, hAmEq, hvatCodeIlkS⟩ :=
                                            catBiteMapUrns hAccounts hdepthNe hUrnsVatCode hIlksCall hUrnsCall
                                          have slotEqUS : ∀ s : UInt256, solcSlotWord σus I s = solcSlotWord σu I s := by
                                            intro s; simp only [solcSlotWord]
                                            rw [accountMapEquiv_storage_findD hAmEq I.codeOwner s ⟨0⟩]
                                          set eUrnE := { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                                            accountMap := σu, substate := Au, createdAccounts := cAu } with heUrnEdef
                                          set eUrnS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                                            accountMap := σus, substate := Aus, createdAccounts := cAu } with heUrnSdef
                                          have hEqU : EVMStateEquiv eUrnE eUrnS := ⟨rfl, rfl, hAmEq⟩
                                          have heUEam : eUrnE.accountMap = σu := rfl
                                          have heUEee : eUrnE.executionEnv = I := rfl
                                          have heUSam : eUrnS.accountMap = σus := rfl
                                          have heUSee : eUrnS.executionEnv = I := rfl
                                          have hboxB : biteBoxW eUrnE = solcSlotWord σu I ⟨5⟩ := by
                                            simp only [biteBoxW, catSlotWord, heUEam, heUEee]
                                          have hlitB : biteLitW eUrnE = solcSlotWord σu I ⟨6⟩ := by
                                            simp only [biteLitW, catSlotWord, heUEam, heUEee]
                                          have hchopB : biteChopW I eUrnE = milkChop := by
                                            rw [hmilkChopDef]
                                            simp only [biteChopW, catSlotWord, heUEam, heUEee, biteChopSlot,
                                              biteFlipSlot_eq hsz36]
                                          have hdunkB : biteDunkW I eUrnE = milkDunk := by
                                            rw [hmilkDunkDef]
                                            simp only [biteDunkW, catSlotWord, heUEam, heUEee, biteDunkSlot,
                                              biteFlipSlot_eq hsz36]
                                          have hroomB : biteRoomV eUrnE = room := by
                                            rw [hroomDef]
                                            simp only [biteRoomV, biteBoxW, biteLitW, catSlotWord, heUEam, heUEee]
                                          have hdunkroomB : biteDunkRoomV I eUrnE = dunkRoom := by
                                            rw [hdunkRoomDef, uminEq milkDunk room]
                                            simp only [biteDunkRoomV, hdunkB, hroomB]
                                          have hdartvB : biteDartV I eUrnE iRate art = dart := by
                                            have hcand : biteDartCandV I eUrnE iRate = dartCandidate := by
                                              simp only [biteDartCandV, biteDartDenomV, biteDunkRoomWadV,
                                                hchopB, hdunkroomB, hwad, hdartCandDef, hdartDenomDef,
                                                hdunkRoomWadDef]
                                              rfl
                                            rw [hdartDef, uminEq art dartCandidate]
                                            simp only [biteDartV, hcand]
                                          have hdinkvB : biteDinkV I eUrnE iRate art ink = dink := by
                                            have hcand : biteDinkCandV I eUrnE iRate art ink = dinkCandidate := by
                                              simp only [biteDinkCandV, biteInkDartV, hdartvB, hdinkCandDef,
                                                hinkDartDef]
                                              rfl
                                            rw [hdinkDef, uminEq ink dinkCandidate]
                                            simp only [biteDinkV, hcand]
                                          have hIlksDec : config.externalABI.decode? "ilks" o' =
                                              some [bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 0 32))),
                                                bw iRate, bw iSpot,
                                                bw (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 96 128))),
                                                bw iDust] := by
                                            have h := catBiteIlksDecode_ok hilkslen
                                            rw [hbr o' 0 (by omega), hbr o' 32 (by omega), hbr o' 64 (by omega),
                                              hbr o' 96 (by omega), hbr o' 128 (by omega)] at h
                                            exact h
                                          have hUrnsDec : config.externalABI.decode? "urns" ou =
                                              some [bw ink, bw art] := by
                                            have h := catBiteUrnsDecode_ok hurnslen
                                            rw [hbr ou 0 (by omega), hbr ou 32 (by omega)] at h
                                            exact h
                                          -- map the (successful) grab CALL, keeping the coupling.
                                          obtain ⟨AG, hGrabCall'⟩ :=
                                            biteTypedCallZeroSetSubstate hGrabCall
                                              (by simpa [initState] using hdepthNe) Au
                                          obtain ⟨σgs, Ags, hGrabSolm, hEqGrab⟩ :=
                                            catBiteMapCall hEqU hGrabCall' hdepthNe
                                          set eGrabE := { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                                            accountMap := σg, substate := AG, createdAccounts := cAg } with heGrabEdef
                                          set eGrabS := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                                            accountMap := σgs, substate := Ags, createdAccounts := cAg } with heGrabSdef
                                          have heGEam : eGrabE.accountMap = σg := rfl
                                          have heGEee : eGrabE.executionEnv = I := rfl
                                          have htgtU : EVM.address (biteVatAddr eUrnS).val =
                                              AccountAddress.ofUInt256 ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord) := by
                                            rw [← biteVatAddr_eq_of_equiv hEqU, addrId,
                                              accountAddress_ofUInt256_eq_ofNat_toNat, hmask]
                                            simp only [biteVatAddr, catSlotWord, heUEam, heUEee]
                                          have h1 : biteIlkVal I =
                                              Value.fixedBytes bytes32Width (EVM.Word.toBytesBE (biteIlkWord I)) := by
                                            simp only [biteIlkVal, hbytes]
                                          have h2 : biteUrnVal I = Value.address (AccountAddress.ofNat
                                              (biteAddrMaskWord.land
                                                (biteAddrMaskWord.land (calldataWord I.calldata 36))).toNat) := by
                                            rw [hurn]
                                            simp only [biteUrnVal, biteUrnWord, biteUrnAddr, hAddrRT]
                                          have h3 : (eUrnS.executionEnv.codeOwner : AccountAddress) =
                                              AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat := by
                                            rw [heUSee]; exact (hAddrRT I.codeOwner).symm
                                          have h4 : biteVowAddrV eUrnS = AccountAddress.ofNat
                                              (biteAddrMaskWord.land (solcSlotWord σu I ⟨4⟩)).toNat := by
                                            rw [← biteVowAddrV_eq_of_equiv hEqU]
                                            simp only [biteVowAddrV, catSlotWord, heUEam, heUEee, hmask]
                                            rw [u256_land_comm]
                                          have hdartvBS : biteDartV I eUrnS iRate art = dart := by
                                            rw [← biteDartV_eq_of_equiv hEqU]; exact hdartvB
                                          have hdinkvBS : biteDinkV I eUrnS iRate art ink = dink := by
                                            rw [← biteDinkV_eq_of_equiv hEqU]; exact hdinkvB
                                          have hdartrateBS : biteDartRateV I eUrnS iRate art = dart.mul iRate := by
                                            rw [← biteDartRateV_eq_of_equiv hEqU]
                                            simp only [biteDartRateV, hdartvB]; rfl
                                          have hGrabCodeS :
                                              ¬ Reasoning.Theory.uniswapExtCodeSizeWord σus
                                                ((solcSlotWord σus I ⟨3⟩).land biteAddrMaskWord) = ⟨0⟩ := by
                                            rw [slotEqUS ⟨3⟩, ← uniswapExtCodeSizeWord_accountMapEquiv hAmEq]
                                            exact hGrabCode
                                          rw [hperm, ← htgtU, ← h1, ← h2, ← h3, ← h4, ← hdinkvBS, ← hdartvBS]
                                            at hGrabSolm
                                          have hGrabDec : config.externalABI.decode? "grab" og = some [] := by
                                            simp [config, externalABI, decodeVoid?]
                                          -- map the (failed) fess CALL from the grab-output coupling.
                                          obtain ⟨AF, hFessCall'⟩ :=
                                            biteTypedCallZeroSetSubstate hFessCall
                                              (by simpa [initState] using hdepthNe) AG
                                          obtain ⟨σfs, Afs, hFessSolm, _hEqFess⟩ :=
                                            catBiteMapCall hEqGrab hFessCall' hdepthNe
                                          have htgtF : EVM.address (biteVowAddrV eGrabS).val =
                                              AccountAddress.ofUInt256 (biteAddrMaskWord.land (solcSlotWord σg I ⟨4⟩)) := by
                                            rw [← biteVowAddrV_eq_of_equiv hEqGrab, addrId,
                                              accountAddress_ofUInt256_eq_ofNat_toNat, hmask, u256_land_comm]
                                            simp only [biteVowAddrV, catSlotWord, heGEam, heGEee]
                                          have hfessArg : bw (biteDartRateV I eUrnS iRate art) =
                                              Value.int (Int.ofNat (dart.mul iRate).toNat) := by rw [hdartrateBS]
                                          rw [hzff, hperm, ← htgtF, ← hfessArg] at hFessSolm
                                          have hvowCodeS : 0 < (UInt256.ofNat
                                              ((eGrabS.lookupAccount (biteVowAddrV eGrabS)).option 0
                                                (fun acc => acc.code.size))).toNat := by
                                            rw [← biteVowAddrV_eq_of_equiv hEqGrab,
                                              ← biteCodeW_eq_of_equiv (biteVowAddrV eGrabE) hEqGrab]
                                            have haddr : biteVowAddrV eGrabE =
                                                AccountAddress.ofUInt256 ((solcSlotWord σg I ⟨4⟩).land solcAddrMask) := by
                                              rw [accountAddress_ofUInt256_eq_ofNat_toNat]
                                              simp only [biteVowAddrV, catSlotWord, heGEam, heGEee]
                                            rw [haddr]
                                            refine codePos eGrabE ((solcSlotWord σg I ⟨4⟩).land solcAddrMask) ?_
                                            rw [heGEam, u256_land_comm, ← hmask]; exact hFessCode
                                          have hlive' : catSlotWord ⟨2⟩ eUrnS.accountMap eUrnS.executionEnv = ⟨1⟩ := by
                                            rw [← biteSlotEqOfEquiv hEqU ⟨2⟩]; exact hlive
                                          refine catBiteFessFailLeaf hcode hdispatch hdecode (by
                                            simpa [hzff] using rd2300) hoszf (by
                                            simp only [List.length_cons, List.length_nil]; omega) ?_
                                          refine catBiteSourceFessFailRevert hwv
                                            (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm hIlksDec
                                            hvatCodeIlkS hUrnsSolm hUrnsDec hlive' hsz36 hfitInkSpot hfitArtRate
                                            hspotPos (hposNe iRate hRatePos) hunsafe ?_ ?_ ?_ ?_ ?_
                                            (hposNe art hArtPos) ?_ ?_ ?_ ?_ ?_ hGrabSolm hGrabDec ?_ hvowCodeS
                                            hFessSolm
                                          · rw [← biteLitW_eq_of_equiv hEqU, ← biteBoxW_eq_of_equiv hEqU, hlitB, hboxB]
                                            exact hlitterbox
                                          · rw [← biteRoomV_eq_of_equiv hEqU, hroomB]; exact hroomdust
                                          · rw [← biteDunkRoomV_eq_of_equiv hEqU, hdunkroomB, hwad, Nat.mul_comm]
                                            exact hFitWad
                                          · rw [← biteChopW_eq_of_equiv hEqU, hchopB]; exact hposNe milkChop hChopPos
                                          · rw [← biteDartV_eq_of_equiv hEqU, hdartvB, Nat.mul_comm]; exact hFitInkDart
                                          · rw [← biteDartV_eq_of_equiv hEqU, hdartvB]; exact hDartPos
                                          · rw [← biteDinkV_eq_of_equiv hEqU, hdinkvB]; exact hDinkPos
                                          · rw [← biteDartV_eq_of_equiv hEqU, hdartvB]; simp only [int256Limit]
                                            exact Int.ofNat_le.mpr (hDartLim.trans_eq hsl)
                                          · rw [← biteDinkV_eq_of_equiv hEqU, hdinkvB]; simp only [int256Limit]
                                            exact Int.ofNat_le.mpr (hDinkLim.trans_eq hsl)
                                          · have haddr : biteVatAddr eUrnS =
                                                AccountAddress.ofUInt256 (catBiteVatTargetWord σus I) := by
                                              rw [accountAddress_ofUInt256_eq_ofNat_toNat]
                                              simp only [biteVatAddr, catBiteVatTargetWord, catAddressReturnWord,
                                                catSlotWord, heUSam, heUSee]
                                            rw [haddr]
                                            refine codePos eUrnS (catBiteVatTargetWord σus I) ?_
                                            rw [heUSam, show catBiteVatTargetWord σus I =
                                                  (solcSlotWord σus I ⟨3⟩).land biteAddrMaskWord from by
                                                simp only [catBiteVatTargetWord, catAddressReturnWord, catSlotWord,
                                                  hmask]]
                                            exact hGrabCodeS
                                          · -- hfitDartRate
                                            rw [← biteDartV_eq_of_equiv hEqU, hdartvB, Nat.mul_comm]; exact hRateFit
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
                                          have hdepthNe : I.depth ≠ 1024 := by omega
                                          obtain ⟨AU, hUrnsCall'⟩ :=
                                            biteTypedCallZeroSetSubstate hUrnsCall
                                              (by simpa [initState] using hdepthNe) A'
                                          obtain ⟨AG, hGrabCall'⟩ :=
                                            biteTypedCallZeroSetSubstate hGrabCall
                                              (by simpa [initState] using hdepthNe) AU
                                          obtain ⟨AF, hFessCall'⟩ :=
                                            biteTypedCallZeroSetSubstate hFessCall
                                              (by simpa [initState] using hdepthNe) AG
                                          obtain ⟨AK, hKickCall'⟩ :=
                                            biteTypedCallZeroSetSubstate hKickCall
                                              (by simpa [initState] using hdepthNe) AF
                                          set S := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
                                            with hS
                                          have hbr : ∀ (o : ByteArray) (k : ℕ), k + 32 ≤ o.size →
                                              ABI.bytesToWord ((o.toList.drop k).take 32) =
                                                UInt256.ofNat (fromByteArrayBigEndian
                                                  (o.extract k (k + 32))) := by
                                            intro o k h
                                            rw [decode_word_at_eq_any o k h, uInt256OfByteArray_eq]
                                            congr 1; unfold fromByteArrayBigEndian; congr 1
                                            rw [byteArray_toList_eq (o.readBytes k 32),
                                              readBytes_at_toList_any o k h,
                                              byteArray_toList_eq (o.extract k (k + 32)),
                                              ByteArray.data_extract, Array.toList_extract,
                                              List.extract_eq_take_drop]
                                            simp
                                          have hmask : biteAddrMaskWord = solcAddrMask := by
                                            native_decide
                                          have uminEq : ∀ a b : UInt256,
                                              (if UInt256.gt a b = ⟨0⟩ then a else b) = umin a b := by
                                            intro a b
                                            unfold umin
                                            by_cases h : a.toNat ≤ b.toNat
                                            · rw [if_pos (ugt_zero h), if_pos h]
                                            · rw [if_neg (by rw [ugt_one (by omega)]; decide), if_neg h]
                                          have hposNe : ∀ w : UInt256, w ≠ ⟨0⟩ → 0 < w.toNat :=
                                            fun w hw => Nat.pos_of_ne_zero
                                              (fun h => hw (uint256_toNat_eq_zero h))
                                          have hwad : wadU = ⟨1000000000000000000⟩ := by native_decide
                                          have hsl : (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat = 57896044618658097711785492504343953926634992332820282019728792003956564819968 := by native_decide
                                          set eIlk := { S with accountMap := σ', substate := A', createdAccounts := cA' } with heIlk
                                          set eUrn := { S with accountMap := σu, substate := AU, createdAccounts := cAu } with heUrn
                                          set eGrab := { S with accountMap := σg, substate := AG, createdAccounts := cAg } with heGrab
                                          set eFess := { S with accountMap := σf, substate := AF, createdAccounts := cAf } with heFess
                                          set eKick := { S with accountMap := σk, substate := AK, createdAccounts := cAk } with heKick
                                          have heUam : eUrn.accountMap = σu := rfl
                                          have heUee : eUrn.executionEnv = I := rfl
                                          have heFam : eFess.accountMap = σf := rfl
                                          have heFee : eFess.executionEnv = I := rfl
                                          have hboxB : biteBoxW eUrn = solcSlotWord σu I ⟨5⟩ := by
                                            simp only [biteBoxW, catSlotWord, heUam, heUee]
                                          have hlitB : biteLitW eUrn = solcSlotWord σu I ⟨6⟩ := by
                                            simp only [biteLitW, catSlotWord, heUam, heUee]
                                          have hchopB : biteChopW I eUrn = milkChop := by
                                            rw [hmilkChopDef]
                                            simp only [biteChopW, catSlotWord, heUam, heUee,
                                              biteChopSlot, biteFlipSlot_eq hsz36]
                                          have hdunkB : biteDunkW I eUrn = milkDunk := by
                                            rw [hmilkDunkDef]
                                            simp only [biteDunkW, catSlotWord, heUam, heUee,
                                              biteDunkSlot, biteFlipSlot_eq hsz36]
                                          have hroomB : biteRoomV eUrn = room := by
                                            rw [hroomDef]
                                            simp only [biteRoomV, biteBoxW, biteLitW, catSlotWord,
                                              heUam, heUee]
                                          have hdunkroomB : biteDunkRoomV I eUrn = dunkRoom := by
                                            rw [hdunkRoomDef, uminEq milkDunk room]
                                            simp only [biteDunkRoomV, hdunkB, hroomB]
                                          have hdartvB : biteDartV I eUrn iRate art = dart := by
                                            have hcand : biteDartCandV I eUrn iRate = dartCandidate := by
                                              simp only [biteDartCandV, biteDartDenomV,
                                                biteDunkRoomWadV, hchopB, hdunkroomB, hwad,
                                                hdartCandDef, hdartDenomDef, hdunkRoomWadDef]
                                              rfl
                                            rw [hdartDef, uminEq art dartCandidate]
                                            simp only [biteDartV, hcand]
                                          have hdinkvB : biteDinkV I eUrn iRate art ink = dink := by
                                            have hcand :
                                                biteDinkCandV I eUrn iRate art ink = dinkCandidate := by
                                              simp only [biteDinkCandV, biteInkDartV, hdartvB,
                                                hdinkCandDef, hinkDartDef]
                                              rfl
                                            rw [hdinkDef, uminEq ink dinkCandidate]
                                            simp only [biteDinkV, hcand]
                                          have hdartrateB : biteDartRateV I eUrn iRate art = dartRate := by
                                            rw [hdartRateDef]
                                            simp only [biteDartRateV, hdartvB]; rfl
                                          have htabB : biteTabV I eUrn iRate art = tab := by
                                            rw [htabDef, htabBaseDef]
                                            simp only [biteTabV, biteTabBaseV, hdartrateB, hchopB, hwad]
                                            rfl
                                          have hlitFB : biteLitW eFess = solcSlotWord σf I ⟨6⟩ := by
                                            simp only [biteLitW, catSlotWord, heFam, heFee]
                                          have heIam : eIlk.accountMap = σ' := rfl
                                          have heIee : eIlk.executionEnv = I := rfl
                                          have heGam : eGrab.accountMap = σg := rfl
                                          have heGee : eGrab.executionEnv = I := rfl
                                          have addrId : ∀ a : AccountAddress, EVM.address a.val = a := by
                                            intro a; apply Fin.ext
                                            show a.val % EVM.addressModulus = a.val
                                            rw [show EVM.addressModulus = AccountAddress.size from by decide]
                                            exact Nat.mod_eq_of_lt a.isLt
                                          have codePos : ∀ (e : EVM.State) (w : UInt256),
                                              uniswapExtCodeSizeWord e.accountMap w ≠ ⟨0⟩ →
                                              0 < (UInt256.ofNat ((e.lookupAccount
                                                (AccountAddress.ofUInt256 w)).option 0
                                                (fun acc => acc.code.size))).toNat := by
                                            intro e w hw
                                            unfold uniswapExtCodeSizeWord at hw
                                            simp only [State.lookupAccount]
                                            cases hf : e.accountMap.find? (AccountAddress.ofUInt256 w) with
                                            | none => rw [hf] at hw; simp [Option.option] at hw
                                            | some acc =>
                                                rw [hf] at hw
                                                simp only [Option.option, Function.comp] at hw ⊢
                                                exact hposNe _ hw
                                          have hbytes :
                                              biteIlkBytes I = EVM.Word.toBytesBE (biteIlkWord I) := by
                                            have hlen32 : (biteIlkBytes I).length = 32 := by
                                              simp only [biteIlkBytes, List.length_take, List.length_drop]
                                              have htlen : I.calldata.toList.length = I.calldata.size := by
                                                rw [byteArray_toList_eq, Array.length_toList]; rfl
                                              rw [htlen]; omega
                                            have hword : ABI.bytesToWord (biteIlkBytes I) = biteIlkWord I := by
                                              simpa [biteIlkBytes, biteIlkWord] using
                                                (decode_word_at_eq_any I.calldata 4 (by simpa using hsz36))
                                            have hto := toBytesBE_bytesToWord_of_length
                                              (bs := biteIlkBytes I) hlen32
                                            rw [hword] at hto; exact hto.symm
                                          have hAddrRT : ∀ a : AccountAddress,
                                              AccountAddress.ofNat (UInt256.ofNat a.val).toNat = a := by
                                            intro a
                                            have h1 : (UInt256.ofNat a.val).toNat = a.val :=
                                              UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le a.isLt
                                                (show AccountAddress.size ≤ UInt256.size from by decide))
                                            rw [h1]; apply Fin.ext
                                            simp only [AccountAddress.ofNat, Fin.ofNat]
                                            exact Nat.mod_eq_of_lt a.isLt
                                          have hlitternew :
                                              biteLitterNewV I eUrn eFess iRate art = litterNew := by
                                            rw [hlitterNewDef]
                                            simp only [biteLitterNewV, hlitFB, htabB]
                                          have hflipAddr : biteFlipAddrV I eUrn =
                                              AccountAddress.ofUInt256 (biteAddrMaskWord.land flipW) := by
                                            rw [accountAddress_ofUInt256_eq_ofNat_toNat, hflipWDef, hmask]
                                            simp only [biteFlipAddrV, catSlotWord, heUam, heUee,
                                              biteFlipSlot_eq hsz36]
                                            rw [solcAddrMask_clean_left
                                              (by rw [u256_land_comm]; exact solcAddrMask_result_canonical _),
                                              u256_land_comm]
                                          refine catBiteSuccessBranch
                                            (evmIlk := eIlk) (evmUrn := eUrn) (evmGrab := eGrab)
                                            (evmFess := eFess) (evmKick := eKick)
                                            (ilksOut := o') (urnsOut := ou) (grabOut := og)
                                            (fessOut := ofb) (kickOut := ok)
                                            (iRate := iRate) (iSpot := iSpot) (iDust := iDust)
                                            (ink := ink) (art := art)
                                            (id := UInt256.ofNat (fromByteArrayBigEndian (ok.extract 0 32)))
                                            (iArt := UInt256.ofNat (fromByteArrayBigEndian (o'.extract 0 32)))
                                            (iLine := UInt256.ofNat (fromByteArrayBigEndian (o'.extract 96 128)))
                                            (acc := (cAk, σk))
                                            (hcode := hcode) (hdispatch := hdispatch) (hdecode := hdecode)
                                            (hAccounts := hAccounts) (hsz36 := hsz36) (hwv := hwv)
                                            (hret := hret) (hcreated := rfl)
                                            (hAccountsFinal := accountMapEquiv_refl σk)
                                            (hLitStore := storageLocStore_uint256 _ ⟨6⟩ _)
                                            (hIlksDec := by
                                              have h := catBiteIlksDecode_ok hilkslen
                                              rw [hbr o' 0 (by omega), hbr o' 32 (by omega),
                                                hbr o' 64 (by omega), hbr o' 96 (by omega),
                                                hbr o' 128 (by omega)] at h
                                              exact h)
                                            (hUrnsDec := by
                                              have h := catBiteUrnsDecode_ok hurnslen
                                              rw [hbr ou 0 (by omega), hbr ou 32 (by omega)] at h
                                              exact h)
                                            (hKickDec := catBiteKickDecode_ok hk32)
                                            (hGrabDec := by simp [config, externalABI, decodeVoid?])
                                            (hFessDec := by simp [config, externalABI, decodeVoid?])
                                            (hfitInkSpot := hfitInkSpot) (hfitArtRate := hfitArtRate)
                                            (hspotPos := hspotPos) (hunsafe := hunsafe)
                                            (hratePos := hposNe iRate hRatePos)
                                            (hartPos := hposNe art hArtPos)
                                            (hlive := by rw [heUam, heUee]; exact hlive)
                                            (hfitDunkRoomWad := by
                                              rw [hdunkroomB, hwad, Nat.mul_comm]; exact hFitWad)
                                            (hfitInkDart := by
                                              rw [hdartvB, Nat.mul_comm]; exact hFitInkDart)
                                            (hfitDartRate := by
                                              rw [hdartvB, Nat.mul_comm]; exact hRateFit)
                                            (hfitTabBase := by
                                              rw [hdartrateB, hchopB, Nat.mul_comm]; exact hChopFit)
                                            (hfitLitterNew := by rw [hlitFB, htabB]; exact hLitFit)
                                            (hmilkChopPos := by rw [hchopB]; exact hposNe milkChop hChopPos)
                                            (hlitLtBox := by rw [hlitB, hboxB]; exact hlitterbox)
                                            (hroomGeDust := by rw [hroomB]; exact hroomdust)
                                            (hdartPos := by rw [hdartvB]; exact hDartPos)
                                            (hdinkPos := by rw [hdinkvB]; exact hDinkPos)
                                            (hdartLim := by
                                              rw [hdartvB]; simp only [int256Limit]
                                              exact Int.ofNat_le.mpr (hDartLim.trans_eq hsl))
                                            (hdinkLim := by
                                              rw [hdinkvB]; simp only [int256Limit]
                                              exact Int.ofNat_le.mpr (hDinkLim.trans_eq hsl))
                                            (hvatCode0 :=
                                              catBiteVatCodePos_of_uniswap (accountMapEquiv_refl σ_evm) hvatCode)
                                            (hIlksCall := by
                                              rw [catBiteVatEvmAddr_eq_target]; exact hIlksCall)
                                            (hvatCodeIlk := by
                                              have haddr : biteVatAddr eIlk =
                                                  AccountAddress.ofUInt256 (catBiteVatTargetWord σ' I) := by
                                                rw [accountAddress_ofUInt256_eq_ofNat_toNat]
                                                simp only [biteVatAddr, catBiteVatTargetWord,
                                                  catAddressReturnWord, catSlotWord, heIam, heIee]
                                              rw [haddr]
                                              refine codePos eIlk (catBiteVatTargetWord σ' I) ?_
                                              have ht : catBiteVatTargetWord σ' I =
                                                  (catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord := by
                                                simp only [catBiteVatTargetWord, catAddressReturnWord, hmask]
                                              rw [heIam, ht]; exact hUrnsVatCode)
                                            (hUrnsCall := by
                                              have haddr : EVM.address (biteVatAddr eIlk).val =
                                                  AccountAddress.ofUInt256
                                                    ((catSlotWord ⟨3⟩ σ' I).land biteAddrMaskWord) := by
                                                rw [addrId, accountAddress_ofUInt256_eq_ofNat_toNat]
                                                simp only [biteVatAddr, catSlotWord, heIam, heIee, hmask]
                                              rw [haddr]; exact hUrnsCall')
                                            (hvatCodeMid := by
                                              have haddr : biteVatAddr eUrn =
                                                  AccountAddress.ofUInt256 (catBiteVatTargetWord σu I) := by
                                                rw [accountAddress_ofUInt256_eq_ofNat_toNat]
                                                simp only [biteVatAddr, catBiteVatTargetWord,
                                                  catAddressReturnWord, catSlotWord, heUam, heUee]
                                              rw [haddr]
                                              refine codePos eUrn (catBiteVatTargetWord σu I) ?_
                                              have ht : catBiteVatTargetWord σu I =
                                                  (solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord := by
                                                simp only [catBiteVatTargetWord, catAddressReturnWord,
                                                  catSlotWord, hmask]
                                              rw [heUam, ht]; exact hGrabCode)
                                            (hGrabCall := by
                                              rw [hperm] at hGrabCall'
                                              have ht : EVM.address (biteVatAddr eUrn).val =
                                                  AccountAddress.ofUInt256
                                                    ((solcSlotWord σu I ⟨3⟩).land biteAddrMaskWord) := by
                                                rw [addrId, accountAddress_ofUInt256_eq_ofNat_toNat, hmask]
                                                simp only [biteVatAddr, catSlotWord, heUam, heUee]
                                              have h1 : biteIlkVal I =
                                                  Value.fixedBytes bytes32Width
                                                    (EVM.Word.toBytesBE (biteIlkWord I)) := by
                                                simp only [biteIlkVal, hbytes]
                                              have h2 : biteUrnVal I = Value.address (AccountAddress.ofNat
                                                  (biteAddrMaskWord.land
                                                    (biteAddrMaskWord.land (calldataWord I.calldata 36))).toNat) := by
                                                rw [hurn]
                                                simp only [biteUrnVal, biteUrnWord, biteUrnAddr, hAddrRT]
                                              have h3 : (eUrn.executionEnv.codeOwner : AccountAddress) =
                                                  AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat := by
                                                rw [heUee]; exact (hAddrRT I.codeOwner).symm
                                              have h4 : biteVowAddrV eUrn = AccountAddress.ofNat
                                                  (biteAddrMaskWord.land (solcSlotWord σu I ⟨4⟩)).toNat := by
                                                simp only [biteVowAddrV, catSlotWord, heUam, heUee, hmask]
                                                rw [u256_land_comm]
                                              rw [ht, h1, h2, h3, h4, hdinkvB, hdartvB]
                                              exact hGrabCall')
                                            (hvowCode := by
                                              have haddr : biteVowAddrV eGrab =
                                                  AccountAddress.ofUInt256
                                                    ((solcSlotWord σg I ⟨4⟩).land solcAddrMask) := by
                                                rw [accountAddress_ofUInt256_eq_ofNat_toNat]
                                                simp only [biteVowAddrV, catSlotWord, heGam, heGee]
                                              rw [haddr]
                                              refine codePos eGrab ((solcSlotWord σg I ⟨4⟩).land solcAddrMask) ?_
                                              rw [heGam, u256_land_comm, ← hmask]; exact hFessCode)
                                            (hFessCall := by
                                              have haddr : EVM.address (biteVowAddrV eGrab).val =
                                                  AccountAddress.ofUInt256
                                                    (biteAddrMaskWord.land (solcSlotWord σg I ⟨4⟩)) := by
                                                rw [addrId, accountAddress_ofUInt256_eq_ofNat_toNat,
                                                  hmask, u256_land_comm]
                                                simp only [biteVowAddrV, catSlotWord, heGam, heGee]
                                              rw [hperm] at hFessCall'
                                              rw [haddr, show bw (biteDartRateV I eUrn iRate art) =
                                                Value.int (Int.ofNat dartRate.toNat) from by rw [hdartrateB]]
                                              exact hFessCall')
                                            (hflipCode := by
                                              rw [hflipAddr]
                                              refine codePos _ (biteAddrMaskWord.land flipW) ?_
                                              simp only [storageStore_accountMap, heFam, heFee]
                                              rw [hlitternew]; exact hKickCode)
                                            (hKickCall := by
                                              rw [hzk, hperm] at hKickCall'
                                              have storeFlat : ∀ (ev : EVM.State) (aa : AccountAddress)
                                                  (k v : UInt256), Solm.EVM.storageStore ev aa k v =
                                                    { ev with accountMap := sstoreAccountMap aa ev.accountMap k v } := by
                                                intro ev aa k v
                                                simp only [Solm.EVM.storageStore, sstoreAccountMap, State.lookupAccount]
                                                cases h : ev.accountMap.find? aa with
                                                | none => simp [Option.option]
                                                | some acc => simp [Option.option, State.setAccount, Account.updateStorage]
                                              have hdiv1 : ∀ y : UInt256, UInt256.div y ⟨1⟩ = y := fun y => by
                                                apply u256_inj
                                                rw [udiv_toNat, show (⟨1⟩ : UInt256).toNat = 1 from by native_decide,
                                                  Nat.div_one]
                                              have hexp : UInt256.exp (⟨256⟩ : UInt256) ⟨0⟩ = ⟨1⟩ := by native_decide
                                              have hvowW : ∀ σx : AccountMap,
                                                  UInt256.land (solcSlotWord σx I ⟨4⟩) solcAddrMask = seg8VowM σx I := by
                                                intro σx
                                                simp only [seg8VowM, hmask, hexp, hdiv1]
                                                rw [solcAddrMask_clean_left
                                                  (by rw [u256_land_comm]; exact solcAddrMask_result_canonical _),
                                                  u256_land_comm]
                                              have hvowArg :
                                                  biteVowAddrV (Solm.EVM.storageStore eFess eFess.executionEnv.codeOwner
                                                      ⟨6⟩ litterNew)
                                                    = AccountAddress.ofNat
                                                      (seg8VowM (sstoreAccountMap I.codeOwner σf ⟨6⟩ litterNew) I).toNat := by
                                                simp only [biteVowAddrV, storageStore_accountMap,
                                                  storageStore_executionEnv, heFam, heFee, catSlotWord]
                                                rw [hvowW]
                                              have h2 : biteUrnVal I = Value.address (AccountAddress.ofNat
                                                  (biteAddrMaskWord.land
                                                    (biteAddrMaskWord.land (calldataWord I.calldata 36))).toNat) := by
                                                rw [hurn]
                                                simp only [biteUrnVal, biteUrnWord, biteUrnAddr, hAddrRT]
                                              rw [hlitternew, hvowArg, storeFlat, addrId, hflipAddr, h2, htabB, hdinkvB]
                                              exact hKickCall')
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
