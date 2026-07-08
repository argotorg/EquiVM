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
                                -- frontier: Seg6Aw (1620 → 1708) onward.
                                sorry
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
