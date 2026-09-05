import Benchmarks.Dss.Clipper.TakeCallbackCall
import Benchmarks.Dss.Clipper.TakeDynamicMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/- The arithmetic branches all join at PC 4223.  From there through the optional
   callback the bytecode is identical, so keep that control-flow split in one place. -/
set_option maxHeartbeats 4000000 in
theorem RD.clipperTakeFluxCallbackElim
    {P : Prop} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA0 cA gh bl σ₀ σStart σ I} {g : Sat256} {A : Substate}
    {price slice owe tab lot tic packed stopped dataLen dataStart who max amt id :
      UInt256}
    {R : List UInt256} {baseMem rdata : ByteArray} {k C : ℕ}
    (rd4223 : RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4223⟩
      (slice :: owe :: tab :: lot :: price :: tic :: packed ::
        stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
      baseMem (UInt256.ofNat 7) rdata (cA, σ) k C)
    (hbaseSize : baseMem.size = 196)
    (hbaseRead64 : baseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hdataLen : dataLen ≠ ⟨0⟩)
    (hdataLenEq : dataLen = clipperTakeDataLenWord I)
    (hdataStartEq : dataStart.toNat =
      32 + (4 + (clipperTakeDataOffsetWord I).toNat))
    (hlenMax : dataLen.toNat ≤ 4294967296)
    (hpayload :
      (((I.calldata.toList.drop 4).drop
        ((clipperTakeDataOffsetWord I).toNat + 32)).take
        (clipperTakeDataLenWord I).toNat).length =
          (clipperTakeDataLenWord I).toNat)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hov : R.length + 32 ≤ 1024)
    (onVatNoCode :
      Reasoning.Theory.extCodeSizeWord σ (clipperTakeVatTarget v) = ⟨0⟩ →
      RDrev code g (initState cA0 gh bl σStart σ₀ g A I) → P)
    (onVatFailure : ∀ {cAVat σVat outVat AVat},
      typedCallViaEVM (config v)
        { initState cA0 gh bl σStart σ₀ g A I with
          accountMap := σ, createdAccounts := cA }
        (EVM.address v.vat) "flux" 0
        [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
          .int (Int.ofNat slice.toNat)]
        (false,
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σVat, substate := AVat, createdAccounts := cAVat },
          outVat) true →
      Reasoning.Theory.extCodeSizeWord σ (clipperTakeVatTarget v) ≠ ⟨0⟩ →
      RDrev code g (initState cA0 gh bl σStart σ₀ g A I) → P)
    (onSkip : ∀ {cAVat σVat outVat AVat memVat awVat kVat CVat},
      typedCallViaEVM (config v)
        { initState cA0 gh bl σStart σ₀ g A I with
          accountMap := σ, createdAccounts := cA }
        (EVM.address v.vat) "flux" 0
        [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
          .int (Int.ofNat slice.toNat)]
        (true,
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σVat, substate := AVat, createdAccounts := cAVat },
          outVat) true →
      Reasoning.Theory.extCodeSizeWord σ (clipperTakeVatTarget v) ≠ ⟨0⟩ →
      (UInt256.land who solcAddrMask = clipperTakeVatTarget v ∨
        (UInt256.land who solcAddrMask ≠ clipperTakeVatTarget v ∧
          UInt256.land who solcAddrMask =
            UInt256.land (solcSlotWord σVat I ⟨1⟩) solcAddrMask)) →
      clipperTakeMemoryWF memVat awVat →
      RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4701⟩
        (UInt256.land (solcSlotWord σVat I ⟨1⟩) solcAddrMask ::
          slice :: owe :: UInt256.sub tab owe :: UInt256.sub lot slice :: price :: tic ::
          packed :: stopped ::
          dataLen :: dataStart :: who :: max :: amt :: id :: R)
        memVat awVat outVat (cAVat, σVat) kVat CVat → P)
    (onCallbackNoCode : ∀ {cAVat σVat outVat AVat},
      typedCallViaEVM (config v)
        { initState cA0 gh bl σStart σ₀ g A I with
          accountMap := σ, createdAccounts := cA }
        (EVM.address v.vat) "flux" 0
        [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
          .int (Int.ofNat slice.toNat)]
        (true,
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σVat, substate := AVat, createdAccounts := cAVat },
          outVat) true →
      Reasoning.Theory.extCodeSizeWord σ (clipperTakeVatTarget v) ≠ ⟨0⟩ →
      UInt256.land who solcAddrMask ≠ clipperTakeVatTarget v →
      UInt256.land who solcAddrMask ≠
        UInt256.land (solcSlotWord σVat I ⟨1⟩) solcAddrMask →
      Reasoning.Theory.extCodeSizeWord σVat (UInt256.land solcAddrMask who) = ⟨0⟩ →
      RDrev code g (initState cA0 gh bl σStart σ₀ g A I) → P)
    (onCallbackFailure : ∀ {cAVat σVat outVat AVat cACb σCb outCb ACb},
      typedCallViaEVM (config v)
        { initState cA0 gh bl σStart σ₀ g A I with
          accountMap := σ, createdAccounts := cA }
        (EVM.address v.vat) "flux" 0
        [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
          .int (Int.ofNat slice.toNat)]
        (true,
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σVat, substate := AVat, createdAccounts := cAVat },
          outVat) true →
      Reasoning.Theory.extCodeSizeWord σ (clipperTakeVatTarget v) ≠ ⟨0⟩ →
      UInt256.land who solcAddrMask ≠ clipperTakeVatTarget v →
      UInt256.land who solcAddrMask ≠
        UInt256.land (solcSlotWord σVat I ⟨1⟩) solcAddrMask →
      Reasoning.Theory.extCodeSizeWord σVat (UInt256.land solcAddrMask who) ≠ ⟨0⟩ →
      typedCallViaEVM (config v)
        { initState cA0 gh bl σStart σ₀ g A I with
          accountMap := σVat, createdAccounts := cAVat }
        (EVM.address (AccountAddress.ofNat (UInt256.land solcAddrMask who).toNat))
        "clipperCall" 0
        [.address I.source, .int (Int.ofNat owe.toNat),
          .int (Int.ofNat slice.toNat), clipperTakeDataValue I]
        (false,
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σCb, substate := ACb, createdAccounts := cACb },
          outCb) true →
      RDrev code g (initState cA0 gh bl σStart σ₀ g A I) → P)
    (onCallbackSuccess : ∀ {cAVat σVat outVat AVat cACb σCb outCb ACb
        memCb awCb kCb CCb},
      typedCallViaEVM (config v)
        { initState cA0 gh bl σStart σ₀ g A I with
          accountMap := σ, createdAccounts := cA }
        (EVM.address v.vat) "flux" 0
        [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
          .int (Int.ofNat slice.toNat)]
        (true,
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σVat, substate := AVat, createdAccounts := cAVat },
          outVat) true →
      Reasoning.Theory.extCodeSizeWord σ (clipperTakeVatTarget v) ≠ ⟨0⟩ →
      UInt256.land who solcAddrMask ≠ clipperTakeVatTarget v →
      UInt256.land who solcAddrMask ≠
        UInt256.land (solcSlotWord σVat I ⟨1⟩) solcAddrMask →
      Reasoning.Theory.extCodeSizeWord σVat (UInt256.land solcAddrMask who) ≠ ⟨0⟩ →
      typedCallViaEVM (config v)
        { initState cA0 gh bl σStart σ₀ g A I with
          accountMap := σVat, createdAccounts := cAVat }
        (EVM.address (AccountAddress.ofNat (UInt256.land solcAddrMask who).toNat))
        "clipperCall" 0
        [.address I.source, .int (Int.ofNat owe.toNat),
          .int (Int.ofNat slice.toNat), clipperTakeDataValue I]
        (true,
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σCb, substate := ACb, createdAccounts := cACb },
          outCb) true →
      RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4701⟩
        (UInt256.land (solcSlotWord σVat I ⟨1⟩) solcAddrMask ::
          slice :: owe :: UInt256.sub tab owe :: UInt256.sub lot slice :: price :: tic ::
          packed :: stopped ::
          dataLen :: dataStart :: who :: max :: amt :: id :: R)
        memCb awCb outCb (cACb, σCb) kCb CCb →
      clipperTakeMemoryWF memCb awCb → P) : P := by
  obtain ⟨_, _, rd4380⟩ := RD.clipperTakeVatFluxExtcodesizeGuard
    v hpatch rd4223 hbaseSize hbaseRead64 hov
  by_cases hvatCode :
      Reasoning.Theory.extCodeSizeWord σ (clipperTakeVatTarget v) = ⟨0⟩
  · exact onVatNoCode hvatCode
      (RD.clipperTakeVatFluxNoCode v hpatch rd4380 hvatCode hov)
  · obtain ⟨cAVat, σVat, zVat, outVat, AVat, _, _, rd4396, hcallVat, _houtVat⟩ :=
      RD.clipperTakeVatFluxPostCall v hpatch rd4380 hbaseSize hvatCode hdepth hperm hov
    by_cases hzVat : zVat = false
    · exact onVatFailure (by simpa [hzVat] using hcallVat) hvatCode
        (RD.clipperTakeVatFluxCallFailure v hpatch (by simpa [hzVat] using rd4396)
          _houtVat (by simp only [List.length_cons]; omega))
    · have hzVatTrue : zVat = true := Bool.eq_true_of_not_eq_false hzVat
      have hcallVatTrue := (show typedCallViaEVM (config v)
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σ, createdAccounts := cA }
          (EVM.address v.vat) "flux" 0
          [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
            .int (Int.ofNat slice.toNat)]
          (true,
            { initState cA0 gh bl σStart σ₀ g A I with
              accountMap := σVat, substate := AVat, createdAccounts := cAVat },
            outVat) true from by simpa [hzVatTrue] using hcallVat)
      obtain ⟨_, _, rd4414⟩ := RD.clipperTakeVatFluxCallSuccessToPostGuard
        v hpatch (by simpa [hzVatTrue] using rd4396) hov
      let memVat := outVat.write 0 (clipperTakeVatFluxCalldataMem v I who slice baseMem)
        128 (min (⟨0⟩ : UInt256) (UInt256.ofNat outVat.size)).toNat
      have hmemVatSize : memVat.size = 260 := by
        exact clipperTakeVatFluxPostCallMem_size v I who slice hbaseSize
      have hmemVatRead : memVat.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
        exact clipperTakeVatFluxPostCallMem_read64 v I who slice hbaseSize hbaseRead64
      have hmemVat : clipperTakeMemoryWF memVat (UInt256.ofNat 9) :=
        clipperTakeMemoryWF_of_size_read_aw_nine hmemVatSize hmemVatRead rfl
      by_cases hwhoVat : UInt256.land who solcAddrMask = clipperTakeVatTarget v
      · obtain ⟨_, _, rd4701⟩ := RD.clipperTakeSkipClipperCallWhoVat
          v hpatch rd4414 hdataLen
          hwhoVat hov
        exact onSkip hcallVatTrue hvatCode (.inl hwhoVat) hmemVat
          (by simpa [memVat] using rd4701)
      · by_cases hwhoDog : UInt256.land who solcAddrMask =
          UInt256.land (solcSlotWord σVat I ⟨1⟩) solcAddrMask
        · obtain ⟨_, _, rd4701⟩ := RD.clipperTakeSkipClipperCallWhoDog
            v hpatch rd4414 hdataLen hwhoVat
            hwhoDog hov
          exact onSkip hcallVatTrue hvatCode (.inr ⟨hwhoVat, hwhoDog⟩) hmemVat
            (by simpa [memVat] using rd4701)
        · obtain ⟨_, _, rd4530⟩ := RD.clipperTakeClipperCallGuardTrue
            v hpatch rd4414 hdataLen hwhoVat hwhoDog hov
          have hpayloadEnd : dataStart.toNat + dataLen.toNat ≤ I.calldata.size := by
            rw [hdataStartEq, hdataLenEq]
            exact clipperTakePayloadEnd_le I (by simpa [hdataLenEq] using hdataLen)
              hpayload
          obtain ⟨awCb, _, _, rd4664, hmemCb⟩ :=
            RD.clipperTakeClipperCallExtcodesizeGuard v hpatch rd4530
              hmemVatSize hmemVatRead hlenMax hdataLen
              hpayloadEnd
              hov
          by_cases hcallbackCode : Reasoning.Theory.extCodeSizeWord σVat
              (UInt256.land solcAddrMask who) = ⟨0⟩
          · exact onCallbackNoCode hcallVatTrue hvatCode hwhoVat hwhoDog hcallbackCode
              (RD.clipperTakeClipperCallNoCode v hpatch rd4664 hcallbackCode hov)
          · obtain ⟨cACb, σCb, zCb, outCb, ACb, _, _, rd4680, hcallCb, houtCb⟩ :=
              RD.clipperTakeClipperCallPostCall v hpatch rd4664 hmemVatSize hdataLen
                hdataLenEq hdataStartEq hlenMax hpayload hcallbackCode hdepth hperm hov
            by_cases hzCb : zCb = false
            · exact onCallbackFailure hcallVatTrue hvatCode hwhoVat hwhoDog hcallbackCode
                (by simpa [hzCb] using hcallCb)
                (RD.clipperTakeClipperCallFailure v hpatch (by simpa [hzCb] using rd4680)
                  houtCb (by simp only [List.length_cons]; omega))
            · have hzCbTrue : zCb = true := Bool.eq_true_of_not_eq_false hzCb
              obtain ⟨_, _, rd4701⟩ := RD.clipperTakeClipperCallSuccess
                v hpatch (by simpa [hzCbTrue] using rd4680) hov
              have hinSizeNat :
                  (UInt256.ofNat (164 + ABI.paddedSize dataLen.toNat)).toNat =
                    164 + ABI.paddedSize dataLen.toNat := by
                apply ulit_toNat'
                have hpad := clipperTake_paddedSize_le dataLen.toNat
                have hsmall : 164 + (4294967296 + 31) < UInt256.size := by
                  native_decide
                omega
              have hinput : (128 : Nat) +
                    (UInt256.ofNat (164 + ABI.paddedSize dataLen.toNat)).toNat ≤
                  (clipperTakeCallbackCalldataMem I owe slice dataLen dataStart memVat).size := by
                rw [hinSizeNat,
                  clipperTakeCallbackCalldataMem_size I owe slice dataLen dataStart
                    hmemVatSize hdataLen hpayloadEnd]
                have hpad := clipperTake_paddedSize_le dataLen.toNat
                omega
              have hmemCbPost := clipperTakeMemoryWF_after_zero_output_call
                (mem := clipperTakeCallbackCalldataMem I owe slice dataLen dataStart memVat)
                (out := outCb) (aw := awCb) (inOff := (⟨128⟩ : UInt256))
                (inLen := (UInt256.ofNat (164 + ABI.paddedSize dataLen.toNat)).toNat)
                (outOff := 128) hmemCb hinput
              exact onCallbackSuccess hcallVatTrue hvatCode hwhoVat hwhoDog hcallbackCode
                (by simpa [hzCbTrue] using hcallCb) rd4701
                (by simpa using hmemCbPost)

/- With empty callback data the bytecode takes its dedicated skip edge after
   `vat.flux`; the source callback guard is false for the same reason. -/
set_option maxHeartbeats 3000000 in
theorem RD.clipperTakeFluxDataEmptyElim
    {P : Prop} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA0 cA gh bl σ₀ σStart σ I} {g : Sat256} {A : Substate}
    {price slice owe tab lot tic packed stopped dataLen dataStart who max amt id :
      UInt256}
    {R : List UInt256} {baseMem rdata : ByteArray} {k C : ℕ}
    (rd4223 : RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4223⟩
      (slice :: owe :: tab :: lot :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: R)
      baseMem (UInt256.ofNat 7) rdata (cA, σ) k C)
    (hbaseSize : baseMem.size = 196)
    (hbaseRead64 : baseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hdataLen : dataLen = ⟨0⟩)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hov : R.length + 32 ≤ 1024)
    (onVatNoCode :
      Reasoning.Theory.extCodeSizeWord σ (clipperTakeVatTarget v) = ⟨0⟩ →
      RDrev code g (initState cA0 gh bl σStart σ₀ g A I) → P)
    (onVatFailure : ∀ {cAVat σVat outVat AVat},
      typedCallViaEVM (config v)
        { initState cA0 gh bl σStart σ₀ g A I with
          accountMap := σ, createdAccounts := cA }
        (EVM.address v.vat) "flux" 0
        [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
          .int (Int.ofNat slice.toNat)]
        (false,
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σVat, substate := AVat, createdAccounts := cAVat },
          outVat) true →
      Reasoning.Theory.extCodeSizeWord σ (clipperTakeVatTarget v) ≠ ⟨0⟩ →
      RDrev code g (initState cA0 gh bl σStart σ₀ g A I) → P)
    (onSuccess : ∀ {cAVat σVat outVat AVat memVat awVat kVat CVat},
      typedCallViaEVM (config v)
        { initState cA0 gh bl σStart σ₀ g A I with
          accountMap := σ, createdAccounts := cA }
        (EVM.address v.vat) "flux" 0
        [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
          .int (Int.ofNat slice.toNat)]
        (true,
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σVat, substate := AVat, createdAccounts := cAVat },
          outVat) true →
      Reasoning.Theory.extCodeSizeWord σ (clipperTakeVatTarget v) ≠ ⟨0⟩ →
      clipperTakeMemoryWF memVat awVat →
      RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4701⟩
        (UInt256.land (solcSlotWord σVat I ⟨1⟩) solcAddrMask ::
          slice :: owe :: UInt256.sub tab owe :: UInt256.sub lot slice :: price ::
          tic :: packed :: stopped :: dataLen :: dataStart :: who :: max :: amt ::
          id :: R)
        memVat awVat outVat (cAVat, σVat) kVat CVat → P) : P := by
  obtain ⟨_, _, rd4380⟩ := RD.clipperTakeVatFluxExtcodesizeGuard
    v hpatch rd4223 hbaseSize hbaseRead64 hov
  by_cases hvatCode :
      Reasoning.Theory.extCodeSizeWord σ (clipperTakeVatTarget v) = ⟨0⟩
  · exact onVatNoCode hvatCode
      (RD.clipperTakeVatFluxNoCode v hpatch rd4380 hvatCode hov)
  · obtain ⟨cAVat, σVat, zVat, outVat, AVat, _, _, rd4396, hcallVat,
        _houtVat⟩ :=
      RD.clipperTakeVatFluxPostCall v hpatch rd4380 hbaseSize hvatCode hdepth
        hperm hov
    by_cases hzVat : zVat = false
    · exact onVatFailure (by simpa [hzVat] using hcallVat) hvatCode
        (RD.clipperTakeVatFluxCallFailure v hpatch (by simpa [hzVat] using rd4396)
          _houtVat (by simp only [List.length_cons]; omega))
    · have hzVatTrue : zVat = true := Bool.eq_true_of_not_eq_false hzVat
      have hcallVatTrue := (show typedCallViaEVM (config v)
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σ, createdAccounts := cA }
          (EVM.address v.vat) "flux" 0
          [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
            .int (Int.ofNat slice.toNat)]
          (true,
            { initState cA0 gh bl σStart σ₀ g A I with
              accountMap := σVat, substate := AVat, createdAccounts := cAVat },
            outVat) true from by simpa [hzVatTrue] using hcallVat)
      obtain ⟨_, _, rd4414⟩ := RD.clipperTakeVatFluxCallSuccessToPostGuard
        v hpatch (by simpa [hzVatTrue] using rd4396) hov
      let memVat := outVat.write 0
        (clipperTakeVatFluxCalldataMem v I who slice baseMem) 128
        (min (⟨0⟩ : UInt256) (UInt256.ofNat outVat.size)).toNat
      have hmemVatSize : memVat.size = 260 :=
        clipperTakeVatFluxPostCallMem_size v I who slice hbaseSize
      have hmemVatRead : memVat.readWithPadding 64 32 =
          UInt256.toByteArray ⟨128⟩ :=
        clipperTakeVatFluxPostCallMem_read64 v I who slice hbaseSize hbaseRead64
      have hmemVat : clipperTakeMemoryWF memVat (UInt256.ofNat 9) :=
        clipperTakeMemoryWF_of_size_read_aw_nine hmemVatSize hmemVatRead rfl
      obtain ⟨_, _, rd4701⟩ := RD.clipperTakeSkipClipperCallDataEmpty
        v hpatch rd4414 hdataLen hov
      exact onSuccess hcallVatTrue hvatCode hmemVat
        (by simpa [memVat] using rd4701)

end Benchmarks.Dss.Clipper
