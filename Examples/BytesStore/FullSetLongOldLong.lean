import Examples.BytesStore.FullPacketTag

/-!
# BytesStore — full `set(bytes)` long writes over old long storage

This module keeps the long `set(bytes)` old-long branches out of the already large
full-contract dispatcher module.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000

namespace BytesStore

theorem bytesStoreX_setCurrentCleanupOldLongLongToLoop {cA gh bl σinit σ σ₀ A I}
    {g : Sat256} {oldLen len ret : UInt256} {tail : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2302⟩
      (⟨0⟩ :: oldLen :: len :: ret :: tail) mem aw rdata (cA, σ) k C)
    (holdLong : UInt256.gt oldLen ⟨31⟩ = ⟨1⟩)
    (hgtOldNew : UInt256.gt oldLen len = ⟨1⟩)
    (hlong : UInt256.lt len ⟨32⟩ = ⟨0⟩)
    (hov : tail.length + 16 ≤ 1024) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2359⟩
      (⟨0⟩ ::
        UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩) ::
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
          StringStoreLite.clearCurrentBaseWord) ::
        ⟨0⟩ :: oldLen :: len :: ret :: tail)
      (StringStoreLite.clearCurrentBaseMemFrom mem)
      (StringStoreLite.clearCurrentHashAw aw) rdata (cA, σ) k C := by
  obtain ⟨_, _, rd2302⟩ := hreach
  have rd2308 := evm_run rd2302 with [
    jumpdest, push1 ⟨31⟩, dup3, gt, iszero, push2 ⟨1809⟩]
  have rd2310 := rd2308.jumpiNT (by native_decide)
    (by rw [holdLong]; decide)
    (by simp only [List.length_cons]; omega)
  have rd2318 := evm_run rd2310 with [dup3, dup3, gt, iszero, push2 ⟨1809⟩]
  have rd2320 := rd2318.jumpiNT (by native_decide)
    (by rw [hgtOldNew]; decide)
    (by simp only [List.length_cons]; omega)
  have rd2343 := evm_run rd2320 with [
    dup1, push0,
    raw mstore (Cₘ (StringStoreLite.clearCurrentBaseAw aw) - Cₘ aw)
      (StringStoreLite.clearCurrentBaseMemFrom mem)
      (StringStoreLite.clearCurrentBaseAw aw) (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          StringStoreLite.clearCurrentBaseAw])
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256
      (Cₘ (StringStoreLite.clearCurrentHashAw aw) -
        Cₘ (StringStoreLite.clearCurrentBaseAw aw))
      StringStoreLite.clearCurrentBaseWord
      (StringStoreLite.clearCurrentHashAw aw) (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          StringStoreLite.clearCurrentHashAw, StringStoreLite.clearCurrentBaseAw])
      (StringStoreLite.clearCurrentBaseMemFrom_keccak mem) (by rfl) (by evm_ov),
    push1 ⟨31⟩, dup5, add, push1 ⟨5⟩, shr, push1 ⟨32⟩, dup6, lt, iszero,
    push2 ⟨2345⟩]
  have rd2345 := rd2343.jumpiT (by native_decide)
    (by rw [hlong]; decide)
    (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd2345 with [
    jumpdest, swap1, dup2, add, swap1, push1 ⟨31⟩, dup5, add,
    push1 ⟨5⟩, shr, sub, push0]⟩

theorem bytesStoreX_setLongOldLongClearReachWriteBranchWithLoopSchedule
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart oldLen : UInt256}
    {fuel : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (holdLen : oldLen = UInt256.div (StringStoreLite.currentLengthHeaderWord σ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldLen len = ⟨1⟩)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ i)
          (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩)
            (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩))) = ⟨0⟩)
    (hdone :
      UInt256.lt (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ fuel)
        (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)) = ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
        ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.clearCurrentBaseMemFrom
        (StringStoreLite.setPaddedMem I.calldata len payloadStart))
      (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
      ByteArray.empty
      (cA, clearDataWordsForwardFrom I.codeOwner σ
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
          StringStoreLite.clearCurrentBaseWord)
        ⟨0⟩ fuel) k C := by
  have hdecoder := bytesStoreX_setReachWriteHeaderDecoderNonempty
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) hreach hnz hlenMax hsrc
  have hvalidHeader :
      UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (StringStoreLite.currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
        ⟨0⟩ := by
    simpa [← holdLen] using hvalid
  have hdecoded := bytesStoreX_bytesLengthDecoderLongValidMem
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := StringStoreLite.currentLengthHeaderWord σ I) (ret := ⟨2428⟩)
    (rest := [len, ⟨2434⟩, len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩,
      ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I])
    (mem := StringStoreLite.setPaddedMem I.calldata len payloadStart)
    (aw := StringStoreLite.setHelperEntryAw len) (rdata := ByteArray.empty)
    hdecoder hflag hvalidHeader
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2428₀⟩ := hdecoded
  obtain ⟨_, _, rd2428⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2428⟩
        [oldLen, len, ⟨2434⟩, len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩,
          ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
        (StringStoreLite.setPaddedMem I.calldata len payloadStart)
        (StringStoreLite.setHelperEntryAw len) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [← holdLen] using rd2428₀⟩
  have hcleanupReach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2302⟩
      [⟨0⟩, oldLen, len, ⟨2434⟩, len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.setPaddedMem I.calldata len payloadStart)
      (StringStoreLite.setHelperEntryAw len) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, evm_run rd2428 with [
      jumpdest, dup5, push2 ⟨2302⟩, jump (by native_decide)]⟩
  have hgt31 : UInt256.lt ⟨31⟩ oldLen ≠ ⟨0⟩ :=
    StringStoreLite.clearCurrentLongValid_gt31
      (header := StringStoreLite.currentLengthHeaderWord σ I) (len := oldLen)
      hflag hvalid
  have holdLong : UInt256.gt oldLen ⟨31⟩ = ⟨1⟩ := by
    rw [show UInt256.gt oldLen ⟨31⟩ = UInt256.lt ⟨31⟩ oldLen from rfl]
    exact StringStoreLite.clearCurrent_ult_eq_one_of_ne_zero hgt31
  have hlongWord : UInt256.lt len ⟨32⟩ = ⟨0⟩ :=
    ult_zero (by
      have hle : 32 ≤ len.toNat := Nat.le_of_not_gt hlong
      simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hle)
  have hloopEntry := bytesStoreX_setCurrentCleanupOldLongLongToLoop
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (oldLen := oldLen) (len := len) (ret := ⟨2434⟩)
    (tail := [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
      payloadStart, ⟨263⟩, bytesStoreSelWord I])
    (mem := StringStoreLite.setPaddedMem I.calldata len payloadStart)
    (aw := StringStoreLite.setHelperEntryAw len) (rdata := ByteArray.empty)
    hcleanupReach holdLong hgtOldNew hlongWord
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hloop := bytesStoreX_setClearDataWordsLoopGenerated
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (idx := (⟨0⟩ : UInt256))
    (count := UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩)
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩))
    (base := UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
      StringStoreLite.clearCurrentBaseWord)
    (dead₀ := (⟨0⟩ : UInt256)) (dead₁ := oldLen) (dead₂ := len)
    (ret := (⟨2434⟩ : UInt256))
    (rest := [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
      payloadStart, ⟨263⟩, bytesStoreSelWord I])
    (mem := StringStoreLite.clearCurrentBaseMemFrom
      (StringStoreLite.setPaddedMem I.calldata len payloadStart))
    (aw := StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
    (rdata := ByteArray.empty) (fuel := fuel)
    hperm hloopEntry hcontinue hdone (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  simpa using hloop

theorem bytesStoreX_setLongOldLongClearReachWriteBranch
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart oldLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (holdLen : oldLen = UInt256.div (StringStoreLite.currentLengthHeaderWord σ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldLen len = ⟨1⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
        ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.clearCurrentBaseMemFrom
        (StringStoreLite.setPaddedMem I.calldata len payloadStart))
      (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
      ByteArray.empty
      (cA, clearDataWordsForwardFrom I.codeOwner σ
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
          StringStoreLite.clearCurrentBaseWord)
        ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat) k C := by
  let count := UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩)
    (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)
  have hcontinue : ∀ i, i < count.toNat →
      UInt256.isZero
        (UInt256.lt (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ i) count) =
          ⟨0⟩ := by
    intro i hi
    have hidx : (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ i).toNat = i := by
      rw [StringStoreLite.clearDataWordsLoopIndex_zero_ofNat]
      exact ulit_toNat' i (lt_trans hi count.val.isLt)
    have hlt : UInt256.lt (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ i) count = ⟨1⟩ :=
      ult_one (by simpa [hidx] using hi)
    rw [hlt]
    decide
  have hdone :
      UInt256.lt (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ count.toNat) count =
        ⟨0⟩ := by
    rw [StringStoreLite.clearDataWordsLoopIndex_zero_ofNat, u256_ofNat_toNat count]
    exact ult_zero (a := count) (b := count) (Nat.le_refl _)
  simpa [count] using
    bytesStoreX_setLongOldLongClearReachWriteBranchWithLoopSchedule
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (len := len) (payloadStart := payloadStart)
      (oldLen := oldLen) (fuel := count.toNat)
      hperm hreach hnz hlong hlenMax hsrc hflag holdLen hvalid hgtOldNew
      hcontinue hdone

theorem bytesStoreSetNewLongOldLongNoClearValidRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hflag :
      UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew :
      UInt256.gt
        (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let value : ByteArray := StringStoreLite.setDecodedValueBytes I
  let oldLen : UInt256 := UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩
  let oldFuel : Nat := (oldLen.toNat + 31) / 32
  let clearFuel : Nat := (value.size + 31) / 32
  let header : UInt256 := solidityBytesHeaderWord value.size
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore
    (writeSolidityBytesDataWordsFrom
      (clearSolidityBytesDataWordsFrom evmSolm0 ⟨0⟩ clearFuel (oldFuel - clearFuel))
      ⟨0⟩ value 0 clearFuel)
    (writeSolidityBytesDataWordsFrom
      (clearSolidityBytesDataWordsFrom evmSolm0 ⟨0⟩ clearFuel (oldFuel - clearFuel))
      ⟨0⟩ value 0 clearFuel).executionEnv.codeOwner
    ⟨0⟩ header
  have hd := bytesStoreDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_set (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    rw [StringStoreLite.setPayloadStart_toNat I.calldata hoffMax]
    exact StringStoreLite.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayloadList
  have hlenMaxLen : len.toNat ≤ ABI.solcMaxU64 := by
    dsimp [len]
    exact Nat.le_of_not_gt hlenMax
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value, len]
    rw [StringStoreLite.setDecodedValueBytes_size hpayloadList]
  have hlong : ¬ len.toNat < 32 := by
    simpa [len] using hnewLong
  have hvalueSizeLong : ¬ value.size < 32 := by
    rw [hsizeDecoded]
    exact hlong
  have hretWord :
      UInt256.ofNat value.size = len := by
    rw [hsizeDecoded]
    exact u256_ofNat_toNat len
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact StringStoreLite.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMaxLen
  have hflagCore :
      UInt256.land (StringStoreLite.currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩ := by
    simpa [bytesStoreCurrentLengthHeaderWord, StringStoreLite.currentLengthHeaderWord]
      using hflag
  have holdLenCore :
      oldLen = UInt256.div (StringStoreLite.currentLengthHeaderWord σ_evm I) ⟨2⟩ := by
    simp [oldLen, bytesStoreCurrentLengthHeaderWord,
      StringStoreLite.currentLengthHeaderWord]
  have hvalidCore :
      UInt256.sub (UInt256.land (StringStoreLite.currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [oldLen, bytesStoreCurrentLengthHeaderWord,
      StringStoreLite.currentLengthHeaderWord] using hvalid
  have hgtOldNewCore : UInt256.gt oldLen len = ⟨0⟩ := by
    simpa [oldLen, len, bytesStoreCurrentLengthHeaderWord,
      StringStoreLite.currentLengthHeaderWord] using hgtOldNew
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    StringStoreLite.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    StringStoreLite.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hdecodedReach := bytesStoreX_setDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz36 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hlenEvm :
      uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = len := by
    simpa [len] using StringStoreLite.setLengthWord_eq_abi I.calldata hoffMax
  have hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [len, payloadStart, hlenEvm] using hdecodedReach
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadCurrentLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hwrite :
      writeStorage? bytesStoreConfig evmSolm0 { base := "current", steps := [] }
        .bytes (.bytes value) = .ok evmSolm1 := by
    have hwrite₀ := bytesStoreWriteCurrentLongFromLongPrepared (evm := evmSolm0)
      (header := bytesStoreCurrentLengthHeaderWord σ_evm I) (len := oldLen)
      (value := value)
      hvalueSizeLong hload hflag rfl (by simpa [oldLen] using hvalid)
    simpa [evmSolm0, evmSolm1, value, header, oldFuel, clearFuel,
      solidityBytesDataWordCount] using hwrite₀
  have hsolmMap :
      evmSolm1.accountMap =
        sstoreAccountMap I.codeOwner
          (solidityDataWordsForwardFrom I.codeOwner
            (clearDataWordsForwardFrom I.codeOwner σ_solm
              (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat clearFuel) (oldFuel - clearFuel))
            ⟨0⟩ value 0 clearFuel)
          ⟨0⟩ header := by
    simpa [evmSolm1, evmSolm0, oldFuel, clearFuel, initState,
      bytesLikeDataBase, solidityBytesDataBaseSlot] using
      storageStore_clear_writeSolidityBytesDataWordsFrom_accountMap
        (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        ⟨0⟩ clearFuel (oldFuel - clearFuel)
        ⟨0⟩ value 0 clearFuel ⟨0⟩ header
  have hCreated : cA = evmSolm1.createdAccounts := by
    simp [evmSolm1, evmSolm0, writeSolidityBytesDataWordsFrom_createdAccounts,
      clearSolidityBytesDataWordsFrom_createdAccounts, storageStore_createdAccounts, initState]
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setTransition.returnType := by
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [hsizeDecoded]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  have holdLenLe : oldLen.toNat ≤ len.toNat :=
    StringStoreLite.ugt_eq_zero_toNat_le hgtOldNewCore
  by_cases hmod : len.toNat % 32 = 0
  · have hret :
        RDret bytesStoreBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (cA, sstoreAccountMap I.codeOwner
            (StringStoreLite.longDataWordsForwardFrom I.codeOwner σ_evm
              StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
              (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
              (StringStoreLite.clearCurrentBaseMemFrom
                (StringStoreLite.setPaddedMem I.calldata len payloadStart))
              (len.toNat / 32))
            ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
          (UInt256.toByteArray len) :=
      bytesStoreX_setLongNoTailReturnsOldLongNoClearFromReach
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) (len := len) (payloadStart := payloadStart)
        (oldLen := oldLen)
        hperm hreach hnz hlong hlenMaxLen hsrc hflagCore holdLenCore hvalidCore
        hgtOldNewCore hmod
    let evmPostMap :=
      sstoreAccountMap I.codeOwner
        (StringStoreLite.longDataWordsForwardFrom I.codeOwner σ_evm
          StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
          (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
          (StringStoreLite.clearCurrentBaseMemFrom
            (StringStoreLite.setPaddedMem I.calldata len payloadStart))
          (len.toNat / 32))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    have hAccountsPost : accountMapEquiv evmPostMap evmSolm1.accountMap := by
      have hgenAccounts :
          accountMapEquiv evmPostMap
            (sstoreAccountMap I.codeOwner
              (StringStoreLite.longDataWordsForwardFrom I.codeOwner σ_solm
                StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
                (StringStoreLite.clearCurrentBaseMemFrom
                  (StringStoreLite.setPaddedMem I.calldata len payloadStart))
                (len.toNat / 32))
              ⟨0⟩ header) := by
        dsimp [evmPostMap]
        simpa [hheaderEq] using
          accountMapEquiv_sstore_header_after_longDataWordsForwardFrom
            (owner := I.codeOwner) (slot := StringStoreLite.clearCurrentBaseWord)
            (stride := (⟨32⟩ : UInt256)) (ptr := (⟨128⟩ : UInt256))
            (aw := StringStoreLite.clearCurrentHashAw
              (StringStoreLite.setHelperEntryAw len))
            (mem := StringStoreLite.clearCurrentBaseMemFrom
              (StringStoreLite.setPaddedMem I.calldata len payloadStart))
            (fuel := len.toNat / 32) (headerSlot := ⟨0⟩) (header := header)
            hAccounts
      have hclearFuelEq : clearFuel = len.toNat / 32 := by
        dsimp [clearFuel]
        rw [hsizeDecoded]
        exact solidityBytesDataWordCount_eq_div_of_mod_zero hmod
      have holdFuelLe : oldFuel ≤ len.toNat / 32 := by
        dsimp [oldFuel]
        rw [← solidityBytesDataWordCount_eq_div_of_mod_zero hmod]
        exact solidityBytesDataWordCount_mono holdLenLe
      have htailClearZero : oldFuel - clearFuel = 0 := by
        omega
      have htailClearZero' : oldFuel - len.toNat / 32 = 0 := by
        omega
      have hdataBridge :=
        StringStoreLite.accountMapEquiv_solidityDataWordsForwardFrom_longDataWordsForwardFrom_full
          (I := I) (len := len) (payloadStart := payloadStart) (owner := I.codeOwner)
          hnz hlenMaxLen hsrc hsizeDecoded (by rfl) (by rfl) hoffMax
          (τ := σ_solm) (i := 0) (fuel := len.toNat / 32) (by omega)
      have hsolmTarget :
          accountMapEquiv
            (sstoreAccountMap I.codeOwner
              (StringStoreLite.longDataWordsForwardFrom I.codeOwner σ_solm
                StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
                (StringStoreLite.clearCurrentBaseMemFrom
                  (StringStoreLite.setPaddedMem I.calldata len payloadStart))
                (len.toNat / 32))
              ⟨0⟩ header)
            evmSolm1.accountMap := by
        have hbase0 : StringStoreLite.clearCurrentBaseWord + UInt256.ofNat 0 =
            StringStoreLite.clearCurrentBaseWord := by
          simpa using StringStoreLite.uint256_add_zero_right
            StringStoreLite.clearCurrentBaseWord
        have hzero : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := by
          native_decide
        have hstride : UInt256.ofNat 32 = (⟨32⟩ : UInt256) := by
          native_decide
        rw [hsolmMap]
        simpa [value, hclearFuelEq, htailClearZero, htailClearZero', hbase0, hzero,
          hstride,
          StringStoreLite.uint256_add_zero_right,
          clearDataWordsForwardFrom, bytesLikeDataBase, solidityBytesDataBaseSlot,
          StringStoreLite.clearCurrentBaseWord] using
          accountMapEquiv_sstore_header_after_solidityDataWordsForwardFrom
            (headerSlot := ⟨0⟩) (header := header)
            (accountMapEquiv.symm hdataBridge)
      exact accountMapEquiv.trans hgenAccounts hsolmTarget
    exact bytesStoreSetRuntimeOfWriteAccountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value)
      (o := UInt256.toByteArray len) (acc := (cA, evmPostMap)) (evmCurrent := evmSolm1)
      hcode hwv (by simpa [evmPostMap] using hret) hd hdec hwrite hCreated
      hAccountsPost henc
  · let wordTail : UInt256 :=
      UInt256.ofNat (fromBytesBigEndian
        (((value).toList.drop (32 * (len.toNat / 32))) ++
          List.replicate
            (32 - ((value).toList.drop (32 * (len.toNat / 32))).length)
            0))
    have hwordTail :
        wordTail = UInt256.ofNat (fromBytesBigEndian
          (((StringStoreLite.setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))) ++
            List.replicate
              (32 - ((StringStoreLite.setDecodedValueBytes I).toList.drop
                (32 * (len.toNat / 32))).length)
              0)) := by
      rfl
    have hret :
        RDret bytesStoreBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (cA, sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (StringStoreLite.longDataWordsForwardFrom I.codeOwner σ_evm
                StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
                (StringStoreLite.clearCurrentBaseMemFrom
                  (StringStoreLite.setPaddedMem I.calldata len payloadStart))
                (len.toNat / 32))
              (StringStoreLite.longDataWordsLoopSlot StringStoreLite.clearCurrentBaseWord
                (len.toNat / 32))
              (StringStoreLite.longDataTailMaskedWord wordTail len))
            ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
          (UInt256.toByteArray len) :=
      bytesStoreX_setLongTailReturnsOldLongNoClearFromReach
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) (len := len) (payloadStart := payloadStart)
        (oldLen := oldLen) (wordTail := wordTail)
        hperm hreach hnz hlong hlenMaxLen hsrc hflagCore holdLenCore hvalidCore
        hgtOldNewCore hmod (by rfl) (by rfl) hoffMax hwordTail
    let evmPostMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (StringStoreLite.longDataWordsForwardFrom I.codeOwner σ_evm
            StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
            (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
            (StringStoreLite.clearCurrentBaseMemFrom
              (StringStoreLite.setPaddedMem I.calldata len payloadStart))
            (len.toNat / 32))
          (StringStoreLite.longDataWordsLoopSlot StringStoreLite.clearCurrentBaseWord
            (len.toNat / 32))
          (StringStoreLite.longDataTailMaskedWord wordTail len))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    have hAccountsPost : accountMapEquiv evmPostMap evmSolm1.accountMap := by
      have hgenAccounts :
          accountMapEquiv evmPostMap
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (StringStoreLite.longDataWordsForwardFrom I.codeOwner σ_solm
                  StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                  (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
                  (StringStoreLite.clearCurrentBaseMemFrom
                    (StringStoreLite.setPaddedMem I.calldata len payloadStart))
                  (len.toNat / 32))
                (StringStoreLite.longDataWordsLoopSlot StringStoreLite.clearCurrentBaseWord
                  (len.toNat / 32))
                (StringStoreLite.longDataTailMaskedWord wordTail len))
              ⟨0⟩ header) := by
        dsimp [evmPostMap]
        simpa [hheaderEq] using
          accountMapEquiv_sstore_tail_header_after_longDataWordsForwardFrom
            (owner := I.codeOwner) (slot := StringStoreLite.clearCurrentBaseWord)
            (stride := (⟨32⟩ : UInt256)) (ptr := (⟨128⟩ : UInt256))
            (aw := StringStoreLite.clearCurrentHashAw
              (StringStoreLite.setHelperEntryAw len))
            (mem := StringStoreLite.clearCurrentBaseMemFrom
              (StringStoreLite.setPaddedMem I.calldata len payloadStart))
            (fuel := len.toNat / 32)
            (tailSlot := StringStoreLite.longDataWordsLoopSlot
              StringStoreLite.clearCurrentBaseWord (len.toNat / 32))
            (tailWord := StringStoreLite.longDataTailMaskedWord wordTail len)
            (headerSlot := ⟨0⟩) (header := header)
            hAccounts
      have hclearFuelEq : clearFuel = (len.toNat + 31) / 32 := by
        dsimp [clearFuel]
        rw [hsizeDecoded]
      have holdFuelLe : oldFuel ≤ (len.toNat + 31) / 32 := by
        dsimp [oldFuel]
        exact solidityBytesDataWordCount_mono holdLenLe
      have htailClearZero : oldFuel - clearFuel = 0 := by
        omega
      have htailClearZero' : oldFuel - (len.toNat + 31) / 32 = 0 := by
        omega
      have hceilTail : (len.toNat + 31) / 32 = len.toNat / 32 + 1 := by
        have hdiv := Nat.div_add_mod len.toNat 32
        have hremLt := Nat.mod_lt len.toNat (by decide : 0 < 32)
        omega
      have htailClearZero'' : oldFuel - (len.toNat / 32 + 1) = 0 := by
        omega
      have hdataBridge :=
        StringStoreLite.accountMapEquiv_solidityDataWordsForwardFrom_longDataWordsForwardFrom_tail
          (I := I) (len := len) (payloadStart := payloadStart) (wordTail := wordTail)
          (owner := I.codeOwner)
          hnz hlenMaxLen hsrc hsizeDecoded hlong (by rfl) (by rfl) hoffMax hmod
          hwordTail σ_solm
      have hsolmTarget :
          accountMapEquiv
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (StringStoreLite.longDataWordsForwardFrom I.codeOwner σ_solm
                  StringStoreLite.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                  (StringStoreLite.clearCurrentHashAw (StringStoreLite.setHelperEntryAw len))
                  (StringStoreLite.clearCurrentBaseMemFrom
                    (StringStoreLite.setPaddedMem I.calldata len payloadStart))
                  (len.toNat / 32))
                (StringStoreLite.longDataWordsLoopSlot StringStoreLite.clearCurrentBaseWord
                  (len.toNat / 32))
                (StringStoreLite.longDataTailMaskedWord wordTail len))
              ⟨0⟩ header)
            evmSolm1.accountMap := by
        have hbase0 : StringStoreLite.clearCurrentBaseWord + UInt256.ofNat 0 =
            StringStoreLite.clearCurrentBaseWord := by
          simpa using StringStoreLite.uint256_add_zero_right
            StringStoreLite.clearCurrentBaseWord
        have hzero : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := by
          native_decide
        have hstride : UInt256.ofNat 32 = (⟨32⟩ : UInt256) := by
          native_decide
        rw [hsolmMap]
        simpa [value, hclearFuelEq, htailClearZero, htailClearZero', htailClearZero'',
          hceilTail, hbase0, hzero, hstride, StringStoreLite.uint256_add_zero_right,
          clearDataWordsForwardFrom, bytesLikeDataBase, solidityBytesDataBaseSlot,
          StringStoreLite.clearCurrentBaseWord] using
          accountMapEquiv_sstore_header_after_solidityDataWordsForwardFrom
            (headerSlot := ⟨0⟩) (header := header)
            (accountMapEquiv.symm hdataBridge)
      exact accountMapEquiv.trans hgenAccounts hsolmTarget
    exact bytesStoreSetRuntimeOfWriteAccountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value)
      (o := UInt256.toByteArray len) (acc := (cA, evmPostMap)) (evmCurrent := evmSolm1)
      hcode hwv (by simpa [evmPostMap] using hret) hd hdec hwrite hCreated
      hAccountsPost henc

end BytesStore
