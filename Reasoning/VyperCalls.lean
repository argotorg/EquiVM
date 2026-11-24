import Reasoning.ExternalCall
import Reasoning.Solc
import Reasoning.VyperDispatch

variable {fork : Ethereum.Fork}

/-!
# Typed external calls in Vyper bytecode

Vyper's `extcall`/`staticcall` to an interface function is a `CALL` (value 0) or `STATICCALL`
whose input is the ABI encoding the spec's `externalABI.encode?` produces.  The bridges below pair
the opcode's `RD` step (`RD.call`/`RD.solcStaticcall`, with the depth-limit twins) with Stele's
`typedCallViaEVM` through `callCoincides`, carrying a `SourceState` across the call.  The decode
lemmas evaluate `decodeReturnValue?` (modern mode) on a `uint256`/`bool` return word.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch

namespace Reasoning.VyperCalls

set_option maxRecDepth 2000000

/-- A `CALL` with value 0 at `pc`, bridged to Stele's typed call: the Stele state `evm` follows the
summary's account map through `hs`; the call's input is the encoding `hcd` of the spec's
arguments. -/
theorem typedCallBridge {code : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State} {pc : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ}
    {evm : EVM.State} {cfg : Config} {name : Ident} {args : List Value}
    {gasArg target inOffset inSize outOffset outSize : UInt256}
    (h : RD fork code I g s0 pc (gasArg :: target :: ⟨0⟩ :: inOffset :: inSize :: outOffset :: outSize :: R) mem aw rdata σ k C)
    (hs : SourceState s0 I σ evm)
    (hdec : decode code pc = some (.CALL, .none))
    (hcd : cfg.externalABI.encode? name args = some (mem.readWithPadding inOffset.toNat inSize.toNat))
    (hsmall : inSize.toNat ≤ 2 ^ 64)
    (hov : R.length + 1 ≤ 1024) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (z : Bool) (out : ByteArray) (k' C' : ℕ),
      typedCallViaEVM fork cfg evm (AccountAddress.ofUInt256 target) name 0 args (z, evm', out) ∧
      SourceState s0 I σ' evm' ∧
      RD fork code I g s0 (pc + ⟨1⟩) ((if z then ⟨1⟩ else ⟨0⟩) :: R)
        (out.write 0 mem outOffset.toNat (min outSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat inSize.toNat) outOffset.toNat outSize.toNat))
        out σ' k' C' ∧
      out.size < 2 ^ 138 ∧
      (σ' = σ ∨ ∃ (A_in : Substate) (callGas g' : UInt256) (A' : Substate),
        (σ', g', A', z, out) = Ethereum.EVM.Θ fork σ s0.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 target) (toExecute fork σ (AccountAddress.ofUInt256 target))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          (mem.readWithPadding inOffset.toNat inSize.toNat) (I.depth + 1) I.header I.blobVersionedHashes I.blocks I.perm) := by
  by_cases hd : I.depth = 1024
  · obtain ⟨k', C', rd⟩ := h.callDepthLimit hdec hd hov
    refine ⟨{ evm with substate := (Ethereum.EVM.callSubstate fork evm.accountMap (AccountAddress.ofUInt256 target) evm.substate) }, σ, false,
      ByteArray.empty, k', C', ?_, ⟨hs.world, hs.env, hs.accounts⟩, rd, by decide, Or.inl rfl⟩
    refine ⟨_, hcd, callViaEVM.callNotMade rfl rfl ?_⟩
    intro hn
    exact hn.2 (by rw [hs.env]; exact hd)
  · have hdlt : I.depth.val < 1024 := by
      have hb := I.depth.isLt
      have hn : I.depth.val ≠ 1024 := fun hv => hd (Fin.ext hv)
      omega
    obtain ⟨σ', z, out, A_in, callGas, k', C', ⟨g'', A', hΘ⟩, rd, _⟩ := h.call hdec hdlt hov
    have hΘ0 := hΘ
    have hsize : out.size < 2 ^ 138 :=
      Theta_returnData_size_lt_2pow138_of_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hΘ
        (le_trans (Ethereum.EVM.ByteArray.readWithPadding_size_le mem inOffset.toNat inSize.toNat)
          (le_trans hsmall Ethereum.EVM.pow_two_64_le_maxReturnDataSizeByGas))
    rw [hs.accounts, ← hs.world, ← hs.env] at hΘ
    have hΘ' : (σ', g'', A', z, out) =
        Ethereum.EVM.Θ fork evm.accountMap evm.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat evm.executionEnv.codeOwner)) evm.executionEnv.sender
          (AccountAddress.ofUInt256 target) (toExecute fork evm.accountMap (AccountAddress.ofUInt256 target))
          callGas (UInt256.ofNat evm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          (mem.readWithPadding inOffset.toNat inSize.toNat) (evm.executionEnv.depth + 1)
          evm.executionEnv.header evm.executionEnv.blobVersionedHashes evm.executionEnv.blocks
          (true && evm.executionEnv.perm) := by
      rw [Bool.true_and]; exact hΘ
    have hcall := callCoincides (cfg := cfg) (name := name) (args := args) (callPerm := true)
      (by rw [hs.env]; exact hd) rfl hcd hΘ'
    exact ⟨_, σ', z, out, k', C', hcall, ⟨hs.world, hs.env, rfl⟩, rd, hsize, Or.inr ⟨A_in, callGas, g'', A', hΘ0⟩⟩

/-- A `STATICCALL` at `pc`, bridged to Stele's typed view call (`perm := false`). -/
theorem typedStaticCallBridge {code : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State} {pc : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ}
    {evm : EVM.State} {cfg : Config} {name : Ident} {args : List Value}
    {gasArg target inOffset inSize outOffset outSize : UInt256}
    (h : RD fork code I g s0 pc (gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: R) mem aw rdata σ k C)
    (hs : SourceState s0 I σ evm)
    (hdec : decode code pc = some (.STATICCALL, .none))
    (hcd : cfg.externalABI.encode? name args = some (mem.readWithPadding inOffset.toNat inSize.toNat))
    (hsmall : inSize.toNat ≤ 2 ^ 64)
    (hov : R.length + 1 ≤ 1024) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (z : Bool) (out : ByteArray) (k' C' : ℕ),
      typedCallViaEVM fork cfg evm (AccountAddress.ofUInt256 target) name 0 args (z, evm', out) false ∧
      SourceState s0 I σ' evm' ∧
      RD fork code I g s0 (pc + ⟨1⟩) ((if z then ⟨1⟩ else ⟨0⟩) :: R)
        (out.write 0 mem outOffset.toNat (min outSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat inSize.toNat) outOffset.toNat outSize.toNat))
        out σ' k' C' ∧
      out.size < 2 ^ 138 := by
  by_cases hd : I.depth = 1024
  · obtain ⟨k', C', rd⟩ := RD.solcStaticcallDepthLimit h hdec hd hov
    refine ⟨{ evm with substate := (Ethereum.EVM.callSubstate fork evm.accountMap (AccountAddress.ofUInt256 target) evm.substate) }, σ, false,
      ByteArray.empty, k', C', ?_, ⟨hs.world, hs.env, hs.accounts⟩, rd, by decide⟩
    refine ⟨_, hcd, callViaEVM.callNotMade rfl rfl ?_⟩
    intro hn
    exact hn.2 (by rw [hs.env]; exact hd)
  · have hdlt : I.depth.val < 1024 := by
      have hb := I.depth.isLt
      have hn : I.depth.val ≠ 1024 := fun hv => hd (Fin.ext hv)
      omega
    obtain ⟨σ', z, out, A_in, callGas, k', C', ⟨g'', A', hΘ⟩, rd, _⟩ := RD.solcStaticcall h hdec hdlt hov
    have hsize : out.size < 2 ^ 138 :=
      Theta_returnData_size_lt_2pow138_of_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hΘ
        (le_trans (Ethereum.EVM.ByteArray.readWithPadding_size_le mem inOffset.toNat inSize.toNat)
          (le_trans hsmall Ethereum.EVM.pow_two_64_le_maxReturnDataSizeByGas))
    rw [hs.accounts, ← hs.world, ← hs.env] at hΘ
    have hΘ' : (σ', g'', A', z, out) =
        Ethereum.EVM.Θ fork evm.accountMap evm.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat evm.executionEnv.codeOwner)) evm.executionEnv.sender
          (AccountAddress.ofUInt256 target) (toExecute fork evm.accountMap (AccountAddress.ofUInt256 target))
          callGas (UInt256.ofNat evm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          (mem.readWithPadding inOffset.toNat inSize.toNat) (evm.executionEnv.depth + 1)
          evm.executionEnv.header evm.executionEnv.blobVersionedHashes evm.executionEnv.blocks
          (false && evm.executionEnv.perm) := by
      rw [Bool.false_and]; exact hΘ
    have hcall := callCoincides (cfg := cfg) (name := name) (args := args) (callPerm := false)
      (by rw [hs.env]; exact hd) rfl hcd hΘ'
    exact ⟨_, σ', z, out, k', C', hcall, ⟨hs.world, hs.env, rfl⟩, rd, hsize⟩

/-! ## Return decoding (modern mode) -/

/-- The first return word. -/
abbrev retWord (out : ByteArray) : UInt256 := uInt256OfByteArray (out.extract 0 32)

theorem bytesToWord_take32_retWord (out : ByteArray) :
    ABI.bytesToWord ((out.toList.drop 0).take 32) = retWord out := by
  rw [List.drop_zero, bytesToWord_take32_eq_extract0_32]
  exact (uInt256OfByteArray_eq _).symm

theorem decodeReturn_uint256_ok (out : ByteArray) (h32 : 32 ≤ out.size) (hbig : out.size < 2 ^ 255) :
    ABI.decodeReturnValue? abiUInt256 out = some (uint256Value (retWord out)) := by
  have htlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake : (out.toList.take 32).length = 32 := by
    rw [List.length_take, htlen]; omega
  have hword := bytesToWord_take32_retWord out
  rw [List.drop_zero] at hword
  unfold ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (by decide), if_neg (by rw [htlen]; omega),
    decodeScalarWords_uint256_ok htake, hword]

theorem decodeReturn_uint256_short (out : ByteArray) (h : out.size < 32) :
    ABI.decodeReturnValue? abiUInt256 out = none := by
  have htlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  unfold ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (by decide), if_neg (by rw [htlen]; omega),
    decodeScalarWords_uint256_none_short (by rw [htlen]; omega)]

theorem decodeReturn_bool_zero (out : ByteArray) (h32 : 32 ≤ out.size) (hbig : out.size < 2 ^ 255)
    (hw : retWord out = ⟨0⟩) :
    ABI.decodeReturnValue? abiBool out = some (.bool false) := by
  have htlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake : ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, htlen]; omega
  have hword := bytesToWord_take32_retWord out
  unfold ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (by decide), if_neg (by rw [htlen]; omega)]
  simp only [decodeScalarWords?]
  rw [decodeScalarWord_bool_ok_zero (start := 0) htake (by rw [hword]; exact hw)]
  rfl

theorem decodeReturn_bool_one (out : ByteArray) (h32 : 32 ≤ out.size) (hbig : out.size < 2 ^ 255)
    (hw : retWord out = ⟨1⟩) :
    ABI.decodeReturnValue? abiBool out = some (.bool true) := by
  have htlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake : ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, htlen]; omega
  have hword := bytesToWord_take32_retWord out
  unfold ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (by decide), if_neg (by rw [htlen]; omega)]
  simp only [decodeScalarWords?]
  rw [decodeScalarWord_bool_ok_one (start := 0) htake (by rw [hword]; exact hw)]
  rfl

theorem decodeReturn_bool_noncanon (out : ByteArray) (h32 : 32 ≤ out.size) (hbig : out.size < 2 ^ 255)
    (hnz : retWord out ≠ ⟨0⟩) (hno : retWord out ≠ ⟨1⟩) :
    ABI.decodeReturnValue? abiBool out = none := by
  have htlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake : ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, htlen]; omega
  have hword := bytesToWord_take32_retWord out
  unfold ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (by decide), if_neg (by rw [htlen]; omega)]
  simp only [decodeScalarWords?]
  rw [decodeScalarWord_bool_none_noncanon (start := 0) htake (by rw [hword]; exact hnz) (by rw [hword]; exact hno)]
  rfl

theorem decodeReturn_bool_short (out : ByteArray) (h : out.size < 32) :
    ABI.decodeReturnValue? abiBool out = none := by
  have htlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  unfold ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (by decide), if_neg (by rw [htlen]; omega)]
  simp only [decodeScalarWords?]
  rw [decodeScalarWord_bool_none_short (start := 0) (by rw [List.drop_zero, List.length_take, htlen]; omega)]
  rfl

/-! ## The output buffer -/

theorem retWord_toByteArray (out : ByteArray) (h32 : 32 ≤ out.size) :
    (retWord out).toByteArray = out.extract 0 32 :=
  toByteArray_uInt256OfByteArray_of_size32 (by rw [ByteArray.size_extract]; omega)

/-- Writing a 32-byte return into memory (in bounds) is writing its first word. -/
theorem write_out_eq_word (out mem : ByteArray) (off : Nat) (h32 : 32 ≤ out.size) (hin : off + 32 ≤ mem.size) :
    out.write 0 mem off 32 = (retWord out).toByteArray.write 0 mem off 32 := by
  rw [write_eq_gen _ _ _ _ (by decide) h32 hin, write_eq_gen _ _ _ _ (by decide) (by rw [toByteArray_size]) hin,
    retWord_toByteArray out h32]
  have hsz : (out.extract 0 32).size = 32 := by rw [ByteArray.size_extract]; omega
  have h2 : (out.extract 0 32).extract 0 32 = out.extract 0 32 := by
    have := byteArray_extract_self (out.extract 0 32)
    rw [hsz] at this
    exact this
  rw [h2]

/-- A call with no output buffer leaves memory unchanged. -/
theorem write_out_zero (out mem : ByteArray) (off : Nat) :
    out.write 0 mem off (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = mem := by
  have hmin : min (⟨0⟩ : UInt256) (UInt256.ofNat out.size) = ⟨0⟩ := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat out.size := by
      change (0 : Nat) ≤ _
      omega
    simp [min, hle]
  rw [hmin]
  exact byteArray_write_len_zero _ _ _ _

/-- The output-buffer length the opcode writes, for a return of at least a word. -/
theorem min32_toNat (n : Nat) (h1 : 32 ≤ n) (h2 : n < UInt256.size) :
    (min (UInt256.ofNat 32) (UInt256.ofNat n)).toNat = 32 := by
  rw [show UInt256.ofNat 32 = (⟨32⟩ : UInt256) from by decide]
  exact u256_min32_ofNat_toNat_of_ge32 n h1 h2

/-- The typed call's target, as the `externalCall` rule spells it. -/
theorem ofUInt256_ofNat_eq_address (a : AccountAddress) :
    AccountAddress.ofUInt256 (UInt256.ofNat a.val) = EVM.address a.val := by
  rw [accountAddress_roundtrip]
  apply Fin.ext
  change a.val = a.val % AccountAddress.size
  exact (Nat.mod_eq_of_lt a.isLt).symm

/-! ## Vyper's multiplication check: `iszero(or(eq(div(mul(x, y), y), x), iszero(y)))` -/

theorem mulCheck_ok (x y : UInt256) (hfit : x.toNat * y.toNat < UInt256.size) :
    UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.div (UInt256.mul x y) y) x) (UInt256.isZero y)) = ⟨0⟩ := by
  by_cases hy : y = ⟨0⟩
  · subst hy
    rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide]
    exact isZero_eq_zero_of_ne (u256_lor_ne_zero_right (by decide))
  · rw [u256_mul_div_right_eq_of_noOverflow x y hy hfit, u256_eq_refl]
    exact isZero_eq_zero_of_ne (by rw [u256_lor_comm]; exact u256_lor_ne_zero_right (by decide))

theorem mulCheck_overflow (x y : UInt256) (hover : UInt256.size ≤ x.toNat * y.toNat) :
    UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.div (UInt256.mul x y) y) x) (UInt256.isZero y)) ≠ ⟨0⟩ := by
  have hy : y ≠ ⟨0⟩ := by
    intro h
    subst h
    have : x.toNat * (⟨0⟩ : UInt256).toNat = 0 := by rfl
    rw [this] at hover
    exact absurd hover (by decide)
  rw [u256_eq_of_ne (u256_mul_div_right_overflow_ne x y hover), isZero_eq_zero_of_ne hy, u256_lor_zero]
  decide

/-- A word read from memory, given the bytes it reads. -/
theorem memLoad_of_read (mem : ByteArray) (off : Nat) (w : UInt256) (hoff : off < UInt256.size)
    (hsz : off < mem.size) (hread : mem.readWithPadding off 32 = w.toByteArray) :
    memLoad (UInt256.ofNat off) mem = w := by
  unfold memLoad
  rw [ulit_toNat' off hoff, if_neg (by omega), hread, fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

/-! ## Vyper's `returndatasize` check: `gt(b + 32, b + min(returndatasize, 32))` -/

/-- `min(n, 32)` as Vyper computes it: `xor(mul(lt(32, n), xor(n, 32)), n)`. -/
theorem vyperMin32 (n : Nat) (hn : n < UInt256.size) :
    UInt256.xor (UInt256.mul (UInt256.lt (UInt256.ofNat 32) (UInt256.ofNat n))
      (UInt256.xor (UInt256.ofNat n) (UInt256.ofNat 32))) (UInt256.ofNat n) = UInt256.ofNat (min n 32) := by
  by_cases h : 32 < n
  · rw [ult_one (by rw [ulit_toNat' 32 (by decide), ulit_toNat' n hn]; exact h), u256_one_mul, u256_xor_xor_cancel,
      Nat.min_eq_right (by omega)]
  · rw [ult_zero (by rw [ulit_toNat' 32 (by decide), ulit_toNat' n hn]; omega), u256_mul_zero_left, u256_zero_xor,
      Nat.min_eq_left (by omega)]

theorem rdsCheck_short (b c n : Nat) (hc : c = b + 32) (hb : b + 32 < UInt256.size) (hn : n < 32) :
    UInt256.gt (UInt256.ofNat c) (UInt256.ofNat b +
      UInt256.xor (UInt256.mul (UInt256.lt (UInt256.ofNat 32) (UInt256.ofNat n))
        (UInt256.xor (UInt256.ofNat n) (UInt256.ofNat 32))) (UInt256.ofNat n)) ≠ UInt256.ofNat 0 := by
  subst hc
  rw [vyperMin32 n (by omega), Nat.min_eq_left (by omega),
    ugt_one (by
      rw [uadd_toNat, ulit_toNat' b (by omega), ulit_toNat' n (by omega), Nat.mod_eq_of_lt (by omega),
        ulit_toNat' (b + 32) hb]
      omega)]
  decide

theorem rdsCheck_ok (b c n : Nat) (hc : c = b + 32) (hb : b + 32 < UInt256.size) (hn : 32 ≤ n) (hn' : n < UInt256.size) :
    UInt256.gt (UInt256.ofNat c) (UInt256.ofNat b +
      UInt256.xor (UInt256.mul (UInt256.lt (UInt256.ofNat 32) (UInt256.ofNat n))
        (UInt256.xor (UInt256.ofNat n) (UInt256.ofNat 32))) (UInt256.ofNat n)) = UInt256.ofNat 0 := by
  subst hc
  rw [vyperMin32 n hn', Nat.min_eq_right hn]
  exact ugt_zero (by
    rw [uadd_toNat, ulit_toNat' b (by omega), ulit_toNat' 32 (by decide), Nat.mod_eq_of_lt (by omega),
      ulit_toNat' (b + 32) hb])

end Reasoning.VyperCalls
