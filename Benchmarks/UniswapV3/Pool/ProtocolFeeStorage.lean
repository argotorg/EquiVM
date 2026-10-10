import Benchmarks.UniswapV3.Pool.PackedStorage
import Benchmarks.UniswapV3.Pool.Routines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem solcShift128 : UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128) =
    UInt256.ofNat (2 ^ 128) := by native_decide

def uint128Word (value : UInt256) : UInt256 :=
  UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) value

theorem uint128Word_toNat (value : UInt256) :
    (uint128Word value).toNat = value.toNat % 2 ^ 128 := by
  rw [uint128Word, uland_toNat, ulit_toNat' _ (by decide)]
  change Nat.land (2 ^ 128 - 1) value.toNat = _
  rw [nat_land_comm, nat_land_mask_eq_mod]

theorem uint128Word_lt (value : UInt256) : (uint128Word value).toNat < 2 ^ 128 := by
  rw [uint128Word_toNat]
  exact Nat.mod_lt _ (by decide)

theorem uint128Word_clean {value : UInt256} (h : value.toNat < 2 ^ 128) :
    uint128Word value = value := by
  apply u256_inj
  rw [uint128Word_toNat, Nat.mod_eq_of_lt h]

def protocolFeesWord (second : Bool) (σ : AccountMap) (ee : ExecutionEnv) : UInt256 :=
  if second then protocolFeesToken1Word σ ee else protocolFeesToken0Word σ ee

theorem protocolFeesWord_lt (second : Bool) (σ : AccountMap) (ee : ExecutionEnv) :
    (protocolFeesWord second σ ee).toNat < 2 ^ 128 := by
  cases second <;>
    exact u256LandMaskToNatLtOfToNat _ _ (by decide)

def protocolFeeUpdateWord (second : Bool) (old value : UInt256) : UInt256 :=
  if second then
    UInt256.lor (UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) old)
      (UInt256.mul (uint128Word value) (UInt256.ofNat (2 ^ 128)))
  else
    UInt256.lor (uint128Word value)
      (UInt256.land old (UInt256.lnot (UInt256.ofNat (2 ^ 128 - 1))))

theorem protocolFeeUpdateWord_false_toNat (old value : UInt256) :
    (protocolFeeUpdateWord false old value).toNat =
      value.toNat % 2 ^ 128 + old.toNat / 2 ^ 128 * 2 ^ 128 := by
  change (UInt256.lor (uint128Word value) _).toNat = _
  rw [u256_lor_comm]
  have h := packedMaskedWord_toNat old (UInt256.lnot (UInt256.ofNat (2 ^ 128 - 1)))
    (uint128Word value) 0 128 (value.toNat % 2 ^ 128) (by decide) (by decide +kernel)
    (by rw [uint128Word_toNat]; simp) (Nat.mod_lt _ (by decide))
  simpa only [Nat.pow_zero, Nat.mod_one, Nat.mul_one, Nat.zero_add] using h

theorem protocolFeeUpdateWord_true_toNat (old value : UInt256) :
    (protocolFeeUpdateWord true old value).toNat =
      old.toNat % 2 ^ 128 + value.toNat % 2 ^ 128 * 2 ^ 128 := by
  have hv := Nat.mod_lt value.toNat (by decide : 0 < 2 ^ 128)
  have hfield : (UInt256.mul (uint128Word value) (UInt256.ofNat (2 ^ 128))).toNat =
      value.toNat % 2 ^ 128 * 2 ^ 128 := by
    change (uint128Word value * UInt256.ofNat (2 ^ 128)).toNat = _
    have hfit : (uint128Word value).toNat * (UInt256.ofNat (2 ^ 128)).toNat < UInt256.size := by
      rw [uint128Word_toNat, ulit_toNat' _ (by decide)]
      change _ < 2 ^ (128 + 128)
      rw [Nat.pow_add]
      exact Nat.mul_lt_mul_of_pos_right hv (by positivity)
    rw [umul_toNat _ _ hfit, uint128Word_toNat, ulit_toNat' _ (by decide)]
  change (UInt256.lor (uint128Word old)
    (UInt256.mul (uint128Word value) (UInt256.ofNat (2 ^ 128)))).toNat = _
  rw [u256_lor_toNat_exact, uint128Word_toNat, hfield]
  exact nat_lor_shift_add _ _ _ (Nat.mod_lt _ (by decide))

def storeProtocolFee (evm : EVM.State) (second : Bool) (value : UInt256) : EVM.State :=
  EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩
    (protocolFeeUpdateWord second (EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩) value)

-- LIBRARY CANDIDATE: update either half of a pair of uint128 storage fields.
theorem storageLocStore_uint128PairField (evm : EVM.State) (slot : UInt256) (second : Bool) (value : UInt256) :
    storageLocStore evm
      { slot := slot, offset := if second then 16 else 0, size := 16,
        type := .int (.uint ⟨128, by decide⟩), hbound := by cases second <;> decide }
      (.int (Int.ofNat value.toNat)) = some (EVM.storageStore evm evm.executionEnv.codeOwner slot
        (protocolFeeUpdateWord second (EVM.storageLoad evm evm.executionEnv.codeOwner slot) value)) := by
  apply storageLocStore_packed_of_toNat evm _ _ value _
    (by simp only [valueToWord, wordOfInt_ofNat_toNat, pure]) rfl
  cases second
  · rw [protocolFeeUpdateWord_false_toNat]
    simp [Nat.mul_comm]
    exact Nat.mod_one _
  · rw [protocolFeeUpdateWord_true_toNat]
    have hn : (EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat < 2 ^ 256 :=
      (EVM.storageLoad evm evm.executionEnv.codeOwner slot).val.isLt
    norm_num [Nat.mul_comm]
    omega

theorem storageLocStore_protocolFee (evm : EVM.State) (second : Bool) (value : UInt256) :
    storageLocStore evm
      { slot := ⟨3⟩, offset := if second then 16 else 0, size := 16,
        type := .int (.uint ⟨128, by decide⟩), hbound := by cases second <;> decide }
      (.int (Int.ofNat value.toNat)) = some (storeProtocolFee evm second value) :=
  storageLocStore_uint128PairField evm ⟨3⟩ second value

def protocolFeesField (second : Bool) : Ident := if second then "token1" else "token0"

def protocolFeesExpr (second : Bool) : Expr :=
  .storage ⟨"protocolFees", [.field (protocolFeesField second)]⟩

theorem evalProtocolFeesWord (locals imms : Store) (evm : EVM.State) (second : Bool)
    (hbase : locals.get? "protocolFees" = none) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (protocolFeesExpr second) =
      .ok (.int (Int.ofNat (protocolFeesWord second evm.accountMap evm.executionEnv).toNat)) := by
  cases second
  · exact evalProtocolFeesToken0 locals imms evm hbase
  · exact evalProtocolFeesToken1 locals imms evm hbase

theorem assignProtocolFee (evm : EVM.State) (locals imms : Store) (second : Bool) (value : UInt256)
    (hbase : locals.get? "protocolFees" = none) :
    assignStorageRef? config { contract := contract, locals := locals, immutables := imms }
      evm .storage ⟨"protocolFees", [.field (protocolFeesField second)]⟩ (.int (Int.ofNat value.toNat)) =
      .ok ({ contract := contract, locals := locals, immutables := imms },
        storeProtocolFee evm second value) := by
  apply assignStorageRef_storage_scalar_value (ty := .elem (.int (.uint ⟨128, by decide⟩)))
    (er := ⟨"protocolFees", [.field (protocolFeesField second)]⟩)
    (loc := { slot := ⟨3⟩, offset := if second then 16 else 0, size := 16,
              type := .int (.uint ⟨128, by decide⟩), hbound := by cases second <;> decide }) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, EvalResult.bind, bind, pure])
    (by cases second <;> dsimp only <;> decide +kernel) poolStorageBackend_eq
    (by cases second <;> rfl) (Or.inl ⟨_, rfl⟩)
  exact storageLocStore_protocolFee evm second value

theorem storeProtocolFee_accountMap (evm : EVM.State) (second : Bool) (value : UInt256) :
    (storeProtocolFee evm second value).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨3⟩
        (protocolFeeUpdateWord second (solcSlotWordAt ⟨3⟩ evm.accountMap evm.executionEnv) value) := by
  rw [storeProtocolFee, storageStore_accountMap,
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv ⟨3⟩ rfl]

theorem storeProtocolFee_executionEnv (evm : EVM.State) (second : Bool) (value : UInt256) :
    (storeProtocolFee evm second value).executionEnv = evm.executionEnv :=
  storageStore_executionEnv _ _ _ _

-- LIBRARY CANDIDATE: an explicit uint128 subtraction cast is the masked EVM subtraction.
theorem uint128_sub_cast (a b : UInt256) :
    normalizeInt (.uint ⟨128, by decide⟩) (Int.ofNat a.toNat - Int.ofNat b.toNat) =
      Int.ofNat (uint128Word (UInt256.sub a b)).toNat := by
  rw [uint128Word_toNat]
  change (Int.ofNat a.toNat - Int.ofNat b.toNat) % (2 ^ 128 : Int) = _
  by_cases hle : b.toNat ≤ a.toNat
  · rw [usub_toNat hle]
    have hcast : Int.ofNat a.toNat - Int.ofNat b.toNat = Int.ofNat (a.toNat - b.toNat) :=
      (Int.ofNat_sub hle).symm
    rw [hcast]
    rfl
  · have hlt : a.toNat < b.toNat := by omega
    rw [usub_toNat_underflow hlt]
    have hb : b.toNat < 2 ^ 256 := b.val.isLt
    change (Int.ofNat a.toNat - Int.ofNat b.toNat) % (2 ^ 128 : Int) =
      Int.ofNat (2 ^ 256 + a.toNat - b.toNat) % (2 ^ 128 : Int)
    have hcast : Int.ofNat (2 ^ 256 + a.toNat - b.toNat) =
        Int.ofNat a.toNat - Int.ofNat b.toNat + (2 ^ 256 : Int) := by
      simp only [Int.ofNat_eq_natCast]
      omega
    rw [hcast, Int.add_emod, show (2 ^ 256 : Int) % 2 ^ 128 = 0 from by norm_num,
      Int.add_zero, Int.emod_emod]

theorem evalExpr_uint128Sub {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int (Int.ofNat b.toNat))) :
    evalExpr? cfg frame evm (.cast (.binary .sub lhs rhs) (.elem (.int (.uint ⟨128, by decide⟩)))) =
      .ok (.int (Int.ofNat (uint128Word (UInt256.sub a b)).toNat)) := by
  have hsub : evalExpr? cfg frame evm (.binary .sub lhs rhs) =
      .ok (.int (Int.ofNat a.toNat - Int.ofNat b.toNat)) := by
    simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?]
  simpa only [uint128_sub_cast] using evalExpr_intCast (.uint ⟨128, by decide⟩) hsub

end Benchmarks.UniswapV3.Pool
