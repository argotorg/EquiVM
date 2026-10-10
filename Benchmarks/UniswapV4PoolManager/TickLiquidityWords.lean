import Benchmarks.UniswapV4PoolManager.WordSar
import Benchmarks.UniswapV4PoolManager.Signed128
import Benchmarks.UniswapV4PoolManager.SignedRangeSource
import Benchmarks.UniswapV4PoolManager.WordFieldPacking

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def tickGrossWord (packed : UInt256) : UInt256 := UInt256.land packed ⟨2^128-1⟩
def tickNetWord (packed : UInt256) : UInt256 := UInt256.sar ⟨128⟩ packed

theorem tickGrossWord_bound (packed : UInt256) : (tickGrossWord packed).toNat < 2^128 :=
  u256LandMaskToNatLtOfToNat packed _ rfl

theorem tickNetWord_fits (packed : UInt256) : signedFits ⟨128, by decide⟩ (EVM.signed (tickNetWord packed)) := by
  change signedFits ⟨128, by decide⟩ (EVM.signed (UInt256.sar (UInt256.ofNat 128) packed))
  rw [wordSarSigned packed (by decide)]
  have hw : packed.toNat < 2^256 := packed.val.isLt
  simp only [signedFits, EVM.signed, EVM.signBit, EVM.wordModulus, EVM.twoPow,
    Int.ofNat_eq_natCast, Int.natCast_pow, Int.cast_ofNat_Int, UInt256.toNat] at *
  split <;> omega

-- LIBRARY CANDIDATE: the high half of a packed word is its arithmetic right shift.
theorem normalizeHighInt128Word (w : UInt256) :
    normalizeInt (.sint ⟨128, by decide⟩)
      (Int.ofNat (UInt256.shiftRight w (UInt256.ofNat 128)).toNat) =
      EVM.signed (UInt256.sar (UInt256.ofNat 128) w) := by
  rw [wordShiftRightNat w (by decide), wordSarSigned w (by decide)]
  have hw : w.toNat < 2^256 := w.val.isLt
  simp only [normalizeInt, EVM.signed, EVM.signBit, EVM.wordModulus, EVM.twoPow,
    Int.ofNat_eq_natCast, Int.natCast_ediv, Int.natCast_pow, Int.cast_ofNat_Int, UInt256.toNat] at *
  split <;> split <;> omega

theorem tickGross_eval {cfg : Config} {f : Frame} {evm : EVM.State} {e : Expr} {packed : UInt256}
    (he : evalExpr? cfg f evm e = .ok (.int (Int.ofNat packed.toNat))) :
    evalExpr? cfg f evm (.cast e (.elem (.int (.uint ⟨128, by decide⟩)))) =
      .ok (.int (Int.ofNat (tickGrossWord packed).toNat)) := by
  simpa only [normalizeUintWord ⟨128, by decide⟩ packed ⟨2^128-1⟩ rfl] using
    evalExpr_cast_int (intType := .uint ⟨128, by decide⟩) he

theorem tickNet_eval {cfg : Config} {f : Frame} {evm : EVM.State} {e : Expr} {packed : UInt256}
    (he : evalExpr? cfg f evm e = .ok (.int (Int.ofNat packed.toNat))) :
    evalExpr? cfg f evm (.cast (.binary (.shr (.uint ⟨256, by decide⟩)) e (.intLit 128))
      (.elem (.int (.sint ⟨128, by decide⟩)))) = .ok (.int (EVM.signed (tickNetWord packed))) := by
  have hs := evalWordShr (n := 128) (by decide) he
    (show evalExpr? cfg f evm (.intLit 128) = .ok (.int (Int.ofNat 128)) by
      simp only [evalExpr?, pure]; rfl)
  simpa only [normalizeHighInt128Word] using evalExpr_cast_int (intType := .sint ⟨128, by decide⟩) hs

def tickNetAfter (packed : UInt256) (delta : Int) (upper : Bool) : Int :=
  if upper then EVM.signed (tickNetWord packed)-delta else EVM.signed (tickNetWord packed)+delta
def tickLiquidityPacked (gross net : UInt256) : UInt256 :=
  UInt256.lor gross (UInt256.shiftLeft net ⟨128⟩)

theorem tickNetAfter_eval {cfg : Config} {f : Frame} {evm : EVM.State}
    {eb ed eu : Expr} {packed : UInt256} {delta : Int} {upper : Bool}
    (hb : evalExpr? cfg f evm eb = .ok (.int (EVM.signed (tickNetWord packed))))
    (hd : evalExpr? cfg f evm ed = .ok (.int delta)) (hu : evalExpr? cfg f evm eu = .ok (.bool upper)) :
    evalExpr? cfg f evm (.ite eu (.inRange (.sint ⟨128, by decide⟩) (.binary .sub eb ed))
      (.inRange (.sint ⟨128, by decide⟩) (.binary .add eb ed))) =
      if signedFits ⟨128, by decide⟩ (tickNetAfter packed delta upper) then
        .ok (.int (tickNetAfter packed delta upper)) else .revert := by
  have hsub : evalExpr? cfg f evm (.binary .sub eb ed) =
      .ok (.int (EVM.signed (tickNetWord packed)-delta)) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), hb, hd]; rfl
  have hadd : evalExpr? cfg f evm (.binary .add eb ed) =
      .ok (.int (EVM.signed (tickNetWord packed)+delta)) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), hb, hd]; rfl
  rw [evalExpr?, hu]
  cases upper
  · exact evalSignedRange ⟨128, by decide⟩ hadd
  · exact evalSignedRange ⟨128, by decide⟩ hsub

theorem tickLiquidityPacked_eval {cfg : Config} {f : Frame} {evm : EVM.State}
    {eg en : Expr} {gross net : UInt256}
    (hg : evalExpr? cfg f evm eg = .ok (.int (Int.ofNat gross.toNat)))
    (hn : evalExpr? cfg f evm en = .ok (.int (EVM.signed net))) :
    evalExpr? cfg f evm (.binary (.bitOr (.uint ⟨256, by decide⟩))
      (.cast eg (.elem (.int (.uint ⟨256, by decide⟩))))
      (.binary (.shl (.uint ⟨256, by decide⟩))
        (.cast (.cast en (.elem (.int (.uint ⟨128, by decide⟩)))) (.elem (.int (.uint ⟨256, by decide⟩))))
        (.intLit 128))) = .ok (.int (Int.ofNat (tickLiquidityPacked gross net).toNat)) := by
  have hg' := evalExpr_cast_int (intType := .uint ⟨256, by decide⟩) hg
  rw [normalizeInt_uint256_word] at hg'
  have hn' := evalExpr_cast_int (intType := .uint ⟨256, by decide⟩)
    (evalExpr_cast_int (intType := .uint ⟨128, by decide⟩) hn)
  rw [normalizeUintSignedWord ⟨128, by decide⟩ net ⟨2^128-1⟩ rfl, normalizeInt_uint256_word] at hn'
  have he := evalWordOr hg' (evalWordShl (n := 128) (by decide) hn'
    (show evalExpr? cfg f evm (.intLit 128) = .ok (.int (Int.ofNat 128)) by simp only [evalExpr?, pure]; rfl))
  simpa only [wordShiftLowMask net ⟨2^128-1⟩ (n := 128) (by decide) rfl] using he

end Benchmarks.UniswapV4PoolManager
