import Benchmarks.CompoundIII.Comet.TypedBits

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def bitMembership (value : UInt256) (bit : Nat) : Bool :=
  decide (Nat.land value.toNat (2^bit) ≠ 0)

def isInAssetBool (assets offset reserved : UInt256) : Bool :=
  if offset.toNat < 16 then bitMembership assets offset.toNat
  else if offset.toNat < 24 then bitMembership reserved (offset.toNat - 16) else false

def bitMembershipExpr (width : BitWidth) (value bit : Expr) : Expr :=
  .binary .ne (.binary (.bitAnd (.uint width)) value
    (.binary (.shl (.uint width))
      (.cast (.intLit 1) (.elem (.int (.uint width)))) bit)) (.intLit 0)

def isInAssetOffsetExpr : Expr :=
  .inRange (.uint ⟨8, by decide⟩) (.binary .sub (.var "assetOffset") (.intLit 16))

def isInAssetCallable : CallableDecl :=
  { params := [⟨"assetsIn", .elem (.int (.uint ⟨16, by decide⟩))⟩,
      ⟨"assetOffset", .elem (.int (.uint ⟨8, by decide⟩))⟩,
      ⟨"_reserved", .elem (.int (.uint ⟨8, by decide⟩))⟩]
    returnType := [.elem .bool]
    body := [.ite (.binary .lt (.var "assetOffset") (.intLit 16))
      [.return [bitMembershipExpr ⟨16, by decide⟩ (.var "assetsIn") (.var "assetOffset")]]
      [.ite (.binary .lt (.var "assetOffset") (.intLit 24))
        [.return [bitMembershipExpr ⟨8, by decide⟩ (.var "_reserved") isInAssetOffsetExpr]] []],
      .return [.boolLit false]] }

theorem isInAssetCallable_lookup : lookupCallable? contract "isInAsset" =
    some isInAssetCallable := rfl

def isInAssetEntry (imms : Store) (assets offset reserved : UInt256) : Frame :=
  { contract := contract, immutables := imms,
    locals := ((∅ : Store).insert "_reserved" (.int reserved.toNat)).insert
      "assetOffset" (.int offset.toNat) |>.insert "assetsIn" (.int assets.toNat) }

-- LIBRARY CANDIDATE: testing a typed bit mask agrees with the corresponding natural AND.
theorem bitMembership_source {cfg frame evm valueExpr bitExpr} (width : BitWidth)
    (value : UInt256) (bit : Nat) (hv : value.toNat < 2^width.val) (hb : bit < width.val)
    (he : evalExpr? cfg frame evm valueExpr = .ok (.int value.toNat))
    (hbit : evalExpr? cfg frame evm bitExpr = .ok (.int (Int.ofNat bit))) :
    evalExpr? cfg frame evm (bitMembershipExpr width valueExpr bitExpr) =
      .ok (.bool (bitMembership value bit)) := by
  have hm := evalUintBitMask width bit hb hbit
  have ha := evalUintAndNat width value.toNat (2^bit) hv
    (Nat.pow_lt_pow_right (by decide) hb)
  simp only [Int.ofNat_eq_natCast] at hm ha
  simp only [bitMembershipExpr, evalExpr?, he, hm, pure, bind, EvalResult.bind,
    evalBinaryOp?, ha]
  apply congrArg EvalResult.ok
  apply congrArg Value.bool
  apply Bool.eq_iff_iff.mpr
  simp [bitMembership]

end Benchmarks.CompoundIII.Comet
