import Reasoning.Solc
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair

-- LIBRARY CANDIDATE: equality of canonical address words is reflected by address conversion.
theorem accountAddress_ofUInt256_eq_iff_of_canonical {a b : UInt256}
    (ha : a.toNat < EVM.addressModulus) (hb : b.toNat < EVM.addressModulus) :
    AccountAddress.ofUInt256 a = AccountAddress.ofUInt256 b ↔ a = b := by
  have ha' : a.toNat < AccountAddress.size := ha
  have hb' : b.toNat < AccountAddress.size := hb
  constructor
  · intro h
    apply u256_inj
    have hv := congrArg Fin.val h
    simpa only [accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat,
      Fin.val_ofNat, Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] using hv
  · intro h; rw [h]

end UniswapV2Pair
