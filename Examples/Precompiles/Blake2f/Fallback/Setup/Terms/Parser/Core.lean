import Examples.Precompiles.Blake2f.Fallback.Setup.Terms.Defs

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-! ## Parser-array memory helpers

Source note: the Solidity compiler zero-initializes fixed-size memory arrays with
`CALLDATACOPY(dst, calldatasize(), len)`.  The EVM active-memory word count expands for the full
requested destination window, but the concrete `ByteArray.write` used by the semantics only stores
bytes that are physically present.  For the length-213 calldata accepted by EIP-152, these zeroing
copies therefore do not extend the concrete bytearray past the already materialized `msg.data`
buffer.  The following local lemmas record exactly the free-pointer readbacks needed by the next
allocation helpers without adding global special cases to `Reasoning/Memory.lean`. -/

theorem copySlice_read_below_gen (src base : ByteArray)
    (srcAddr destAddr written readAddr len : Nat)
    (hbelow : readAddr + len ≤ destAddr)
    (hreadIn : readAddr + len ≤ base.size)
    (hpos : 0 < len)
    (hlen64 : len < 2 ^ 64) :
    (src.copySlice srcAddr base destAddr written).readWithPadding readAddr len =
      base.readWithPadding readAddr len := by
  have hpre : (base.extract 0 destAddr).size = min destAddr base.size := by
    rw [ByteArray.size_extract]
    omega
  have hpreFull : readAddr + len ≤ (base.extract 0 destAddr).size := by
    rw [hpre]
    omega
  have hresultIn : readAddr + len ≤ (src.copySlice srcAddr base destAddr written).size := by
    rw [ByteArray.copySlice_eq_append, ByteArray.size_append, ByteArray.size_append]
    rw [hpre]
    omega
  rw [readWithPadding_eq_extract' _ readAddr len hpos hlen64 hresultIn]
  rw [ByteArray.copySlice_eq_append]
  rw [extract_append_left _ _ _ _ (by rw [ByteArray.size_append, hpre]; omega)]
  rw [extract_append_left _ _ _ _ hpreFull]
  rw [extract_prefix _ destAddr readAddr (readAddr + len) hbelow]
  exact (readWithPadding_eq_extract' base readAddr len hpos hlen64 hreadIn).symm

end Blake2f
