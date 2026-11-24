import Benchmarks.EAS.Attester.Immutables
import Reasoning.Listing.FromHex

/-! `Attester`'s runtime bytecode as a table of sections, the check tying the table to the
bytes, and what the check gives (`Reasoning/Listing/Sound.lean`) for the code the block
summaries are stated over: the template (`runtime.hex` with the sites of `immutableLayout`
zeroed) with the immutables written in.  The listing is computed from `runtime.hex` when this
file is elaborated (`Reasoning/Listing/FromHex.lean`); `#print_listing
Benchmarks.EAS.Attester.Listing.table` shows it. -/

namespace Benchmarks.EAS.Attester.Listing

listing_from_hex "runtime.hex" sha256 "e89d3390ab72057de9f08cc051bffcdbe7ee59b66f46ec1edfaf495ccf3ae731"
  bytecode Benchmarks.EAS.Attester.attesterBytecode
  layout Benchmarks.EAS.Attester.Immutables.immutableLayout blocks attesterRuntimeBlocks

end Benchmarks.EAS.Attester.Listing
