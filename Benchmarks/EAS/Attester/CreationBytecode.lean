import Reasoning.Listing.FromHex

/-! `Attester`'s creation bytecode as a table of sections, the check tying the table to the
bytes, and what the check gives (`Reasoning/Listing/Sound.lean`) for the code the block
summaries are stated over: the code followed by any `tail` (the constructor arguments).  The
listing is computed from `creation.hex` when this file is elaborated
(`Reasoning/Listing/FromHex.lean`); `#print_listing
Benchmarks.EAS.Attester.CreationListing.table` shows it. -/

namespace Benchmarks.EAS.Attester.CreationListing

listing_from_hex "creation.hex" sha256 "7b1d38f3c940a1f25f63ff820d5b885e0dc941c99b83f8f6474a282f5597b923"
  bytecode Benchmarks.EAS.Attester.attesterCreationBytecode creation followed_by tail

end Benchmarks.EAS.Attester.CreationListing
