import DisjointnessFoundations.UpdatePrefixAccounting

namespace DisjointnessFoundations.HardProtocol

/-- The hard history inserts the longest epoch first. -/
def order (ℓ : ℕ) : List (Fin ℓ) := (List.finRange ℓ).reverse

end DisjointnessFoundations.HardProtocol
