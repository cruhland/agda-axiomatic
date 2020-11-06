open import net.cruhland.axioms.Operators as Op using (-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Rationals.Negation (PA : PeanoArithmetic) where

import net.cruhland.models.Integers PA as ℤ
open import net.cruhland.models.Rationals.Base PA using (ℚ)

instance
  dashᴸ : Op.Dashᴸ ℚ
  dashᴸ = record { -_ = -₀_ }
    where
      -₀_ : ℚ → ℚ
      -₀ record { n = p↑ ; d = p↓ ; d≄0 = p↓≄0 } =
        record { n = - p↑ ; d = p↓ ; d≄0 = p↓≄0 }
