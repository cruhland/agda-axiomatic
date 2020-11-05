import net.cruhland.axioms.AbstractAlgebra as AA
import net.cruhland.axioms.Operators as Op
open Op using (_*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Rationals.Multiplication (PA : PeanoArithmetic) where

import net.cruhland.models.Integers PA as ℤ
open import net.cruhland.models.Rationals.Base PA using (ℚ)

instance
  star : Op.Star ℚ
  star = record { _*_ = _*₀_ }
    where
      _*₀_ : ℚ → ℚ → ℚ
      record { n = p↑ ; d = p↓ ; d≄0 = p↓≄0 } *₀
        record { n = q↑ ; d = q↓ ; d≄0 = q↓≄0 } =
          record
            { n = p↑ * q↑
            ; d = p↓ * q↓
            ; d≄0 = AA.nonzero-prod p↓≄0 q↓≄0
            }
