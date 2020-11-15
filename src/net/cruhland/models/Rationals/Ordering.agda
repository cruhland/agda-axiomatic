open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Operators using (-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Rationals.Ordering (PA : PeanoArithmetic) where

import net.cruhland.models.Integers PA as ℤ
open import net.cruhland.models.Rationals.Base PA as Base using (ℚ)
import net.cruhland.models.Rationals.Equality PA as Equality
import net.cruhland.models.Rationals.Negation PA as Negation

record Positive (q : ℚ) : Set where
  field
    n-pos : ℤ.Positive (ℚ.n q)
    d-pos : ℤ.Positive (ℚ.d q)

record Negative (q : ℚ) : Set where
  field
    p : ℚ
    p-pos : Positive p
    q≃-p : q ≃ - p
