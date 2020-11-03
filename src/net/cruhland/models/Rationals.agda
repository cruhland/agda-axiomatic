-- Needed for positive integer literals (typeclass)
import Agda.Builtin.FromNat as FromNat
open import net.cruhland.axioms.Eq using (_≄ⁱ_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
-- Needed for positive integer literals (instance for ⊤)
open import net.cruhland.models.Logic using ()

module net.cruhland.models.Rationals (PA : PeanoArithmetic) where

import net.cruhland.models.Integers PA as ℤ
open ℤ using (ℤ)

infixl 8 _//_
record ℚ : Set where
  constructor _//_
  field
    n d : ℤ
    {{d≄ⁱ0}} : d ≄ⁱ 0
