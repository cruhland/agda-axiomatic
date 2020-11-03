-- Needed for positive integer literals (typeclass)
import Agda.Builtin.FromNat as FromNat
open import Relation.Nullary.Decidable using (False)
open import net.cruhland.axioms.DecEq using (_≃?_; ≄-derive)
open import net.cruhland.axioms.Eq using (_≄_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
-- Needed for positive integer literals (instance for ⊤)
open import net.cruhland.models.Logic using ()

module net.cruhland.models.Rationals.Base (PA : PeanoArithmetic) where

import net.cruhland.models.Integers PA as ℤ
open ℤ using (ℤ)

record ℚ : Set where
  field
    n d : ℤ
    d≄0 : d ≄ 0

infixl 8 _//_
_//_ : (n d : ℤ) {{_ : False (d ≃? 0)}} → ℚ
n // d = record { n = n ; d = d ; d≄0 = ≄-derive }
