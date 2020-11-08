-- Needed for positive integer literals (typeclass)
import Agda.Builtin.FromNat
open import Function using (_∘_)
open import Relation.Nullary.Decidable using (False)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast as Cast using (_As_)
open import net.cruhland.axioms.DecEq using (_≃?_; ≄-derive)
open import net.cruhland.axioms.Eq using (_≄_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
-- Needed for positive integer literals (instance for ⊤)
import net.cruhland.models.Logic

module net.cruhland.models.Rationals.Base (PA : PeanoArithmetic) where

private module ℕ = PeanoArithmetic PA
open ℕ using (ℕ)
import net.cruhland.models.Integers PA as ℤ
open ℤ using (ℤ; ≃ᶻ-intro)

record ℚ : Set where
  field
    n d : ℤ
    d≄0 : d ≄ 0

infixl 8 _//_
_//_ : (n d : ℤ) {{_ : False (d ≃? 0)}} → ℚ
n // d = record { n = n ; d = d ; d≄0 = ≄-derive }

_//1 : ℤ → ℚ
a //1 = record { n = a ; d = 1 ; d≄0 = ℕ.step≄zero ∘ AA.inject }

instance
  from-ℤ : ℤ As ℚ
  from-ℤ = record { cast = _//1 }

  from-ℕ : ℕ As ℚ
  from-ℕ = Cast.transitive {B = ℤ}
