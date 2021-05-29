open import Relation.Nullary.Decidable using (False)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast as Cast using (_As_; As-intro)
open import net.cruhland.axioms.DecEq using (_≃?_; ≄-derive)
open import net.cruhland.axioms.Eq using (_≄_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Function using (_∘_)
open import net.cruhland.models.Literals

module net.cruhland.models.Rationals.Base (PA : PeanoArithmetic) where

private module ℕ = PeanoArithmetic PA
open ℕ using (ℕ)
import net.cruhland.models.Integers PA as ℤ
open ℤ using (ℤ; ≃ᶻ-intro)

infixl 8 _//_ _//_~_

record ℚ : Set where
  constructor _//_~_
  field
    n d : ℤ
    d≄0 : d ≄ 0

_//_ : (n d : ℤ) {{_ : False (d ≃? 0)}} → ℚ
n // d = n // d ~ ≄-derive

_//1 : ℤ → ℚ
a //1 = a // 1 ~ ℕ.step≄zero ∘ AA.inject

instance
  from-ℤ : ℤ As ℚ
  from-ℤ = As-intro _//1

  from-ℕ : ℕ As ℚ
  from-ℕ = Cast.via ℤ

  from-Nat : Nat As ℚ
  from-Nat = Cast.via ℕ

  from-literal : FromNatLiteral ℚ
  from-literal = nat-literal-from-cast
