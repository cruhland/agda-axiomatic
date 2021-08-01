import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_As_; As-intro)
open import net.cruhland.axioms.DecEq using (_≃?_; ≄-derive)
open import net.cruhland.axioms.Eq using (_≄_)
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Function using (_∘_)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (False)

module net.cruhland.models.Rationals.Base
  (PA : PeanoArithmetic) (Z : Integers PA) where

private open module ℕ = PeanoArithmetic PA using (ℕ)
private open module ℤ = Integers Z using (ℤ)

infixl 8 _//_ _//_~_

record ℚ : Set where
  constructor _//_~_
  field
    n d : ℤ
    d≄0 : d ≄ 0

_//_ : (n d : ℤ) {{_ : False (d ≃? 0)}} → ℚ
n // d = n // d ~ ≄-derive

_//1 : ℤ → ℚ
a //1 = a // 1 ~ ℤ.1≄0

instance
  from-ℤ : ℤ As ℚ
  from-ℤ = As-intro _//1

  from-literal : FromNatLiteral ℚ
  from-literal = nat-literal-via ℤ
