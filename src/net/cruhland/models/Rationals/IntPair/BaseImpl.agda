open import net.cruhland.axioms.Cast using (_As_; As-intro)
open import net.cruhland.axioms.Eq using (_≄ⁱ_)
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.models.Rationals.IntPair.BaseImpl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open Integers Z using (ℤ)

record ℚ : Set where
  constructor _//_
  field
    numerator denominator : ℤ
    {{denominator≄ⁱ0}} : denominator ≄ⁱ 0

instance
  from-ℤ : ℤ As ℚ
  from-ℤ = As-intro (_// 1)
