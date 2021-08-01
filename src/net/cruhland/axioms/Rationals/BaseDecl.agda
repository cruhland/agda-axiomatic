import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_As_; _as_)
open import net.cruhland.axioms.DecEq using (DecEq)
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Rationals.BaseDecl
  (PA : PeanoArithmetic) (Z : Integers PA) where

private open module ℤ = Integers Z using (ℤ)

record Base : Set₁ where
  field
    ℚ : Set
    {{decEq}} : DecEq ℚ
    {{from-ℤ}} : ℤ As ℚ
    {{from-ℤ-substitutive}} : AA.Substitutive₁ {A = ℤ} (_as ℚ) _≃_ _≃_
    {{from-ℤ-injective}} : AA.Injective {A = ℤ} (_as ℚ) _≃_ _≃_
