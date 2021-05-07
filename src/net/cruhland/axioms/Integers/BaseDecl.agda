import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_As_; _as_)
open import net.cruhland.axioms.Eq using (_≃_; Eq)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Integers.BaseDecl (PA : PeanoArithmetic) where

open PeanoArithmetic PA using (ℕ)

record Base : Set₁ where
  field
    ℤ : Set
    {{eq}} : Eq ℤ
    {{from-ℕ}} : ℕ As ℤ
    {{from-ℕ-substitutive}} : AA.Substitutive₁ {A = ℕ} (_as ℤ) _≃_ _≃_
    {{from-ℕ-injective}} : AA.Injective {A = ℕ} (_as ℤ) _≃_ _≃_
