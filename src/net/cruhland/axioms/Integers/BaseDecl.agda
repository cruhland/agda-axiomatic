import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_As_; _as_; _value_)
open import net.cruhland.axioms.DecEq using (DecEq)
open import net.cruhland.axioms.Eq using (_≃_; _≄_; _≄ⁱ_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Integers.BaseDecl (PA : PeanoArithmetic) where

private open module ℕ = PeanoArithmetic PA using (ℕ)

record Base : Set₁ where
  field
    ℤ : Set
    {{dec-eq}} : DecEq ℤ
    {{from-ℕ}} : ℕ As ℤ
    {{from-ℕ-substitutive}} : AA.Substitutive₁ {A = ℕ} (_as ℤ) _≃_ _≃_
    {{from-ℕ-injective}} : AA.Injective {A = ℕ} (_as ℤ) _≃_ _≃_

    {{nat-literal}} : FromNatLiteral ℤ
    fromNatLiteral≃casts : ∀ n → fromNatLiteral n ≃ (n as ℕ as ℤ)
    1≄0 : (ℤ value 1) ≄ 0
    {{1≄ⁱ0}} : (ℤ value 1) ≄ⁱ 0
