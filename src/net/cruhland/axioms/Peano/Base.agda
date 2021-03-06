module net.cruhland.axioms.Peano.Base where

import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq using (_≃_; _≄_; Eq)

record Peano : Set₁ where
  field
    ℕ : Set
    zero : ℕ
    step : ℕ → ℕ
    {{eq}} : Eq ℕ
    {{step-substitutive}} : AA.Substitutive₁ step _≃_ _≃_
    {{step-injective}} : AA.Injective step _≃_ _≃_
    step≄zero : ∀ {n} → step n ≄ zero

  step-case : (P : ℕ → Set) → Set
  step-case P = ∀ {k} → P k → P (step k)

  field
    ind : (P : ℕ → Set) → P zero → step-case P → ∀ n → P n
