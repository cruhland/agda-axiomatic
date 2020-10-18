module net.cruhland.axioms.Peano.Base where

open import net.cruhland.axioms.Eq using (_≃_; _≄_; Eq)

record Peano : Set₁ where
  field
    ℕ : Set
    zero : ℕ
    step : ℕ → ℕ
    {{eq}} : Eq ℕ
    step≄zero : ∀ {n} → step n ≄ zero
    step-subst : ∀ {n m} → n ≃ m → step n ≃ step m
    step-inj : ∀ {n m} → step n ≃ step m → n ≃ m

  open Eq eq using (_≃_) public

  step-case : (P : ℕ → Set) → Set
  step-case P = ∀ {k} → P k → P (step k)

  field
    ind : (P : ℕ → Set) → P zero → step-case P → ∀ n → P n
