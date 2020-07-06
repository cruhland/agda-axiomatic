module net.cruhland.axiomatic.Peano.Base where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

record Peano : Set₁ where
  field
    ℕ : Set
    zero : ℕ
    step : ℕ → ℕ
    step≢zero : ∀ {n} → step n ≢ zero
    step-inj : ∀ {n m} → step n ≡ step m → n ≡ m

  step-case : (P : ℕ → Set) → Set
  step-case P = ∀ {k} → P k → P (step k)

  field
    ind : (P : ℕ → Set) → P zero → step-case P → ∀ n → P n
