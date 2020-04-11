module net.cruhland.axiomatic.Peano where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

record Peano (ℕ : Set) : Set₁ where
  field
    zero : ℕ
    succ : ℕ → ℕ

    succ≢zero : ∀ {n} → succ n ≢ zero
    succ-inj : ∀ {n m} → succ n ≡ succ m → n ≡ m
    ind : (P : ℕ → Set) → P zero → (∀ {k} → P k → P (succ k)) → ∀ n → P n

record PeanoBundle : Set₁ where
  field
    ℕ : Set
    isPeano : Peano ℕ

  open Peano isPeano public
