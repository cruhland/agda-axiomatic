module net.cruhland.axiomatic.Peano where

open import Agda.Builtin.FromNat using (Number)
import Agda.Builtin.Nat as Nat
open import Data.Unit using (⊤)
open import Function using (const)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

record Peano (ℕ : Set) : Set₁ where
  field
    zero : ℕ
    succ : ℕ → ℕ

    succ≢zero : ∀ {n} → succ n ≢ zero
    succ-inj : ∀ {n m} → succ n ≡ succ m → n ≡ m
    ind : (P : ℕ → Set) → P zero → (∀ {k} → P k → P (succ k)) → ∀ n → P n

module _ {ℕ : Set} {{P : Peano ℕ}} where
  open Peano P

  fromNat : Nat.Nat → {{_ : ⊤}} → ℕ
  fromNat Nat.zero = zero
  fromNat (Nat.suc n) = succ (fromNat n)

  instance
    number : Number ℕ
    number = record { Constraint = const ⊤ ; fromNat = fromNat }
