module net.cruhland.axiomatic.Peano.Base where

open import Function using (const; _∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import net.cruhland.axiomatic.Logic
  using (_∨_; Σ; ∨-introᴸ; ∨-introᴿ; Σ-intro; ∨-forceᴿ; Decidable; ¬sym; ∨-rec)

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
    ind-zero : ∀ {P z} {s : step-case P} → ind P z s zero ≡ z
    ind-step : ∀ {P z n} {s : step-case P} → ind P z s (step n) ≡ s (ind P z s n)

  case : ∀ n → n ≡ zero ∨ Σ ℕ λ p → n ≡ step p
  case n = ind P Pz Ps n
    where
      P = λ x → x ≡ zero ∨ Σ ℕ λ p → x ≡ step p
      Pz = ∨-introᴸ refl

      Ps : step-case P
      Ps {k} _ = ∨-introᴿ (Σ-intro k refl)

  pred : ∀ {n} → n ≢ zero → Σ ℕ λ p → n ≡ step p
  pred {n} n≢z = ∨-forceᴿ n≢z (case n)

  _≡?_ : (n m : ℕ) → Decidable (n ≡ m)
  n ≡? m = ind P Pz Ps n m
    where
      P = λ x → ∀ y → Decidable (x ≡ y)

      Qz = λ y → Decidable (zero ≡ y)
      Qzz = ∨-introᴸ refl

      Qzs : step-case Qz
      Qzs z≡k∨z≢k = ∨-introᴿ (¬sym step≢zero)

      Pz = λ y → ind Qz Qzz Qzs y

      Ps : step-case P
      Ps {k} y→k≡y∨k≢y = ind Qs Qsz Qss
        where
          Qs = λ y → Decidable (step k ≡ y)
          Qsz = ∨-introᴿ step≢zero

          Qss : step-case Qs
          Qss {j} k≡j∨k≢j = ∨-rec use-k≡j use-k≢j (y→k≡y∨k≢y j)
            where
              use-k≡j = ∨-introᴸ ∘ cong step
              use-k≢j = λ k≢j → ∨-introᴿ (k≢j ∘ step-inj)
