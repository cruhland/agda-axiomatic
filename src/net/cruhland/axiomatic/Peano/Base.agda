module net.cruhland.axiomatic.Peano.Base where

open import Function using (const; _∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import net.cruhland.axiomatic.Logic using
  (∨-introᴸ; ∨-introᴿ; ∨-rec; ⊥; ⊥-elim; ¬sym; Decidable)

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

  record Pred (n : ℕ) : Set where
    constructor Pred-intro
    field
      p : ℕ
      n≡sp : n ≡ step p

  data Case (n : ℕ) : Set where
    Case-zero : (n≡z : n ≡ zero) → Case n
    Case-step : (n≡s : Pred n) → Case n

  case : ∀ n → Case n
  case = ind Case Cz Cs
    where
      Cz = Case-zero refl

      Cs : step-case Case
      Cs {k} _ = Case-step (Pred-intro k refl)

  pred : ∀ {n} → n ≢ zero → Pred n
  pred {n} n≢z with case n
  ... | Case-zero n≡z = ⊥-elim (n≢z n≡z)
  ... | Case-step n≡s = n≡s

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
          Qss {j} _ = ∨-rec use-k≡j use-k≢j (y→k≡y∨k≢y j)
            where
              use-k≡j = ∨-introᴸ ∘ cong step
              use-k≢j = λ k≢j → ∨-introᴿ (k≢j ∘ step-inj)
