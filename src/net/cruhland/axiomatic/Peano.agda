module net.cruhland.axiomatic.Peano where

open import Function using (const; _∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import net.cruhland.axiomatic.Logic
  using (_∨_; Σ; ∨-introᴸ; ∨-introᴿ; Σ-intro; ∨-forceᴿ; Decidable; ¬sym; ∨-rec)

record Peano (ℕ : Set) : Set₁ where
  field
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

  rec : {A : Set} → A → (A → A) → ℕ → A
  rec {A} z s n = ind (const A) z s n

  rec-zero : {A : Set} {z : A} {s : A → A} → rec z s zero ≡ z
  rec-zero {A} = ind-zero {const A}

  rec-step :
    {A : Set} {z : A} {s : A → A} {n : ℕ} → rec z s (step n) ≡ s (rec z s n)
  rec-step {A} = ind-step {const A}

  rec-s-comm :
    {A : Set} {z : A} {s : A → A} {n : ℕ} → s (rec z s n) ≡ rec (s z) s n
  rec-s-comm {A} {z} {s} {n} = ind P Pz Ps n
    where
      P = λ x → s (rec z s x) ≡ rec (s z) s x

      Pz =
        begin
          s (rec z s zero)
        ≡⟨ cong s rec-zero ⟩
          s z
        ≡⟨ sym rec-zero ⟩
          rec (s z) s zero
        ∎

      Ps : step-case P
      Ps {k} s[rec-z]≡rec[s-z] =
        begin
          s (rec z s (step k))
        ≡⟨ cong s rec-step ⟩
          s (s (rec z s k))
        ≡⟨ cong s s[rec-z]≡rec[s-z] ⟩
          s (rec (s z) s k)
        ≡⟨ sym rec-step ⟩
          rec (s z) s (step k)
        ∎

  rec-step-tail :
    {A : Set} {z : A} {s : A → A} {n : ℕ} → rec z s (step n) ≡ rec (s z) s n
  rec-step-tail = trans rec-step rec-s-comm

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

record PeanoBundle : Set₁ where
  field
    ℕ : Set
    isPeano : Peano ℕ

  open Peano isPeano public
