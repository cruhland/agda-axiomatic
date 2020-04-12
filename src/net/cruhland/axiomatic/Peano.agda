module net.cruhland.axiomatic.Peano where

open import Function using (const)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; sym; trans; cong)
open Eq.≡-Reasoning

record Peano (ℕ : Set) : Set₁ where
  field
    zero : ℕ
    succ : ℕ → ℕ

    succ≢zero : ∀ {n} → succ n ≢ zero
    succ-inj : ∀ {n m} → succ n ≡ succ m → n ≡ m

  succProp : (P : ℕ → Set) → Set
  succProp P = ∀ {k} → P k → P (succ k)

  field
    ind : (P : ℕ → Set) → P zero → succProp P → ∀ n → P n
    ind-zero : ∀ {P z} {s : succProp P} → ind P z s zero ≡ z
    ind-succ : ∀ {P z n} {s : succProp P} → ind P z s (succ n) ≡ s (ind P z s n)

  rec : {A : Set} → A → (A → A) → ℕ → A
  rec {A} z s n = ind (const A) z s n

  rec-zero : {A : Set} {z : A} {s : A → A} → rec z s zero ≡ z
  rec-zero {A} = ind-zero {const A}

  rec-succ :
    {A : Set} {z : A} {s : A → A} {n : ℕ} → rec z s (succ n) ≡ s (rec z s n)
  rec-succ {A} = ind-succ {const A}

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

      Ps : succProp P
      Ps {k} s[rec-z]≡rec[s-z] =
        begin
          s (rec z s (succ k))
        ≡⟨ cong s rec-succ ⟩
          s (s (rec z s k))
        ≡⟨ cong s s[rec-z]≡rec[s-z] ⟩
          s (rec (s z) s k)
        ≡⟨ sym rec-succ ⟩
          rec (s z) s (succ k)
        ∎

  rec-succ-tail :
    {A : Set} {z : A} {s : A → A} {n : ℕ} → rec z s (succ n) ≡ rec (s z) s n
  rec-succ-tail = trans rec-succ rec-s-comm

record PeanoBundle : Set₁ where
  field
    ℕ : Set
    isPeano : Peano ℕ

  open Peano isPeano public
