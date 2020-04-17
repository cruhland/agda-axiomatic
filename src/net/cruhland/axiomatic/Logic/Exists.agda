module net.cruhland.axiomatic.Logic.Exists where

open import Function using (const)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; sym; cong; subst; subst-subst-sym)
open Eq.≡-Reasoning

record Exists (Σ : (A : Set) → (A → Set) → Set) : Set₁ where
  field
    Σ-intro : {A : Set} {B : A → Set} (a : A) → B a → Σ A B

    Σ-elim :
      {A : Set} {B : A → Set} (C : Σ A B → Set) →
      ((a : A) → (b : B a) → C (Σ-intro a b)) →
      ∀ ΣAB →
      C ΣAB

    Σ-β :
      {A : Set} {B : A → Set} {C : Σ A B → Set} →
      {f : (a : A) → (b : B a) → C (Σ-intro a b)} {a : A} {b : B a} →
      Σ-elim C f (Σ-intro a b) ≡ f a b

    Σ-η :
      ∀ {A} {B : A → Set} {ΣAB : Σ A B} →
      Σ-elim (const (Σ A B)) Σ-intro ΣAB ≡ ΣAB

  Σ-rec : {A C : Set} {B : A → Set} → ((a : A) → B a → C) → Σ A B → C
  Σ-rec {A} {C} {B} f ΣAB = Σ-elim (const C) f ΣAB

  Σ-rec-β :
    ∀ {A C} {B : A → Set} {f : (a : A) → B a → C} {a : A} {b : B a} →
    Σ-rec f (Σ-intro a b) ≡ f a b
  Σ-rec-β = Σ-β

  fst : {A : Set} {B : A → Set} → Σ A B → A
  fst {A} ΣAB = Σ-rec (λ a b → a) ΣAB

  fst-β : ∀ {A} {B : A → Set} {a : A} {b : B a} → fst (Σ-intro {B = B} a b) ≡ a
  fst-β = Σ-rec-β

  snd : {A : Set} {B : A → Set} → (ΣAB : Σ A B) → B (fst ΣAB)
  snd {A} {B} ΣAB =
    Σ-elim (λ ΣAB → B (fst ΣAB)) (λ a b → subst B (sym fst-β) b) ΣAB

  snd-β :
    ∀ {A} {B : A → Set} {a : A} {b : B a} →
    subst B fst-β (snd (Σ-intro {A} {B} a b)) ≡ b
  snd-β {A} {B} {a} {b} =
    begin
      subst B fst-β (snd (Σ-intro {A} {B} a b))
    ≡⟨⟩
      subst B fst-β snd-expanded
    ≡⟨ cong (subst B fst-β) Σ-β ⟩
      subst B fst-β (subst B (sym fst-β) b)
    ≡⟨ subst-subst-sym fst-β ⟩
      b
    ∎
    where
      snd-expanded =
        Σ-elim
          (λ ΣAB → B (fst ΣAB))
          (λ a b → subst B (sym fst-β) b)
          (Σ-intro {B = B} a b)
