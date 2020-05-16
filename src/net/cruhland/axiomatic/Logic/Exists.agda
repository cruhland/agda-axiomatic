module net.cruhland.axiomatic.Logic.Exists where

open import Function using (const; id)
open import Level using (_⊔_; Setω)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; sym; cong; subst; subst-subst-sym)
open Eq.≡-Reasoning

record Exists (Σ : ∀ {α β} (A : Set α) → (A → Set β) → Set (α ⊔ β))
    : Setω where
  field
    Σ-intro : ∀ {α β} {A : Set α} {B : A → Set β} (a : A) → B a → Σ A B

    Σ-elim :
      ∀ {α β χ} {A : Set α} {B : A → Set β} (C : Σ A B → Set χ) →
      ((a : A) → (b : B a) → C (Σ-intro a b)) →
      ∀ ΣAB →
      C ΣAB

    Σ-β :
      ∀ {α β χ} {A : Set α} {B : A → Set β} {C : Σ A B → Set χ} →
      {f : (a : A) → (b : B a) → C (Σ-intro a b)} {a : A} {b : B a} →
      Σ-elim C f (Σ-intro a b) ≡ f a b

    Σ-η :
      ∀ {α β} {A : Set α} {B : A → Set β} {ΣAB : Σ A B} →
      Σ-elim (const (Σ A B)) Σ-intro ΣAB ≡ ΣAB

  Σ-rec :
    ∀ {α β χ} {A : Set α} {B : A → Set β} {C : Set χ} →
    ((a : A) → B a → C) → Σ A B → C
  Σ-rec {α} {β} {χ} {A} {B} {C} f ΣAB = Σ-elim (const C) f ΣAB

  Σ-rec-β :
    ∀ {α β χ} {A : Set α} {B : A → Set β} {C : Set χ}
    {f : (a : A) → B a → C} {a : A} {b : B a} →
    Σ-rec f (Σ-intro a b) ≡ f a b
  Σ-rec-β = Σ-β

  fst : ∀ {α β} {A : Set α} {B : A → Set β} → Σ A B → A
  fst {A = A} ΣAB = Σ-rec (λ a b → a) ΣAB

  fst-β :
    ∀ {α β} {A : Set α} {B : A → Set β} {a : A} {b : B a} →
    fst (Σ-intro {B = B} a b) ≡ a
  fst-β = Σ-rec-β

  snd : ∀ {α β} {A : Set α} {B : A → Set β} → (ΣAB : Σ A B) → B (fst ΣAB)
  snd {α} {β} {A} {B} ΣAB =
    Σ-elim (λ ΣAB → B (fst ΣAB)) (λ a b → subst B (sym fst-β) b) ΣAB

  snd-β :
    ∀ {α β} {A : Set α} {B : A → Set β} {a : A} {b : B a} →
    subst B fst-β (snd (Σ-intro {A = A} {B} a b)) ≡ b
  snd-β {α} {β} {A} {B} {a} {b} =
    begin
      subst B fst-β (snd (Σ-intro {A = A} {B} a b))
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

  Σ-map-snd :
    ∀ {α β χ} {A : Set α} {B : A → Set β} {C : A → Set χ} →
    (f : ∀ {a} → B a → C a) → Σ A B → Σ A C
  Σ-map-snd f ΣAB = Σ-rec (λ a b → Σ-intro a (f b)) ΣAB

  Σ-map-snd-id :
    ∀ {α β} {A : Set α} {B : A → Set β} {ΣAB : Σ A B} → Σ-map-snd id ΣAB ≡ ΣAB
  Σ-map-snd-id = Σ-η
