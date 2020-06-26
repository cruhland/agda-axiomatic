module net.cruhland.axiomatic.Logic.Exists where

open import Function using (const; id)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; subst; subst-subst-sym)
open Eq.≡-Reasoning

-- Export standard library definitions
open import Data.Product public
  using (Σ) renaming (_,_ to Σ-intro; proj₁ to fst; proj₂ to snd)

Σ-elim :
  ∀ {α β χ} {A : Set α} {B : A → Set β} (C : Σ A B → Set χ) →
  ((a : A) → (b : B a) → C (Σ-intro a b)) →
  ∀ ΣAB →
  C ΣAB
Σ-elim C f (Σ-intro fst snd) = f fst snd

Σ-rec :
  ∀ {α β χ} {A : Set α} {B : A → Set β} {C : Set χ} →
  ((a : A) → B a → C) → Σ A B → C
Σ-rec {α} {β} {χ} {A} {B} {C} f ΣAB = Σ-elim (const C) f ΣAB

Σ-rec-β :
  ∀ {α β χ} {A : Set α} {B : A → Set β} {C : Set χ}
  {f : (a : A) → B a → C} {a : A} {b : B a} →
  Σ-rec f (Σ-intro a b) ≡ f a b
Σ-rec-β = refl

fst-β :
  ∀ {α β} {A : Set α} {B : A → Set β} {a : A} {b : B a} →
  fst (Σ-intro {B = B} a b) ≡ a
fst-β {α} {β} {A} {B} {a} {b} = Σ-rec-β {α} {β} {α} {A} {B} {A} {λ x _ → x} {a} {b}

snd-β :
  ∀ {α β} {A : Set α} {B : A → Set β} {a : A} {b : B a} →
  subst B (fst-β {B = B} {b = b}) (snd (Σ-intro {A = A} {B} a b)) ≡ b
snd-β {α} {β} {A} {B} {a} {b} =
  begin
    subst B (fst-β {B = B} {b = b}) (snd (Σ-intro {A = A} {B} a b))
  ≡⟨⟩
    subst B (fst-β {B = B} {b = b}) snd-expanded
  ≡⟨ cong (subst B (fst-β {B = B} {b = b})) refl ⟩
    subst B (fst-β {B = B} {b = b}) (subst B (sym (fst-β {B = B} {b = b})) b)
  ≡⟨ subst-subst-sym {P = B} (fst-β {B = B} {b = b}) ⟩
    b
  ∎
  where
    snd-expanded =
      Σ-elim
        (λ ΣAB → B (fst ΣAB))
        (λ a b → subst B (sym (fst-β {B = B} {b = b})) b)
        (Σ-intro {B = B} a b)

Σ-map-snd :
  ∀ {α β χ} {A : Set α} {B : A → Set β} {C : A → Set χ} →
  (f : ∀ {a} → B a → C a) → Σ A B → Σ A C
Σ-map-snd f ΣAB = Σ-rec (λ a b → Σ-intro a (f b)) ΣAB

Σ-map-snd-id :
  ∀ {α β} {A : Set α} {B : A → Set β} {ΣAB : Σ A B} → Σ-map-snd id ΣAB ≡ ΣAB
Σ-map-snd-id {ΣAB = Σ-intro a b} = refl
