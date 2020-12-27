module net.cruhland.axioms.AbstractAlgebra.Injective where

open import Function using (_∘_)
open import net.cruhland.axioms.Eq using (_≃_; _≄_; Eq)
open import net.cruhland.models.Logic using (⊤)

open import net.cruhland.axioms.AbstractAlgebra.Commutative
open import net.cruhland.axioms.AbstractAlgebra.Substitutive

record Injective
    {A B : Set} (f : A → B) (_~_ : A → A → Set) (_≈_ : B → B → Set) : Set where
  field
    inject : ∀ {a₁ a₂} → f a₁ ≈ f a₂ → a₁ ~ a₂

open Injective {{...}} public using (inject)

instance
  ≄-substitutive :
    {A B : Set} {f : A → B}
      {{_ : Eq A}} {{_ : Eq B}} {{_ : Injective f _≃_ _≃_}} →
        Substitutive₁ f _≄_ _≄_
  ≄-substitutive = substitutive₁ (λ a₁≄a₂ fa₁≃fa₂ → a₁≄a₂ (inject fa₁≃fa₂))

record Cancellativeᴸ
    {A : Set} (_⊙_ : A → A → A) (_~_ : A → A → Set) : Set₁ where
  field
    C : A → Set
    {{injectᴸ}} : ∀ {a} {{_ : C a}} → Injective (a ⊙_) _~_ _~_

cancellativeⁱᴸ :
  {A : Set} {_⊙_ : A → A → A} {_~_ : A → A → Set}
    (C : A → Set) → (∀ {a b₁ b₂} {{c : C a}} → (a ⊙ b₁) ~ (a ⊙ b₂) → b₁ ~ b₂) →
      Cancellativeᴸ _⊙_ _~_
cancellativeⁱᴸ C injectFn =
  record { C = C ; injectᴸ = record { inject = injectFn } }

cancellativeᴸ :
  {A : Set} {_⊙_ : A → A → A} {_~_ : A → A → Set} →
    (∀ {a b₁ b₂} → (a ⊙ b₁) ~ (a ⊙ b₂) → b₁ ~ b₂) →
      Cancellativeᴸ _⊙_ _~_
cancellativeᴸ injectFn = cancellativeⁱᴸ (λ _ → ⊤) (λ {a} → injectFn {a})

cancelᴸ :
  {A : Set} {_⊙_ : A → A → A} {_~_ : A → A → Set}
    {{cancel : Cancellativeᴸ _⊙_ _~_}} →
      ∀ {a b₁ b₂} {{_ : Cancellativeᴸ.C cancel a}} →
        (a ⊙ b₁) ~ (a ⊙ b₂) → b₁ ~ b₂
cancelᴸ = inject

record Cancellativeᴿ
    {A : Set} (_⊙_ : A → A → A) (_~_ : A → A → Set) : Set₁ where
  field
    C : A → Set
    {{injectᴿ}} : ∀ {a} {{_ : C a}} → Injective (_⊙ a) _~_ _~_

cancellativeⁱᴿ :
  {A : Set} {_⊙_ : A → A → A} {_~_ : A → A → Set}
    (C : A → Set) → (∀ {a b₁ b₂} {{c : C a}} → (b₁ ⊙ a) ~ (b₂ ⊙ a) → b₁ ~ b₂) →
      Cancellativeᴿ _⊙_ _~_
cancellativeⁱᴿ C injectFn =
  record { C = C ; injectᴿ = record { inject = injectFn } }

cancellativeᴿ :
  {A : Set} {_⊙_ : A → A → A} {_~_ : A → A → Set} →
    (∀ {a b₁ b₂} → (b₁ ⊙ a) ~ (b₂ ⊙ a) → b₁ ~ b₂) →
      Cancellativeᴿ _⊙_ _~_
cancellativeᴿ injectFn = cancellativeⁱᴿ (λ _ → ⊤) (λ {a} → injectFn {a})

cancellativeᴿ-from-cancellativeᴸ :
  {A : Set} {_⊙_ : A → A → A}
    {{eq : Eq A}} {{⊙-comm : Commutative _⊙_}}
    {{⊙-cancelᴸ : Cancellativeᴸ _⊙_ _≃_}} →
      Cancellativeᴿ _⊙_ _≃_
cancellativeᴿ-from-cancellativeᴸ {{⊙-cancelᴸ = ⊙-cancelᴸ}} = record
  { C = Cancellativeᴸ.C ⊙-cancelᴸ
  ; injectᴿ = record { inject = cancelᴸ ∘ with-comm }
  }

cancelᴿ :
  {A : Set} {_⊙_ : A → A → A} {_~_ : A → A → Set}
    {{cancel : Cancellativeᴿ _⊙_ _~_}} →
      ∀ {a b₁ b₂} {{_ : Cancellativeᴿ.C cancel a}} →
        (b₁ ⊙ a) ~ (b₂ ⊙ a) → b₁ ~ b₂
cancelᴿ = inject
