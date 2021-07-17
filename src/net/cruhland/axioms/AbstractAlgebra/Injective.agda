module net.cruhland.axioms.AbstractAlgebra.Injective where

open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_; Eq)
open import net.cruhland.models.Function using
  (_∘_; _⟨→⟩_; ConstrainableFn; flip; toImpFn)
import net.cruhland.models.Logic

open import net.cruhland.axioms.AbstractAlgebra.Base using
  (forHand; forHandᶜ; Hand; handᴸ; handᴿ; tc₂)
open import net.cruhland.axioms.AbstractAlgebra.Substitutive using
  (Substitutive₁; substitutive₁; Substitutive₂; swappable-from-commutative
  ; module EqProperties
  )
open import net.cruhland.axioms.AbstractAlgebra.Swappable using
  (Commutative; Swappable; with-swap)

record Injective
    {A B : Set} (f : A → B) (_~_ : A → A → Set) (_≈_ : B → B → Set) : Set where
  constructor injective
  field
    inject : ∀ {a₁ a₂} → f a₁ ≈ f a₂ → a₁ ~ a₂

open Injective {{...}} public using (inject)

instance
  ≄-substitutive :
    {A B : Set} {f : A → B}
      {{_ : Eq A}} {{_ : Eq B}} {{_ : Injective f _≃_ _≃_}} →
        Substitutive₁ f _≄_ _≄_
  ≄-substitutive = substitutive₁ (λ a₁≄a₂ fa₁≃fa₂ → a₁≄a₂ (inject fa₁≃fa₂))

CancellativePropertyᶜ :
  Hand → {A B : Set} {C : A → A → Set} → ((x y : A) {{_ : C x y}} → B) →
  (A → A → Set) → (B → B → Set) → A → Set
CancellativePropertyᶜ hand {C = C} _⊙_ _~_ _≈_ x =
  let C˘ = forHand hand C
      _⊙˘_ = forHandᶜ hand _⊙_
   in ∀ {y₁ y₂} {{c₁ : C˘ x y₁}} {{c₂ : C˘ x y₂}} →
      (x ⊙˘ y₁) ≈ (x ⊙˘ y₂) → y₁ ~ y₂

CancellativeProperty :
  Hand → {A B : Set} → (A → A → B) → (A → A → Set) → (B → B → Set) → A → Set
CancellativeProperty hand _⊙_ = CancellativePropertyᶜ hand (tc₂ _⊙_)

record Cancellativeᶜ
    (hand : Hand) {A B : Set} {C⊙ : A → A → Set}
    (_⊙_ : (x y : A) {{_ : C⊙ x y}} → B)
    (_~_ : A → A → Set) (_≈_ : B → B → Set) (C : A → Set)
    : Set where
  constructor cancellative
  field
    cancel : ∀ {a} {{c : C a}} → CancellativePropertyᶜ hand _⊙_ _~_ _≈_ a

open Cancellativeᶜ {{...}} public using (cancel)

Cancellative :
    Hand → {A B : Set} (_⊙_ : A → A → B) (_~_ : A → A → Set) (_≈_ : B → B → Set)
    (C : A → Set) → Set
Cancellative hand _⊙_ = Cancellativeᶜ hand (tc₂ _⊙_)

cancellativeᴿ-from-cancellativeᴸ :
  {A B : Set} {_⊙_ : A → A → B} {_~_ : A → A → Set} {_≈_ : B → B → Set}
  {C : A → Set} {{_ : Eq.Transitive _≈_}} {{_ : Swappable _⊙_ _≈_}}
  {{_ : Cancellative handᴸ _⊙_ _~_ _≈_ C}} →
  Cancellative handᴿ _⊙_ _~_ _≈_ C
cancellativeᴿ-from-cancellativeᴸ = cancellative (cancel ∘ with-swap)

cancelᴿ-from-cancelᴸ-comm :
  {A : Set} {_⊙_ : A → A → A} {C : A → Set} {{_ : Eq A}} {{_ : Commutative _⊙_}}
  {{c : Cancellative handᴸ _⊙_ _≃_ _≃_ C}} → Cancellative handᴿ _⊙_ _≃_ _≃_ C
cancelᴿ-from-cancelᴸ-comm = cancellativeᴿ-from-cancellativeᴸ
  where
    instance ⊙-swap = swappable-from-commutative
    instance ≃-substᴿ = EqProperties.≃-substitutiveᴿ

record Cancellative²ᶜ
    {A B : Set} {C⊙ : A → A → Set}
    (_⊙_ : (x y : A) {{_ : C⊙ x y}} → B)
    (_~_ : A → A → Set) (_≈_ : B → B → Set) (Cᴸ : A → Set) (Cᴿ : A → Set)
    : Set where
  constructor cancellative²
  field
    {{cancellativeᴸ}} : Cancellativeᶜ handᴸ _⊙_ _~_ _≈_ Cᴸ
    {{cancellativeᴿ}} : Cancellativeᶜ handᴿ _⊙_ _~_ _≈_ Cᴿ

Cancellative² :
  {A B : Set} (_⊙_ : A → A → B) (_~_ : A → A → Set) (_≈_ : B → B → Set)
  (C : A → Set) → Set
Cancellative² _⊙_ _~_ _≈_ C = Cancellative²ᶜ (tc₂ _⊙_) _~_ _≈_ C C

{--- Equivalences ---}

module _
    {A B : Set} {C : A → Set} {_⊙_ : A → A → B}
    {_~_ : A → A → Set} {_≈_ : B → B → Set}
    where

  injective-from-cancellativeᴸ :
    ∀ {a} {{_ : Cancellative handᴸ _⊙_ _~_ _≈_ C}} {{_ : C a}} →
    Injective (a ⊙_) _~_ _≈_
  injective-from-cancellativeᴸ = injective cancel

  cancellativeᴸ-from-injective :
    (∀ a → Injective (a ⊙_) _~_ _≈_) → Cancellative handᴸ _⊙_ _~_ _≈_ C
  cancellativeᴸ-from-injective mkInjective =
    cancellative λ {a b₁ b₂} → inject {{r = mkInjective a}}

  cancellativeᴸ-flip :
    {{c : Cancellative handᴸ _⊙_ _~_ _≈_ C}} →
    Cancellative handᴿ (flip _⊙_) _~_ _≈_ C
  cancellativeᴸ-flip {{c}} = cancellative λ {a} {{_ : C a}} {b₁ b₂} → cancel

  cancellativeᴿ-flip :
    {{c : Cancellative handᴿ _⊙_ _~_ _≈_ C}} →
    Cancellative handᴸ (flip _⊙_) _~_ _≈_ C
  cancellativeᴿ-flip {{c}} = cancellative λ {a} {{_ : C a}} {b₁ b₂} → cancel
