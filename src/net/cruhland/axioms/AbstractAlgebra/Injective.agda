module net.cruhland.axioms.AbstractAlgebra.Injective where

open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_; Eq)
open import net.cruhland.models.Function using
  (_∘_; _⟨→⟩_; ConstrainableFn; flip; toImpFn)

open import net.cruhland.axioms.AbstractAlgebra.Base using
  (forHand; Hand; handᴸ; handᴿ)
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

CancellativeProperty :
  Hand → {A B : Set} → (A → A → B) → (A → A → Set) → (B → B → Set) → A → Set
CancellativeProperty hand _⊙_ _~_ _≈_ x =
  let _<⊙>_ = forHand hand _⊙_
   in ∀ {y₁ y₂} → (x <⊙> y₁) ≈ (x <⊙> y₂) → y₁ ~ y₂

record IsCancellative
    (hand : Hand) {A B : Set} (_⊙_ : A → A → B) (_~_ : A → A → Set)
    (_≈_ : B → B → Set) (C : A → Set)
    : Set where
  constructor isCancellative
  field
    isCancel : ∀ {a} {{_ : C a}} → CancellativeProperty hand _⊙_ _~_ _≈_ a

open IsCancellative {{...}} public using (isCancel)

record Cancellative
    (hand : Hand) {A B : Set} (_⊙_ : A → A → B) (_~_ : A → A → Set)
    (_≈_ : B → B → Set)
    : Set₁ where
  field
    C : A → Set
    cancel : ∀ {a} {{_ : C a}} → CancellativeProperty hand _⊙_ _~_ _≈_ a

open Cancellative {{...}} public using (cancel)

cancellative :
  {hand : Hand} {A B F : Set} {C : A → Set}
  {_⊙_ : A → A → B} {_~_ : A → A → Set} {_≈_ : B → B → Set}
  {{cf : ConstrainableFn F C (CancellativeProperty hand _⊙_ _~_ _≈_)}} → F →
  Cancellative hand _⊙_ _~_ _≈_
cancellative {hand} {C = C} {_⊙_ = _⊙_} {_~_} {_≈_} {{cf}} f =
    record { C = C ; cancel = cancelPrf }
  where
    cancelPrf : ∀ {a} {{_ : C a}} → CancellativeProperty hand _⊙_ _~_ _≈_ a
    cancelPrf {a} {b₁} = toImpFn f {a} {b₁}

isCancellativeᴿ-from-isCancellativeᴸ :
  {A B : Set} {_⊙_ : A → A → B} {_~_ : A → A → Set} {_≈_ : B → B → Set}
  {C : A → Set} {{_ : Eq.Transitive _≈_}} {{_ : Swappable _⊙_ _≈_}}
  {{_ : IsCancellative handᴸ _⊙_ _~_ _≈_ C}} →
  IsCancellative handᴿ _⊙_ _~_ _≈_ C
isCancellativeᴿ-from-isCancellativeᴸ = isCancellative (isCancel ∘ with-swap)

cancellativeᴿ-from-cancellativeᴸ :
  {A B : Set} {_⊙_ : A → A → B} {_~_ : A → A → Set} {_≈_ : B → B → Set}
  {{_ : Eq.Transitive _≈_}} {{_ : Swappable _⊙_ _≈_}}
  {{c : Cancellative handᴸ _⊙_ _~_ _≈_}} → Cancellative handᴿ _⊙_ _~_ _≈_
cancellativeᴿ-from-cancellativeᴸ {{c = c}} =
  let open Cancellative c using (C)
   in record { C = C ; cancel = λ {a} {{_ : C a}} → cancel ∘ with-swap }

cancelᴿ-from-cancelᴸ-comm :
  {A : Set} {_⊙_ : A → A → A} {{_ : Eq A}} {{_ : Commutative _⊙_}}
  {{c : Cancellative handᴸ _⊙_ _≃_ _≃_}} → Cancellative handᴿ _⊙_ _≃_ _≃_
cancelᴿ-from-cancelᴸ-comm = cancellativeᴿ-from-cancellativeᴸ
  where
    instance ⊙-swap = swappable-from-commutative
    instance ≃-substᴿ = EqProperties.≃-substitutiveᴿ

record IsCancellative²
    {A B : Set} (_⊙_ : A → A → B)  (_~_ : A → A → Set) (_≈_ : B → B → Set)
    (C : A → Set)
    : Set where
  constructor isCancellative²
  field
    {{isCancellativeᴸ}} : IsCancellative handᴸ _⊙_ _~_ _≈_ C
    {{isCancellativeᴿ}} : IsCancellative handᴿ _⊙_ _~_ _≈_ C

record Cancellative²
    {A B : Set} (_⊙_ : A → A → B)  (_~_ : A → A → Set) (_≈_ : B → B → Set)
    : Set₁ where
  constructor cancellative²
  field
    {{cancellativeᴸ}} : Cancellative handᴸ _⊙_ _~_ _≈_
    {{cancellativeᴿ}} : Cancellative handᴿ _⊙_ _~_ _≈_

{--- Equivalences ---}

module _
    {A B : Set} {_⊙_ : A → A → B}  {_~_ : A → A → Set} {_≈_ : B → B → Set} where

  injective-from-cancellativeᴸ :
    ∀ {a} {{c : Cancellative handᴸ _⊙_ _~_ _≈_}} {{_ : Cancellative.C c a}} →
      Injective (a ⊙_) _~_ _≈_
  injective-from-cancellativeᴸ = injective cancel

  cancellativeᴸ-from-injective :
    (∀ a → Injective (a ⊙_) _~_ _≈_) → Cancellative handᴸ _⊙_ _~_ _≈_
  cancellativeᴸ-from-injective mkInjective =
    cancellative λ {a b₁ b₂} → inject {{r = mkInjective a}}

  cancellativeᴸ-flip :
    {{c : Cancellative handᴸ _⊙_ _~_ _≈_}} →
    Cancellative handᴿ (flip _⊙_) _~_ _≈_
  cancellativeᴸ-flip {{c}} = cancellative λ {a} {{_ : C a}} {b₁ b₂} → cancel
    where open Cancellative c using (C)

  cancellativeᴿ-flip :
    {{c : Cancellative handᴿ _⊙_ _~_ _≈_}} →
    Cancellative handᴸ (flip _⊙_) _~_ _≈_
  cancellativeᴿ-flip {{c}} = cancellative λ {a} {{_ : C a}} {b₁ b₂} → cancel
    where open Cancellative c using (C)
