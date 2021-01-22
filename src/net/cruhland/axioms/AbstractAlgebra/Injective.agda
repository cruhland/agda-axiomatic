module net.cruhland.axioms.AbstractAlgebra.Injective where

open import net.cruhland.axioms.Eq using (_≃_; _≄_; Eq)
open import net.cruhland.models.Function using (_∘_)
open import net.cruhland.models.Logic using (⊤)

open import net.cruhland.axioms.AbstractAlgebra.Base using
  (forHand; Hand; handᴸ; handᴿ)
open import net.cruhland.axioms.AbstractAlgebra.Commutative using
  (Commutative; with-comm)
open import net.cruhland.axioms.AbstractAlgebra.Substitutive using
  (Substitutive₁; substitutive₁)

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

record Cancellative
    (hand : Hand) {A : Set} (_⊙_ : A → A → A) (_~_ : A → A → Set) : Set₁ where
  constructor cancellative
  _<⊙>_ = forHand hand _⊙_
  field
    C : A → Set
    cancel : ∀ {a b₁ b₂} {{_ : C a}} → (a <⊙> b₁) ~ (a <⊙> b₂) → b₁ ~ b₂

open Cancellative {{...}} public using (cancel)

cancellativeᴿ-from-cancellativeᴸ :
  {A : Set} {_⊙_ : A → A → A} {{_ : Eq A}} {{_ : Commutative _⊙_}}
    {{c : Cancellative handᴸ _⊙_ _≃_}} → Cancellative handᴿ _⊙_ _≃_
cancellativeᴿ-from-cancellativeᴸ {{c = c}} =
  cancellative (Cancellative.C c) (cancel ∘ with-comm)
