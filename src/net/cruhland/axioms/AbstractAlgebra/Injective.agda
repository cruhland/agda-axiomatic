module net.cruhland.axioms.AbstractAlgebra.Injective where

open import net.cruhland.axioms.Eq using (_≃_; _≄_; Eq)
open import net.cruhland.models.Function using
  (_∘_; ConstrainableFn; flip; toImpFn)

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

CancellativeProperty : Hand → {A : Set} → (A → A → A) → (A → A → Set) → A → Set
CancellativeProperty hand _⊙_ _~_ a =
  let _<⊙>_ = forHand hand _⊙_
   in ∀ {b₁ b₂} → (a <⊙> b₁) ~ (a <⊙> b₂) → b₁ ~ b₂

record Cancellative
    (hand : Hand) {A : Set} (_⊙_ : A → A → A) (_~_ : A → A → Set) : Set₁ where
  field
    C : A → Set
    cancel : ∀ {a} {{_ : C a}} → CancellativeProperty hand _⊙_ _~_ a

open Cancellative {{...}} public using (cancel)

cancellative :
  {hand : Hand} {A F : Set} {_⊙_ : A → A → A} {_~_ : A → A → Set}
    {{cf : ConstrainableFn F (CancellativeProperty hand _⊙_ _~_)}} → F →
      Cancellative hand _⊙_ _~_
cancellative {hand} {_⊙_ = _⊙_} {_~_} {{cf}} f =
    record { C = C ; cancel = cancelPrf }
  where
    open ConstrainableFn cf using (C)

    cancelPrf : ∀ {a} {{_ : C a}} → CancellativeProperty hand _⊙_ _~_ a
    cancelPrf {a} {b₁} = toImpFn f {a} {b₁}

cancellativeᴿ-from-cancellativeᴸ :
  {A : Set} {_⊙_ : A → A → A} {{_ : Eq A}} {{_ : Commutative _⊙_}}
    {{c : Cancellative handᴸ _⊙_ _≃_}} → Cancellative handᴿ _⊙_ _≃_
cancellativeᴿ-from-cancellativeᴸ {{c = c}} =
  let open Cancellative c using (C)
   in record { C = C ; cancel = λ {a} {{_ : C a}} → cancel ∘ with-comm }

{--- Equivalences ---}

module _ {A : Set} {_⊙_ : A → A → A} {_~_ : A → A → Set} where

  injective-from-cancellativeᴸ :
    ∀ {a} {{c : Cancellative handᴸ _⊙_ _~_}} {{_ : Cancellative.C c a}} →
      Injective (a ⊙_) _~_ _~_
  injective-from-cancellativeᴸ = injective cancel

  cancellativeᴸ-from-injective :
    (∀ a → Injective (a ⊙_) _~_ _~_) → Cancellative handᴸ _⊙_ _~_
  cancellativeᴸ-from-injective mkInjective =
    cancellative λ {a b₁ b₂} → inject {{r = mkInjective a}}

  cancellativeᴸ-flip :
    {{c : Cancellative handᴸ _⊙_ _~_}} → Cancellative handᴿ (flip _⊙_) _~_
  cancellativeᴸ-flip {{c}} = cancellative λ {a} {{_ : C a}} {b₁ b₂} → cancel
    where open Cancellative c using (C)

  cancellativeᴿ-flip :
    {{c : Cancellative handᴿ _⊙_ _~_}} → Cancellative handᴸ (flip _⊙_) _~_
  cancellativeᴿ-flip {{c}} = cancellative λ {a} {{_ : C a}} {b₁ b₂} → cancel
    where open Cancellative c using (C)
