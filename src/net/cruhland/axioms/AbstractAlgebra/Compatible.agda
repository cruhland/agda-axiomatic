module net.cruhland.axioms.AbstractAlgebra.Compatible where

open import net.cruhland.axioms.Eq as Eq using (_≃_; Eq)

private
  record IsCompatible₁
      {A B : Set} {{_ : Eq B}} (f : A → B) (g : A → A) (h : B → B) : Set where
    constructor isCompatible₁
    field
      isCompat₁ : ∀ {a} → f (g a) ≃ h (f a)

  open IsCompatible₁ {{...}} using (isCompat₁)

  record IsCompatible₂
      {A B : Set} {{_ : Eq B}}
        (f : A → B) (_⊙_ : A → A → A) (_⊕_ : B → B → B) : Set where
    constructor isCompatible₂
    field
      isCompat₂ : ∀ {a b} → f (a ⊙ b) ≃ f a ⊕ f b

  open IsCompatible₂ {{...}} using (isCompat₂)

record Compatible₁ {A B : Set} {{_ : Eq B}} (f : A → B) (g : A → A) : Set where
  constructor compatible₁
  field
    h : B → B
    compat₁ : ∀ {a} → f (g a) ≃ h (f a)

open Compatible₁ {{...}} public using (compat₁)

record Compatible₂
    {A B : Set} {{_ : Eq B}} (f : A → B) (_⊙_ : A → A → A) : Set where
  constructor compatible₂
  field
    _⊕_ : B → B → B
    compat₂ : ∀ {a b} → f (a ⊙ b) ≃ f a ⊕ f b

open Compatible₂ {{...}} public using (compat₂)

record Distributiveᴸ {A : Set} {{_ : Eq A}} (_⊙_ _⊕_ : A → A → A) : Set where
  constructor distributiveᴸ
  field
    distribᴸ : ∀ {a b c} → a ⊙ (b ⊕ c) ≃ (a ⊙ b) ⊕ (a ⊙ c)

open Distributiveᴸ {{...}} public using (distribᴸ)

{--- Equivalences ---}

module _ {A B : Set} {f : A → B} {g : A → A} {{_ : Eq B}} where

  isCompatible₁-from-compatible₁ :
    {{r : Compatible₁ f g}} →
      let open Compatible₁ r using (h) in IsCompatible₁ f g h
  isCompatible₁-from-compatible₁ = isCompatible₁ compat₁

  compatible₁-from-isCompatible₁ :
    {h : B → B} {{_ : IsCompatible₁ f g h}} → Compatible₁ f g
  compatible₁-from-isCompatible₁ {h} = compatible₁ h isCompat₁

module _
    {A B : Set} {f : A → B} {_⊙_ : A → A → A} {_⊕_ : B → B → B}
      {{_ : Eq B}} where

  isCompatible₁-from-isCompatible₂ :
    {{_ : IsCompatible₂ f _⊙_ _⊕_}} → ∀ {b} → IsCompatible₁ f (_⊙ b) (_⊕ f b)
  isCompatible₁-from-isCompatible₂ = isCompatible₁ isCompat₂

  isCompatible₂-from-isCompatible₁ :
    {{_ : ∀ {b} → IsCompatible₁ f (_⊙ b) (_⊕ f b)}} → IsCompatible₂ f _⊙_ _⊕_
  isCompatible₂-from-isCompatible₁ = isCompatible₂ isCompat₁

module _ {A B : Set} {f : A → B} {_⊙_ : A → A → A} {{_ : Eq B}} where

  isCompatible₂-from-compatible₂ :
    {{r : Compatible₂ f _⊙_}} →
      let open Compatible₂ r using (_⊕_) in IsCompatible₂ f _⊙_ _⊕_
  isCompatible₂-from-compatible₂ = isCompatible₂ compat₂

  compatible₂-from-isCompatible₂ :
    {_⊕_ : B → B → B} {{_ : IsCompatible₂ f _⊙_ _⊕_}} → Compatible₂ f _⊙_
  compatible₂-from-isCompatible₂ {_⊕_} = compatible₂ _⊕_ isCompat₂

module _ {A : Set} {_⊙_ _⊕_ : A → A → A} {{_ : Eq A}} where

  isCompatible₂-from-distributiveᴸ :
    {{_ : Distributiveᴸ _⊙_ _⊕_}} → ∀ {a} → IsCompatible₂ (a ⊙_) _⊕_ _⊕_
  isCompatible₂-from-distributiveᴸ {a} = isCompatible₂ distribᴸ

  distributiveᴸ-from-isCompatible₂ :
    {{_ : ∀ {a} → IsCompatible₂ (a ⊙_) _⊕_ _⊕_}} → Distributiveᴸ _⊙_ _⊕_
  distributiveᴸ-from-isCompatible₂ = distributiveᴸ isCompat₂
