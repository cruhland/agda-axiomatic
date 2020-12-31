module net.cruhland.axioms.AbstractAlgebra.Compatible where

open import net.cruhland.axioms.Eq as Eq using (_≃_; Eq)

private
  record IsCompatible₁
      {A B : Set} {{_ : Eq B}} (f : A → B) (g : A → A) (h : B → B) : Set where
    field
      compat₁ : ∀ {a} → f (g a) ≃ h (f a)

open IsCompatible₁ {{...}} using () renaming (compat₁ to private-compat₁)

record Compatible₁
    {A B : Set} {{_ : Eq B}} (f : A → B) (g : A → A) : Set where
  field
    h : B → B
    isCompat₁ : IsCompatible₁ f g h

  open IsCompatible₁ isCompat₁ public

open Compatible₁ {{...}} public using (compat₁)

compatible₁ :
  {A B : Set} {{_ : Eq B}} {f : A → B} {g : A → A}
    (h : B → B) → (∀ {a} → f (g a) ≃ h (f a)) → Compatible₁ f g
compatible₁ h compatFn =
  record { h = h ; isCompat₁ = record { compat₁ = compatFn } }

record Compatible₂
    {A B : Set} {{_ : Eq B}} (f : A → B) (_⊙_ : A → A → A) : Set where
  field
    _⊕_ : B → B → B
    {{isCompat₁}} : ∀ {b} → IsCompatible₁ f (_⊙ b) (_⊕ f b)

compatible₂ :
  {A B : Set} {{_ : Eq B}} {f : A → B} {_⊙_ : A → A → A}
    (_⊕_ : B → B → B) → (∀ {a b} → f (a ⊙ b) ≃ f a ⊕ f b) → Compatible₂ f _⊙_
compatible₂ _⊕_ compatFn =
  record { _⊕_ = _⊕_ ; isCompat₁ = record { compat₁ = compatFn } }

compat₂ :
  {A B : Set} {f : A → B} {_⊙_ : A → A → A}
    {{_ : Eq B}} {{r : Compatible₂ f _⊙_}} →
      let open Compatible₂ r using (_⊕_) in ∀ {a b} → f (a ⊙ b) ≃ f a ⊕ f b
compat₂ = private-compat₁
