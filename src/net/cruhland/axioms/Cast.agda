module net.cruhland.axioms.Cast where

open import Level using (_⊔_)
open import net.cruhland.models.Function using (id)

record _As_ {α β} (A : Set α) (B : Set β) : Set (α ⊔ β) where
  constructor As-intro
  field
    cast : A → B

open _As_ {{...}} public using (cast)

{-# DISPLAY _As_.cast _ x = cast x #-}

infixl 0 _as_
_as_ : ∀ {α β} {A : Set α} → A → (B : Set β) {{_ : A As B}} → B
x as B = cast x

_value_ : (A : Set) → A → A
A value x = x

via : ({A} B {C} : Set) {{_ : A As B}} {{_ : B As C}} → A As C
via B {C} = As-intro λ x → (x as B) as C

delegate₂ :
  {A₁ B₁ C₁ A₂ B₂ C₂ : Set} (f : A₂ → B₂ → C₂)
    {{_ : A₁ As A₂}} {{_ : B₁ As B₂}} {{_ : C₂ As C₁}} →
      A₁ → B₁ → C₁
delegate₂ {C₁ = C₁} {A₂} {B₂} f a₁ b₁ = f (a₁ as A₂) (b₁ as B₂) as C₁
