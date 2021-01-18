module net.cruhland.axioms.Cast where

record _As_ (A B : Set) : Set where
  field
    cast : A → B

open _As_ {{...}} public using (cast)

infixl 0 _as_
_as_ : {A : Set} → A → (B : Set) {{_ : A As B}} → B
x as B = cast x

_value_ : (A : Set) → A → A
A value x = x

via : ({A} B {C} : Set) {{_ : A As B}} {{_ : B As C}} → A As C
via B {C} = record { cast = λ x → (x as B) as C }

delegate₂ :
  {A₁ B₁ C₁ A₂ B₂ C₂ : Set} (f : A₂ → B₂ → C₂)
    {{_ : A₁ As A₂}} {{_ : B₁ As B₂}} {{_ : C₂ As C₁}} →
      A₁ → B₁ → C₁
delegate₂ {C₁ = C₁} {A₂} {B₂} f a₁ b₁ = f (a₁ as A₂) (b₁ as B₂) as C₁
