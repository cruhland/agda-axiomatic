module net.cruhland.axioms.Cast where

record _As_ (A B : Set) : Set where
  field
    cast : A → B

open _As_ {{...}} using (cast)

infixl 0 _as_
_as_ : {A : Set} → A → (B : Set) {{_ : A As B}} → B
x as B = cast x

_value_ : (A : Set) → A → A
A value x = x

transitive : {A B C : Set} {{_ : A As B}} {{_ : B As C}} → A As C
transitive {A} {B} {C} = record { cast = λ x → (x as B) as C }
