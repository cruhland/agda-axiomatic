module net.cruhland.models.Function where

open import Data.Unit using (⊤)

-- Export standard library definitions
open import Function public
  using (_∘_; const; flip; id) renaming (Morphism to _⟨→⟩_)
open import Function.Equivalence public using (Equivalence)

with-dummy-constraint : {A B : Set} → (A → B) → (a : A) {{_ : ⊤}} → B
with-dummy-constraint f a = f a

record ConstrainableFn (F : Set) {A : Set} : Set₁ where
  constructor constrainableFn
  field
    {C} : A → Set
    toConstrainedFn : F → (a : A) {{_ : C a}} → A

open ConstrainableFn {{...}} public using (toConstrainedFn)

instance
  plainFn : {A : Set} → ConstrainableFn (A → A)
  plainFn = constrainableFn with-dummy-constraint

  constrainedFn :
    {A : Set} {C : A → Set} → ConstrainableFn ((a : A) {{_ : C a}} → A)
  constrainedFn = constrainableFn id
