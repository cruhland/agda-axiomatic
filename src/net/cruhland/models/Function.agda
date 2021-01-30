module net.cruhland.models.Function where

open import Level using (_⊔_; 0ℓ) renaming (suc to sℓ)
open import Data.Unit using (⊤)

-- Export standard library definitions
open import Function public
  using (_∘_; const; flip; id) renaming (Morphism to _⟨→⟩_)
open import Function.Equivalence public using (Equivalence)

addDummyConstraintExp :
  {A : Set} {B : A → Set} → ((a : A) → B a) → (a : A) {{_ : ⊤}} → B a
addDummyConstraintExp f a = f a

addDummyConstraintImp :
  {A : Set} {B : A → Set} → ({a : A} → B a) → {a : A} {{_ : ⊤}} → B a
addDummyConstraintImp f {a} = f

toExp : {A : Set} {B : A → Set} → ({a : A} → B a) → (a : A) → B a
toExp f a = f {a}

toImp : {A : Set} {B : A → Set} → ((a : A) → B a) → {a : A} → B a
toImp f {a} = f a

record ConstrainableFn
    {β} (F : Set) {A : Set} (B : A → Set β) : Set (β ⊔ sℓ 0ℓ) where
  constructor constrainableFn
  field
    {C} : A → Set
    toExpFn : F → (a : A) {{_ : C a}} → B a
    toImpFn : F → {a : A} {{_ : C a}} → B a

open ConstrainableFn {{...}} public using (toExpFn; toImpFn)

instance
  plainExpFn : {A : Set} {B : A → Set} → ConstrainableFn ((a : A) → B a) B
  plainExpFn =
    constrainableFn addDummyConstraintExp (toImp ∘ addDummyConstraintExp)

  plainImpFn : {A : Set} {B : A → Set} → ConstrainableFn ({a : A} → B a) B
  plainImpFn =
    constrainableFn (toExp ∘ addDummyConstraintImp) addDummyConstraintImp

  constrainedExpFn :
    {A : Set} {B C : A → Set} → ConstrainableFn ((a : A) {{_ : C a}} → B a) B
  constrainedExpFn = constrainableFn id toImp

  constrainedImpFn :
    {A : Set} {B C : A → Set} → ConstrainableFn ({a : A} {{_ : C a}} → B a) B
  constrainedImpFn = constrainableFn toExp id
