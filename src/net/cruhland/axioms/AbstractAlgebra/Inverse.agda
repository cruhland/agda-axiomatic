module net.cruhland.axioms.AbstractAlgebra.Inverse where

open import net.cruhland.axioms.Eq as Eq using (_≃_; Eq)
open import net.cruhland.models.Function using (ConstrainableFn; const; toExpFn)

open import net.cruhland.axioms.AbstractAlgebra.Base
  using (forHand; Hand; handᴸ; handᴿ)
open import net.cruhland.axioms.AbstractAlgebra.Reductive using (Identity²)

record Inverse
    (hand : Hand) {A F : Set} (f : F) (C : A → Set) (_⊙_ : A → A → A) (e : A)
    {{_ : Eq A}} {{_ : ConstrainableFn F C (const A)}} {{_ : Identity² _⊙_ e}}
    : Set₁ where
  constructor inverse
  invert = toExpFn f
  _<⊙>_ = forHand hand _⊙_

  field
    inv : ∀ {a} {{c : C a}} → invert a <⊙> a ≃ e

open Inverse {{...}} public using (inv)

invᴸ = inv {handᴸ}
invᴿ = inv {handᴿ}

record Inverse²
    {A F : Set} (f : F) (C : A → Set) (_⊙_ : A → A → A) (e : A) {{_ : Eq A}}
    {{_ : ConstrainableFn F C (const A)}} {{_ : Identity² _⊙_ e}}
    : Set₁ where
  constructor inverse²
  field
    {{inverseᴸ}} : Inverse handᴸ f C _⊙_ e
    {{inverseᴿ}} : Inverse handᴿ f C _⊙_ e

-- TODO Equivalence for switching handedness and flip _⊙_
