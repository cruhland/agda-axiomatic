module net.cruhland.axioms.AbstractAlgebra.Inverse where

open import net.cruhland.axioms.Eq as Eq using (_≃_; Eq)

private
  module AA where
    open import net.cruhland.axioms.AbstractAlgebra.Base public
    open import net.cruhland.axioms.AbstractAlgebra.Reductive public

open AA using (forHand; Hand; handᴸ; handᴿ)

record Inverse
    (hand : Hand) {A : Set} {C : A → Set} (invert : (a : A) {{_ : C a}} → A)
    (_⊙_ : A → A → A) (e : A) {{_ : Eq A}} {{_ : AA.Identity² _⊙_ e}}
    : Set₁ where
  constructor inverse
  _<⊙>_ = forHand hand _⊙_

  field
    inv : ∀ {a} {{c : C a}} → invert a <⊙> a ≃ e

open Inverse {{...}} public using (inv)

invᴸ = inv {handᴸ}
invᴿ = inv {handᴿ}

record Inverse²
    {A : Set} {C : A → Set} (f : (a : A) {{_ : C a}} → A) (_⊙_ : A → A → A)
    (e : A) {{_ : Eq A}} {{_ : AA.Identity² _⊙_ e}}
    : Set₁ where
  constructor inverse²
  field
    {{inverseᴸ}} : Inverse handᴸ f _⊙_ e
    {{inverseᴿ}} : Inverse handᴿ f _⊙_ e

-- TODO Equivalence for switching handedness and flip _⊙_
