module net.cruhland.axioms.AbstractAlgebra.Inverse where

open import net.cruhland.axioms.AbstractAlgebra.Base using
  (forHand; Hand; handᴸ; handᴿ)
open import net.cruhland.axioms.AbstractAlgebra.Reductive using
  (Identity₂; id₂-elem)
open import net.cruhland.axioms.Eq as Eq using (_≃_; Eq)
open import net.cruhland.models.Function using
  (ConstrainableFn; toConstrainedFn)

record Inverse (hand : Hand) {A F : Set} {{_ : Eq A}} (f : F) : Set₁ where
  constructor inverse
  field
    {_⊙_} : A → A → A
    {{identity}} : Identity₂ _⊙_
    {{cf}} : ConstrainableFn F

  open ConstrainableFn cf using (C)
  invert = toConstrainedFn f
  _<⊙>_ = forHand hand _⊙_

  field
    inv : ∀ {a} {{c : C a}} → invert a <⊙> a ≃ id₂-elem

open Inverse {{...}} public using (inv)

invᴸ = inv {handᴸ}
invᴿ = inv {handᴿ}

-- TODO Equivalence for switching handedness and flip _⊙_
