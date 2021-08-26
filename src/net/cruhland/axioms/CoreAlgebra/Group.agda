module net.cruhland.axioms.CoreAlgebra.Group where

open import net.cruhland.axioms.CoreAlgebra.Monoid
open import net.cruhland.axioms.Eq as Eq using (_≃_; Eq)

import net.cruhland.axioms.AbstractAlgebra as AA

open import net.cruhland.models.Function using (const)
open import net.cruhland.models.Logic using (⊤)
open Eq.≃-Reasoning



-- is there a way to make pass and an explicit Monoid if necessary?
record Group (G : Set) {{_ : Eq G}} {{_ : Monoid G}} : Set₁ where
  field
    invert : G → G
    {{is-inverse}} : AA.Inverse² {A = G} (AA.tc₁ invert) (_⊙_) (identity)

  -- Group properties
  instance
    -- invert is well-defined.
    inverse-substitutive : AA.Substitutive₁ {A = G} invert _≃_ _≃_
    inverse-substitutive = AA.substitutive₁ helper
      where
        helper : {a b : G} → (a ≃ b) → (invert a ≃ invert b)
        helper {a} {b} a≃b =
          begin
            invert a
          ≃˘⟨ AA.ident ⟩
            (invert a) ⊙ identity
          ≃˘⟨ AA.subst₂ AA.inv ⟩
            invert a ⊙ (b ⊙ invert b)
          ≃˘⟨ AA.assoc ⟩
            (invert a ⊙ b ) ⊙ invert b
          ≃˘⟨ AA.subst₂ ( AA.subst₂ (a≃b) ) ⟩
            (invert a ⊙ a ) ⊙ invert b
          ≃⟨ AA.subst₂ AA.inv ⟩
            identity ⊙ invert b
          ≃⟨ AA.ident ⟩
            invert b
          ∎
          
open Group {{...}} public using (invert)
