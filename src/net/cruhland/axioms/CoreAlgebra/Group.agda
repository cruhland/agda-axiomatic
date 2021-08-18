open import net.cruhland.axioms.CoreAlgebra.Monoid using (Monoid)

module net.cruhland.axioms.CoreAlgebra.Group (G : Set) (M : Monoid G) where

import net.cruhland.axioms.AbstractAlgebra as AA

open import net.cruhland.axioms.Eq as Eq using (_≃_; sym)
open import net.cruhland.models.Function using (const)
open import net.cruhland.models.Logic using (⊤)
open Eq.≃-Reasoning

private open module M = Monoid M using (_⊙_; identity)

record Group : Set₁ where
  field
    invert_ : G → G
    {{is-inverse}} : AA.Inverse² invert_ (const ⊤) (_⊙_) (identity)

  -- Group properties
  instance
    -- invert_ is well-defined.
    inverse-substitutive : AA.Substitutive₁ {A = G} invert_ _≃_ _≃_
    inverse-substitutive = AA.substitutive₁ λ {x → helper x}
      where
        helper : {a : G} → {b : G} → (a ≃ b) → (invert a ≃ invert b)
        helper {a} {b} x =
          begin
            invert a
          ≃˘⟨ AA.ident ⟩
            (invert a) ⊙ identity
          ≃˘⟨ AA.subst₂ AA.inv ⟩
            invert a ⊙ (b ⊙ invert b)
          ≃˘⟨ AA.assoc ⟩
            (invert a ⊙ b ) ⊙ invert b
          ≃⟨ AA.subst₂ ( AA.subst₂ (sym x) ) ⟩
            (invert a ⊙ a ) ⊙ invert b
          ≃⟨ AA.subst₂ AA.inv ⟩
            identity ⊙ invert b
          ≃⟨ AA.ident ⟩
            invert b
          ∎
          
open Group public
