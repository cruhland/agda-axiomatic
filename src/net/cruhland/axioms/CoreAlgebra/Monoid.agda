module net.cruhland.axioms.CoreAlgebra.Monoid where

import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_; Eq)
  
record Monoid (G : Set) {{_ : Eq G}} : Set₁ where
  infix 7 _⊙_
  field
    _⊙_ : G → G → G
    identity : G

    -- properties of composition
    {{⊙-substitutive}} : AA.Substitutive² {A = G} _⊙_ _≃_ _≃_  -- Eq subst with ⊙
    {{⊙-associative}} : AA.Associative {A = G} _⊙_

    -- proof of identity
    {{is-identity}} : AA.Identity² {A = G} _⊙_ identity

open Monoid {{...}} public using (_⊙_; identity)


