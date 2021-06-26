module net.cruhland.axioms.Sign where

import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq using (_≃_; _≄_; Eq)
open import net.cruhland.models.Function using (_⟨→⟩_)

record Positivity {A : Set} {{_ : Eq A}} (zero : A) : Set₁ where
  field
    Positive : A → Set
    {{substitutive}} : AA.Substitutive₁ Positive _≃_ _⟨→⟩_
    pos≄0 : ∀ {a} → Positive a → a ≄ zero

open Positivity {{...}} public using (pos≄0; Positive)

{-# DISPLAY Positivity.Positive _ x = Positive x #-}

record Negativity {A : Set} {{_ : Eq A}} (zero : A) : Set₁ where
  field
    Negative : A → Set
    {{substitutive}} : AA.Substitutive₁ Negative _≃_ _⟨→⟩_
    neg≄0 : ∀ {a} → Negative a → a ≄ zero

open Negativity {{...}} public using (neg≄0; Negative)

{-# DISPLAY Negativity.Negative _ x = Negative x #-}
