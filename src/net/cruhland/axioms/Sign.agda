import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq using (_≃_; _≄_; Eq)
open import net.cruhland.axioms.Operators as Op using (_+_; -_)
open import net.cruhland.models.Function using (_⟨→⟩_)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Sign where

record Positivity (A : Set) {{_ : Eq A}} {{_ : FromNatLiteral A}} : Set₁ where
  field
    Positive : A → Set
    {{substitutive}} : AA.Substitutive₁ Positive _≃_ _⟨→⟩_
    pos≄0 : ∀ {a} → Positive a → a ≄ 0

open Positivity {{...}} public using (pos≄0; Positive)

{-# DISPLAY Positivity.Positive _ x = Positive x #-}

record PositivityCommon
    (A : Set)
    {{_ : Eq A}}
    {{_ : FromNatLiteral A}}
    {{_ : Op.Plus A}}
    {{_ : Positivity A}}
    : Set where
  field
    {{+-preserves-pos}} : AA.Preserves Positive _+_

record Negativity (A : Set) {{_ : Eq A}} {{_ : FromNatLiteral A}} : Set₁ where
  field
    Negative : A → Set
    {{substitutive}} : AA.Substitutive₁ Negative _≃_ _⟨→⟩_
    neg≄0 : ∀ {a} → Negative a → a ≄ 0

open Negativity {{...}} public using (neg≄0; Negative)

{-# DISPLAY Negativity.Negative _ x = Negative x #-}

record NegativityCommon
    (A : Set)
    {{_ : Eq A}}
    {{_ : FromNatLiteral A}}
    {{_ : Op.Plus A}}
    {{_ : Negativity A}}
    : Set where
  field
    {{+-preserves-neg}} : AA.Preserves Negative _+_

record Trichotomy
    (A : Set) {{_ : FromNatLiteral A}} {{_ : Eq A}}
    {{_ : Positivity A}} {{_ : Negativity A}}
    : Set where
  constructor trichotomy-intro
  field
    trichotomy :
      (x : A) → AA.ExactlyOneOfThree (x ≃ 0) (Positive x) (Negative x)

open Trichotomy {{...}} public using (trichotomy)

{-# DISPLAY Trichotomy.trichotomy _ x = trichotomy x #-}

record SignCommon
    (A : Set)
    {{_ : Eq A}}
    {{_ : FromNatLiteral A}}
    {{_ : Op.Plus A}}
    {{_ : Op.Dashᴸ A}}
    {{_ : Positivity A}}
    {{_ : Negativity A}}
    : Set where
  field
    {{positivity-common}} : PositivityCommon A
    {{negativity-common}} : NegativityCommon A
    {{sign-trichotomy}} : Trichotomy A

    neg-Positive : {x : A} → Positive x → Negative (- x)
    neg-Negative : {x : A} → Negative x → Positive (- x)

open SignCommon {{...}} public using (neg-Positive; neg-Negative)
