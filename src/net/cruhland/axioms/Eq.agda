open import Level using (_⊔_) renaming (suc to sℓ)
open import net.cruhland.models.Logic using (⊥; ¬_; ¬-intro; contrapositive)

module net.cruhland.axioms.Eq where

module _ {α β} {A : Set α} (_~_ : A → A → Set β) where

  record Reflexive : Set (α ⊔ β) where
    constructor reflexive
    field
      refl : ∀ {a} → a ~ a

  open Reflexive {{...}} public using (refl)

  record Symmetric : Set (α ⊔ β) where
    constructor symmetric
    field
      sym : ∀ {a b} → a ~ b → b ~ a

  open Symmetric {{...}} public using (sym)

  record Transitive : Set (α ⊔ β) where
    constructor transitive
    field
      trans : ∀ {a b c} → a ~ b → b ~ c → a ~ c

  open Transitive {{...}} public using (trans)

record Eq {α} (A : Set α) : Set (sℓ α) where
  constructor equivalence
  infix 4 _≃_
  field
    _≃_ : A → A → Set α
    {{≃-reflexive}} : Reflexive _≃_
    {{≃-symmetric}} : Symmetric _≃_
    {{≃-transitive}} : Transitive _≃_

open Eq {{...}} public

{-# DISPLAY Eq._≃_ _ x y = x ≃ y #-}

module _ {α} {A : Set α} {{eq : Eq A}} where

  infix 4 _≄_
  _≄_ : A → A → Set α
  x ≄ y = ¬ (x ≃ y)

  ≄-intro : {x y : A} → (x ≃ y → ⊥) → x ≄ y
  ≄-intro = ¬-intro

  instance
    ≄-symmetric : Symmetric _≄_
    ≄-symmetric = symmetric ≄-sym
      where
        ≄-sym : {x y : A} → x ≄ y → y ≄ x
        ≄-sym x≄y = contrapositive sym x≄y

  module ≃-Reasoning where

    infix 3 _∎
    infixr 2 _≃⟨⟩_ step-≃ step-≃˘
    infix 1 begin_

    begin_ : {x y : A} → x ≃ y → x ≃ y
    begin x≃y = x≃y

    _≃⟨⟩_ : (x {y} : A) → x ≃ y → x ≃ y
    _ ≃⟨⟩ x≃y = x≃y

    step-≃ : (x {y z} : A) → y ≃ z → x ≃ y → x ≃ z
    step-≃ _ y≃z x≃y = trans x≃y y≃z

    step-≃˘ : (x {y z} : A) → y ≃ z → y ≃ x → x ≃ z
    step-≃˘ _ y≃z y≃x = trans (sym y≃x) y≃z

    _∎ : (x : A) → x ≃ x
    _ ∎ = refl

    syntax step-≃ x y≃z x≃y = x ≃⟨ x≃y ⟩ y≃z
    syntax step-≃˘ x y≃z y≃x = x ≃˘⟨ y≃x ⟩ y≃z
