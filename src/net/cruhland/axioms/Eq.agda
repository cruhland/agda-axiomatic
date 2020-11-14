module net.cruhland.axioms.Eq where

open import Level using (_⊔_; 0ℓ; Level) renaming (suc to sℓ)
open import net.cruhland.models.Logic using (¬_; ¬ⁱ_; ¬ⁱ-intro)

private
  variable
    α : Level
    A : Set α

record Eq (A : Set α) : Set (sℓ α) where
  infix 4 _≃_
  field
    _≃_ : A → A → Set α
    {{refl}} : ∀ {x} → x ≃ x
    sym : ∀ {x y} → x ≃ y → y ≃ x
    trans : ∀ {x y z} → x ≃ y → y ≃ z → x ≃ z

  infix 4 _≄_
  _≄_ : A → A → Set α
  x ≄ y = ¬ (x ≃ y)

open Eq {{...}} public

module _ {{eq : Eq A}} where

  ¬sym : {x y : A} → x ≄ y → y ≄ x
  ¬sym x≄y = λ y≃x → x≄y (sym y≃x)

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

infix 4 _≄ⁱ_
_≄ⁱ_ : {A : Set α} {{_ : Eq A}} → A → A → Set α
x ≄ⁱ y = ¬ⁱ (x ≃ y)

≄ⁱ-intro : {x y : A} {{_ : Eq A}} → x ≄ y → x ≄ⁱ y
≄ⁱ-intro = ¬ⁱ-intro

≄ⁱ-elim : {x y : A} {{_ : Eq A}} → x ≄ⁱ y → x ≄ y
≄ⁱ-elim = ¬ⁱ_.elim
