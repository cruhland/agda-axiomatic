module net.cruhland.axioms.Eq where

open import net.cruhland.models.Logic using (¬_)

record Eq (A : Set) : Set₁ where
  infix 4 _≃_
  field
    _≃_ : A → A → Set
    {{refl}} : ∀ {x} → x ≃ x
    sym : ∀ {x y} → x ≃ y → y ≃ x
    trans : ∀ {x y z} → x ≃ y → y ≃ z → x ≃ z

  infix 4 _≄_
  _≄_ : A → A → Set
  x ≄ y = ¬ (x ≃ y)

  -- An alternative form of inequality for use in "instance
  -- arguments".  Agda doesn't allow standard inequality as the type
  -- of instance arguments, because it's a function type with an
  -- explicit parameter (only implicit and instance parameters are
  -- allowed in instance types).
  infix 4 _≄ⁱ_
  field
    _≄ⁱ_ : A → A → Set
    ≄ⁱ-elim : ∀ {x y} {{i : x ≄ⁱ y}} → x ≄ y

open Eq {{...}} public

¬sym : {A : Set} {{_ : Eq A}} {x y : A} → x ≄ y → y ≄ x
¬sym x≄y = λ y≃x → x≄y (sym y≃x)

module ≃-Reasoning where

  infix 3 _∎
  infixr 2 _≃⟨⟩_ step-≃ step-≃˘
  infix 1 begin_

  begin_ : {A : Set} {{_ : Eq A}} {x y : A} → x ≃ y → x ≃ y
  begin x≃y = x≃y

  _≃⟨⟩_ : {A : Set} {{_ : Eq A}} (x {y} : A) → x ≃ y → x ≃ y
  _ ≃⟨⟩ x≃y = x≃y

  step-≃ : {A : Set} {{_ : Eq A}} (x {y z} : A) → y ≃ z → x ≃ y → x ≃ z
  step-≃ _ y≃z x≃y = trans x≃y y≃z

  step-≃˘ : {A : Set} {{_ : Eq A}} (x {y z} : A) → y ≃ z → y ≃ x → x ≃ z
  step-≃˘ _ y≃z y≃x = trans (sym y≃x) y≃z

  _∎ : {A : Set} {{_ : Eq A}} (x : A) → x ≃ x
  _ ∎ = refl

  syntax step-≃ x y≃z x≃y = x ≃⟨ x≃y ⟩ y≃z
  syntax step-≃˘ x y≃z y≃x = x ≃˘⟨ y≃x ⟩ y≃z
