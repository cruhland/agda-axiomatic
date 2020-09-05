module net.cruhland.axioms.Sets.Difference where

open import Function using (_∘_)
open import Level using (_⊔_; Setω)
open import net.cruhland.axioms.Sets.Base using (α; β; σ₁; σ₂; S; SetAxioms)
import net.cruhland.axioms.Sets.Decidable as Decidable
open import net.cruhland.models.Logic using
  (_∧_; _∧?_; ∧-elimᴸ; ∧-elimᴿ; _↔_; ↔-elimᴸ; ↔-elimᴿ; ¬?; curry; Dec; dec-map)
open import net.cruhland.models.Setoid using (Setoid)

record Difference (SA : SetAxioms) : Setω where
  open Decidable SA using (_∈?_; DecMembership; ∈?-intro)
  open SetAxioms SA using (_∈_; _∉_; PSet)

  infixl 7 _∖_

  field
    _∖_ : PSet S α → PSet S β → PSet S (α ⊔ β)

  is-diff :
    {S : Setoid σ₁ σ₂} → PSet S α → PSet S β → PSet S (α ⊔ β) → Set (σ₁ ⊔ α ⊔ β)
  is-diff A B A∖B = ∀ {x} → x ∈ A∖B ↔ x ∈ A ∧ x ∉ B

  field
    x∈A∖B↔x∈A∧x∉B : {A : PSet S α} {B : PSet S β} → is-diff A B (A ∖ B)

  module _ {S : Setoid σ₁ σ₂} {A : PSet S α} {B : PSet S β} where
    x∈A∖B-elim : ∀ {x} → x ∈ A ∖ B → x ∈ A ∧ x ∉ B
    x∈A∖B-elim = ↔-elimᴸ x∈A∖B↔x∈A∧x∉B

    x∈A∖B-elimᴸ : ∀ {x} → x ∈ A ∖ B → x ∈ A
    x∈A∖B-elimᴸ = ∧-elimᴸ ∘ x∈A∖B-elim

    x∈A∖B-elimᴿ : ∀ {x} → x ∈ A ∖ B → x ∉ B
    x∈A∖B-elimᴿ = ∧-elimᴿ ∘ x∈A∖B-elim

    x∈A∖B-intro : ∀ {x} → x ∈ A ∧ x ∉ B → x ∈ A ∖ B
    x∈A∖B-intro = ↔-elimᴿ x∈A∖B↔x∈A∧x∉B

    x∈A∖B-intro₂ : ∀ {x} → x ∈ A → x ∉ B → x ∈ A ∖ B
    x∈A∖B-intro₂ = curry x∈A∖B-intro

    instance
      ∖-∈? :
        {{_ : DecMembership A}} {{_ : DecMembership B}} → DecMembership (A ∖ B)
      ∖-∈? =
        ∈?-intro λ {x} → dec-map x∈A∖B-intro x∈A∖B-elim (x ∈? A ∧? ¬? (x ∈? B))
