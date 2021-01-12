module net.cruhland.axioms.Sets.Difference where

open import Level using (Setω)
open import net.cruhland.axioms.Sets.Base using (SetAxioms)
import net.cruhland.axioms.Sets.Decidable as Decidable
open import net.cruhland.models.Function using (_∘_)
open import net.cruhland.models.Logic using
  (_∧_; _∧?_; ∧-elimᴸ; ∧-elimᴿ; _↔_; ↔-elimᴸ; ↔-elimᴿ; ¬?; curry; Dec; dec-map)
open import net.cruhland.models.Setoid using (Setoid₀)

private
  variable
    S : Setoid₀

record Difference (SA : SetAxioms) : Setω where
  open Decidable SA using (_∈?_; DecMembership; ∈?-intro)
  open SetAxioms SA using (_∈_; _∉_; PSet₀)

  infixl 7 _∖_

  field
    _∖_ : PSet₀ S → PSet₀ S → PSet₀ S

  is-diff : PSet₀ S → PSet₀ S → PSet₀ S → Set
  is-diff A B A∖B = ∀ {x} → x ∈ A∖B ↔ x ∈ A ∧ x ∉ B

  field
    x∈A∖B↔x∈A∧x∉B : {A B : PSet₀ S} → is-diff A B (A ∖ B)

  module _ {A B : PSet₀ S} where
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
