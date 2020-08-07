module net.cruhland.axioms.Sets.Pair where

open import Function using (_∘_)
open import Level using (_⊔_; Setω)
open import net.cruhland.axioms.Sets.Base using
  (El; S; SetAxioms; Setoid; σ₁; σ₂)
import net.cruhland.axioms.Sets.Equality as Equality
open import net.cruhland.models.Logic using
  (_∨_; ∨-introᴸ; ∨-introᴿ; _↔_; ↔-elimᴸ; ↔-elimᴿ; ↔-sym; ↔-trans)

module PairDef (SA : SetAxioms) where
  open SetAxioms SA using (_∈_; PSet)

  is-pair : {S : Setoid σ₁ σ₂} → El S → El S → PSet S σ₂ → Set (σ₁ ⊔ σ₂)
  is-pair {S = S} a b A = ∀ {x} → x ∈ A ↔ a ≈ x ∨ b ≈ x
    where open Setoid S using (_≈_)

record PairSet (SA : SetAxioms) : Setω where
  open Equality SA using (_≃_; ≃-intro)
  open SetAxioms SA using (_∈_; PSet)
  open PairDef SA using (is-pair)

  field
    pair : {S : Setoid σ₁ σ₂} → El S → El S → PSet S σ₂
    x∈pab↔a≈x∨b≈x :
      {S : Setoid σ₁ σ₂} {a b : El S} → is-pair {S = S} a b (pair a b)

  module _ {S : Setoid σ₁ σ₂} where
    open Setoid S using (_≈_) renaming (refl to ≈-refl)

    x∈pab-elim : {x a b : El S} → x ∈ pair {S = S} a b → a ≈ x ∨ b ≈ x
    x∈pab-elim = ↔-elimᴸ x∈pab↔a≈x∨b≈x

    x∈pab-intro : {x a b : El S} → a ≈ x ∨ b ≈ x → x ∈ pair {S = S} a b
    x∈pab-intro = ↔-elimᴿ x∈pab↔a≈x∨b≈x

    x∈pab-introᴸ : {x a b : El S} → a ≈ x → x ∈ pair {S = S} a b
    x∈pab-introᴸ = x∈pab-intro ∘ ∨-introᴸ

    x∈pab-introᴿ : {x a b : El S} → b ≈ x → x ∈ pair {S = S} a b
    x∈pab-introᴿ = x∈pab-intro ∘ ∨-introᴿ

    a∈pab : {a b : El S} → a ∈ pair {S = S} a b
    a∈pab = x∈pab-introᴸ ≈-refl

    b∈pab : {a b : El S} → b ∈ pair {S = S} a b
    b∈pab = x∈pab-introᴿ ≈-refl

    pair-unique : {A : PSet S σ₂} {a b : El S} → is-pair a b A → pair a b ≃ A
    pair-unique x∈A↔x≈a∨x≈b =
      ≃-intro (↔-trans x∈pab↔a≈x∨b≈x (↔-sym x∈A↔x≈a∨x≈b))
