module net.cruhland.axioms.Sets.Pair where

open import Function using (_∘_)
open import Level using (_⊔_; Setω)
open import Relation.Binary using (DecSetoid)
open import net.cruhland.axioms.Sets.Base using (S; SetAxioms; σ₁; σ₂)
import net.cruhland.axioms.Sets.Decidable as Decidable
import net.cruhland.axioms.Sets.Equality as Equality
open import net.cruhland.models.Logic using
  ( _∨_; _∨?_; ∨-introᴸ; ∨-introᴿ; ∨-map
  ; _↔_; ↔-elimᴸ; ↔-elimᴿ; ↔-sym; ↔-trans
  ; Dec; dec-map; no; yes
  )
open import net.cruhland.models.Setoid using (El; Setoid)

module PairDef (SA : SetAxioms) where
  open SetAxioms SA using (_∈_; PSet)

  is-pair : {S : Setoid σ₁ σ₂} → El S → El S → PSet S σ₂ → Set (σ₁ ⊔ σ₂)
  is-pair {S = S} a b A = ∀ {x} → x ∈ A ↔ a ≈ x ∨ b ≈ x
    where open Setoid S using (_≈_)

record PairSet (SA : SetAxioms) : Setω where
  open Decidable SA using (DecMembership; ∈?-intro)
  open Equality SA using (_≃_; ≃-intro)
  open SetAxioms SA using (_∈_; PSet)
  open PairDef SA using (is-pair)

  field
    pair : {S : Setoid σ₁ σ₂} → El S → El S → PSet S σ₂
    x∈pab↔a≈x∨b≈x :
      {S : Setoid σ₁ σ₂} {a b : El S} → is-pair {S = S} a b (pair a b)

  module _ {S : Setoid σ₁ σ₂} where
    open Setoid S using (_≈_) renaming (refl to ≈-refl; sym to ≈-sym)

    x∈pab-elimᴸ : {x a b : El S} → x ∈ pair {S = S} a b → x ≈ a ∨ x ≈ b
    x∈pab-elimᴸ = ∨-map ≈-sym ≈-sym ∘ (↔-elimᴸ x∈pab↔a≈x∨b≈x)

    x∈pab-elimᴿ : {x a b : El S} → x ∈ pair {S = S} a b → a ≈ x ∨ b ≈ x
    x∈pab-elimᴿ = ↔-elimᴸ x∈pab↔a≈x∨b≈x

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

  instance
    pair-∈? :
      {{DS : DecSetoid σ₁ σ₂}} →
        ∀ {a b} → DecMembership (pair {S = DecSetoid.setoid DS} a b)
    pair-∈? {{DS}} {a} {b} =
      ∈?-intro (λ {x} → dec-map x∈pab-intro x∈pab-elimᴿ (a ≟ x ∨? b ≟ x))
        where open DecSetoid DS using (_≈_; _≟_)
