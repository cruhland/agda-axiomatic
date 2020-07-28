module net.cruhland.axioms.Sets.Pair where

open import Level using (_⊔_; Setω)
open import net.cruhland.axioms.Sets.Base using
  (α; El; S; SetAxioms; Setoid; σ₁; σ₂)
import net.cruhland.axioms.Sets.Equality as Equality
open import net.cruhland.models.Logic using
  (_∨_; _↔_; ↔-elimᴸ; ↔-elimᴿ; ↔-sym; ↔-trans)

module PairDef (SA : SetAxioms) where
  open SetAxioms SA using (_∈_; PSet)

  is-pair : {S : Setoid σ₁ σ₂} → El S → El S → PSet S α → Set (σ₁ ⊔ σ₂ ⊔ α)
  is-pair {S = S} a b A = ∀ {x} → x ∈ A ↔ x ≈ a ∨ x ≈ b
    where open Setoid S using (_≈_)

record PairSet (SA : SetAxioms) : Setω where
  open Equality SA using (_≃_; ≃-intro)
  open SetAxioms SA using (_∈_; PSet)
  open PairDef SA using (is-pair)

  field
    pair : El S → El S → PSet S α
    x∈pab↔x≈a∨x≈b :
      {S : Setoid σ₁ σ₂} {a b : El S} → is-pair {α = α} {S} a b (pair a b)

  module _ {S : Setoid σ₁ σ₂} where
    open Setoid S using (_≈_)

    x∈pab-elim : {x a b : El S} → x ∈ pair {S = S} {α} a b → x ≈ a ∨ x ≈ b
    x∈pab-elim = ↔-elimᴸ x∈pab↔x≈a∨x≈b

    x∈pab-intro : {x a b : El S} → x ≈ a ∨ x ≈ b → x ∈ pair {S = S} {α} a b
    x∈pab-intro = ↔-elimᴿ x∈pab↔x≈a∨x≈b

    pair-unique : {A : PSet S α} {a b : El S} → is-pair a b A → pair a b ≃ A
    pair-unique x∈A↔x≈a∨x≈b =
      ≃-intro (↔-trans x∈pab↔x≈a∨x≈b (↔-sym x∈A↔x≈a∨x≈b))
