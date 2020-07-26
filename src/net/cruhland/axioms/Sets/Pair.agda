module net.cruhland.axioms.Sets.Pair where

open import Level using (_⊔_; Setω)
open import net.cruhland.axioms.Sets.Base using
  (α; El; S; SetAxioms; Setoid; σ₁; σ₂)
open import net.cruhland.models.Logic using (_∨_; _↔_)

module PairDef (SA : SetAxioms) where
  open SetAxioms SA using (_∈_; PSet)

  is-pair : {S : Setoid σ₁ σ₂} → El S → El S → PSet S α → Set (σ₁ ⊔ σ₂ ⊔ α)
  is-pair {S = S} a b A = ∀ {x} → x ∈ A ↔ x ≈ a ∨ x ≈ b
    where open Setoid S using (_≈_)

record PairSet (SA : SetAxioms) : Setω where
  open SetAxioms SA using (_∈_; PSet)
  open PairDef SA using (is-pair)

  field
    pair : El S → El S → PSet S α
    x∈pab↔x≈a∨x≈b :
      {S : Setoid σ₁ σ₂} {a b : El S} → is-pair {α = α} {S} a b (pair a b)
