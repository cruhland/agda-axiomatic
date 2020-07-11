module net.cruhland.axiomatic.Sets.Union where

open import Level using (_⊔_; Setω)
open import net.cruhland.axiomatic.Logic using (_∨_; _↔_)
open import net.cruhland.axiomatic.Sets.Base using
  (α; β; S; SetAxioms; Setoid; σ₁; σ₂)

record PairwiseUnion (SA : SetAxioms) : Setω where
  open SetAxioms SA using (_∈_; PSet)

  field
    _∪_ : PSet S α → PSet S β → PSet S (α ⊔ β)

  is-union :
    {S : Setoid σ₁ σ₂} → PSet S α → PSet S β → PSet S (α ⊔ β) → Set (σ₁ ⊔ α ⊔ β)
  is-union A B A∪B = ∀ {x} → x ∈ A∪B ↔ x ∈ A ∨ x ∈ B

  field
    x∈A∪B↔x∈A∨x∈B : {A : PSet S α} {B : PSet S β} → is-union A B (A ∪ B)
