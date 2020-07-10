module net.cruhland.axiomatic.Sets.Empty where

open import Function using (_∘_)
open import Level using (_⊔_; Setω)
open import net.cruhland.axiomatic.Logic using (⊥-elim; _↔_; ↔-intro)
open import net.cruhland.axiomatic.Sets.Base using (SetAxioms; Setoid)
import net.cruhland.axiomatic.Sets.Equality as Equality

record EmptySet (SA : SetAxioms) : Setω where
  open Equality SA using (_≗_; ≗-intro)
  open SetAxioms SA using (_∈_; _∉_; PSet)

  field
    ∅ : ∀ {σ₁ σ₂ α} {S : Setoid σ₁ σ₂} → PSet S α

  is-empty : ∀ {σ₁ σ₂ α} {S : Setoid σ₁ σ₂} → PSet S α → Set (σ₁ ⊔ α)
  is-empty A = ∀ {x} → x ∉ A

  field
    x∉∅ : ∀ {σ₁ σ₂ α} {S : Setoid σ₁ σ₂} → is-empty {α = α} {S} ∅

  ∅-unique :
    ∀ {σ₁ σ₂ α} {S : Setoid σ₁ σ₂} {∅′ : PSet S α} → is-empty ∅′ → ∅ ≗ ∅′
  ∅-unique x∉∅′ = ≗-intro (↔-intro (⊥-elim ∘ x∉∅) (⊥-elim ∘ x∉∅′))
