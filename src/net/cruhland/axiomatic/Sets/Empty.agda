module net.cruhland.axiomatic.Sets.Empty where

open import Function using (_∘_)
open import Level using (_⊔_; Setω)
open import net.cruhland.axiomatic.Logic using (⊥-elim; _↔_; ↔-intro)
open import net.cruhland.axiomatic.Sets.Base using
  (α; S; SetAxioms; Setoid; σ₁; σ₂)
import net.cruhland.axiomatic.Sets.Equality as Equality

record EmptySet (SA : SetAxioms) : Setω where
  open Equality SA using (_≗_; ≗-intro)
  open SetAxioms SA using (_∈_; _∉_; PSet)

  field
    ∅ : PSet S α

  is-empty : {S : Setoid σ₁ σ₂} → PSet S α → Set (σ₁ ⊔ α)
  is-empty A = ∀ {x} → x ∉ A

  field
    x∉∅ : is-empty {α = α} {S} ∅

  ∅-unique : {∅′ : PSet S α} → is-empty ∅′ → ∅ ≗ ∅′
  ∅-unique x∉∅′ = ≗-intro (↔-intro (⊥-elim ∘ x∉∅) (⊥-elim ∘ x∉∅′))
