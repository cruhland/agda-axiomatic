module net.cruhland.axioms.Sets.Empty where

open import Function using (_∘_)
open import Level using (_⊔_; Setω)
open import net.cruhland.axioms.Sets.Base using (α; S; SetAxioms; σ₁; σ₂)
import net.cruhland.axioms.Sets.Decidable as Decidable
import net.cruhland.axioms.Sets.Equality as Equality
open import net.cruhland.models.Logic using (⊥-elim; _↔_; ↔-intro; Dec; no)
open import net.cruhland.models.Setoid using (El; Setoid; Setoid₀)

record EmptySet (SA : SetAxioms) : Setω where
  open Decidable SA using (DecMembership; ∈?-intro)
  open Equality SA using (_≃_; ≃-intro)
  open SetAxioms SA using (_∈_; _∉_; PSet)

  field
    ∅ : PSet S α

  is-empty : {S : Setoid σ₁ σ₂} → PSet S α → Set (σ₁ ⊔ α)
  is-empty A = ∀ {x} → x ∉ A

  field
    x∉∅ : is-empty {α = α} {S} ∅

  ∅-unique : {∅′ : PSet S α} → is-empty ∅′ → ∅ ≃ ∅′
  ∅-unique x∉∅′ = ≃-intro (↔-intro (⊥-elim ∘ x∉∅) (⊥-elim ∘ x∉∅′))

  instance
    ∅-∈? : {S : Setoid₀} → DecMembership (∅ {S = S})
    ∅-∈? = ∈?-intro (no x∉∅)
