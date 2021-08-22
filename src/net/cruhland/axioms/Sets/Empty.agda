open import Level using (_⊔_; Level; Setω)
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Sets.Base using (SetAxioms)
import net.cruhland.axioms.Sets.Decidable as Decidable
import net.cruhland.axioms.Sets.Equality as Equality
open import net.cruhland.models.Logic using (↔-intro; _↯_; no)
open import net.cruhland.models.Setoid using (Setoid)

module net.cruhland.axioms.Sets.Empty where

-- If an empty set is being compared for equality with a nested set,
-- it needs to be lifted to the same level, so we need parameters
private
  variable
    σ₁ σ₂ : Level
    S : Setoid σ₁ σ₂

record EmptySet (SA : SetAxioms) : Setω where
  open Decidable SA using (DecMembership; ∈?-intro)
  private
    open module SE = Equality SA using (≃-intro)
  open SetAxioms SA using (_∉_; PSet)

  field
    ∅ : PSet S

  is-empty : {S : Setoid σ₁ σ₂} → PSet S → Set (σ₁ ⊔ σ₂)
  is-empty A = ∀ {x} → x ∉ A

  field
    x∉∅ : is-empty {S = S} ∅

  ∅-unique : {∅′ : PSet S} → is-empty ∅′ → ∅ ≃ ∅′
  ∅-unique x∉∅′ = ≃-intro (↔-intro (_↯ x∉∅) (_↯ x∉∅′))

  instance
    ∅-∈? : DecMembership (∅ {S = S})
    ∅-∈? = ∈?-intro (no x∉∅)
