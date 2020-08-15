module net.cruhland.axioms.Sets.Complement where

open import Level using (_⊔_; Setω)
open import net.cruhland.axioms.Sets.Base using
  (α; σ₁; σ₂; El; S; SetAxioms; Setoid)
import net.cruhland.axioms.Sets.Decidable as Decidable
open import net.cruhland.models.Logic using
  (_↔_; ↔-elimᴸ; ↔-elimᴿ; ¬?; Dec; dec-map)

record Complement (SA : SetAxioms) : Setω where
  open Decidable SA using (_∈?_; DecMembership; ∈?-intro)
  open SetAxioms SA using (_∈_; _∉_; PSet)

  field
    ∁ : PSet S α → PSet S α

  is-complement : {S : Setoid σ₁ σ₂} → PSet S α → PSet S α → Set (σ₁ ⊔ α)
  is-complement A ∁A = ∀ {x} → x ∈ ∁A ↔ x ∉ A

  field
    x∈∁A↔x∉A : {A : PSet S α} → is-complement A (∁ A)

  x∈∁A-elim : {S : Setoid σ₁ σ₂} {A : PSet S α} → ∀ {x} → x ∈ ∁ A → x ∉ A
  x∈∁A-elim = ↔-elimᴸ x∈∁A↔x∉A

  x∈∁A-intro : {S : Setoid σ₁ σ₂} {A : PSet S α} → ∀ {x} → x ∉ A → x ∈ ∁ A
  x∈∁A-intro = ↔-elimᴿ x∈∁A↔x∉A

  instance
    ∁-∈? : {A : PSet S α} {{_ : DecMembership A}} → DecMembership (∁ A)
    ∁-∈? {A = A} = ∈?-intro (λ {x} → dec-map x∈∁A-intro x∈∁A-elim (¬? (x ∈? A)))
