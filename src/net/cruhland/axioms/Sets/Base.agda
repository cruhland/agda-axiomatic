module net.cruhland.axioms.Sets.Base where

open import Level using (_⊔_; Level; Setω) renaming (suc to lsuc)
open import net.cruhland.models.Logic using (¬_; _↔_)

-- Export standard library definitions
open import Relation.Binary public using (Setoid)
open Setoid public using () renaming (Carrier to El)

variable
  σ₁ σ₂ α β : Level
  S : Setoid σ₁ σ₂

record SetAxioms : Setω where
  infix 5 _∈_ _∉_

  field
    PSet : Setoid σ₁ σ₂ → ∀ α → Set (σ₁ ⊔ σ₂ ⊔ lsuc α)
    _∈_ : El S → PSet S α → Set α

    PSet-cong :
      {S : Setoid σ₁ σ₂} {x y : El S} {A : PSet S α} →
        let open Setoid S using (_≈_) in x ≈ y → x ∈ A ↔ y ∈ A

  _∉_ : El S → PSet S α → Set α
  x ∉ A = ¬ (x ∈ A)
