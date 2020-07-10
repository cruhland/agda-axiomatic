module net.cruhland.axiomatic.Sets.Base where

open import Level using (_⊔_; Setω) renaming (suc to lsuc)
open import net.cruhland.axiomatic.Logic using (¬_; _↔_)

-- Export standard library definitions
open import Relation.Binary public using (Setoid)
open Setoid public using () renaming (Carrier to El)

record SetAxioms : Setω where
  infix 5 _∈_ _∉_

  field
    PSet : ∀ {σ₁ σ₂} → Setoid σ₁ σ₂ → ∀ α → Set (σ₁ ⊔ σ₂ ⊔ lsuc α)
    _∈_ : ∀ {σ₁ σ₂ α} {S : Setoid σ₁ σ₂} → El S → PSet S α → Set α

    PSet-cong :
      ∀ {σ₁ σ₂ α} {S : Setoid σ₁ σ₂} {x y : El S} {A : PSet S α} →
        let open Setoid S using (_≈_) in x ≈ y → x ∈ A ↔ y ∈ A

  _∉_ : ∀ {α₁ α₂ β} {A : Setoid α₁ α₂} → El A → PSet A β → Set β
  x ∉ A = ¬ (x ∈ A)
