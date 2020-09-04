module net.cruhland.axioms.Sets.Base where

open import Level using (_⊔_; 0ℓ; Level; Setω) renaming (suc to sℓ)
open import net.cruhland.models.Logic using (¬_)

-- Export standard library definitions
open import Relation.Binary public using (DecSetoid; module DecSetoid; Setoid)
open Setoid public using () renaming (Carrier to El)

Setoid₀ : Set (sℓ 0ℓ)
Setoid₀ = Setoid 0ℓ 0ℓ

DecSetoid₀ : Set (sℓ 0ℓ)
DecSetoid₀ = DecSetoid 0ℓ 0ℓ

variable
  σ₁ σ₂ α β χ : Level
  S : Setoid σ₁ σ₂

record SetAxioms : Setω where
  infix 4 _∈_ _∉_

  field
    PSet : ∀ {σ₁ σ₂} → Setoid σ₁ σ₂ → ∀ α → Set (σ₁ ⊔ σ₂ ⊔ sℓ α)
    _∈_ : {S : Setoid σ₁ σ₂} → El S → PSet S α → Set α

    PSet-cong :
      {S : Setoid σ₁ σ₂} {x y : El S} {A : PSet S α} →
        let open Setoid S using (_≈_) in x ≈ y → x ∈ A → y ∈ A

  _∉_ : El S → PSet S α → Set α
  x ∉ A = ¬ (x ∈ A)

  PSet₀ : Setoid 0ℓ 0ℓ → Set (sℓ 0ℓ)
  PSet₀ S = PSet S 0ℓ
