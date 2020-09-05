module net.cruhland.axioms.Sets.Base where

open import Level using (_⊔_; 0ℓ; Level; Setω) renaming (suc to sℓ)
open import net.cruhland.models.Logic using (¬_)
open import net.cruhland.models.Setoid using (El; Setoid; Setoid₀)

variable
  σ₁ σ₂ α β χ : Level
  S : Setoid σ₁ σ₂

record SetAxioms : Setω where
  infix 4 _∈_ _∉_

  field
    PSet : Setoid σ₁ σ₂ → ∀ α → Set (σ₁ ⊔ σ₂ ⊔ sℓ α)
    _∈_ : El S → PSet S α → Set α

    PSet-cong :
      {S : Setoid σ₁ σ₂} {x y : El S} {A : PSet S α} →
        let open Setoid S using (_≈_) in x ≈ y → x ∈ A → y ∈ A

  _∉_ : El S → PSet S α → Set α
  x ∉ A = ¬ (x ∈ A)

  PSet₀ : Setoid₀ → Set (sℓ 0ℓ)
  PSet₀ S = PSet S 0ℓ
