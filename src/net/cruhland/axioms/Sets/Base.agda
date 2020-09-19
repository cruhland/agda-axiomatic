module net.cruhland.axioms.Sets.Base where

open import Level using (_⊔_; 0ℓ; Level; Setω) renaming (suc to sℓ)
open import net.cruhland.models.Logic using (¬_)
open import net.cruhland.models.Setoid using (El; Setoid; Setoid₀)

-- Because we want to have sets contain other sets, the first level
-- parameter of the Setoid argument must be allowed to be greater than
-- 0ℓ. And the Predicate model requires the σ₁ parameter to be in the
-- result type. Also, for doubly-nested sets, the second parameter
-- also has to vary.
private
  variable
    σ₁ σ₂ : Level

record SetAxioms : Setω where
  infix 4 _∈_ _∉_

  field
    PSet : Setoid σ₁ σ₂ → Set (σ₁ ⊔ sℓ σ₂ ⊔ sℓ 0ℓ)
    _∈_ : {S : Setoid σ₁ σ₂} → El S → PSet S → Set σ₂

    PSet-cong :
      {S : Setoid σ₁ σ₂} {x y : El S} {A : PSet S} →
        let open Setoid S using (_≈_) in x ≈ y → x ∈ A → y ∈ A

  _∉_ : {S : Setoid σ₁ σ₂} → El S → PSet S → Set σ₂
  x ∉ A = ¬ (x ∈ A)

  PSet₀ : Setoid₀ → Set₁
  PSet₀ = PSet
