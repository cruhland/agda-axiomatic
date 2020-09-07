module net.cruhland.models.Setoid where

open import Level using (0ℓ) renaming (suc to sℓ)

-- Export standard library definitions
open import Function.Equivalence public
  using (Equivalence; ⇔-setoid) renaming (id to equivalence-id)
open import Function.Equality public
  using (_⟶_; _⇨_; _⟨$⟩_; cong; Π) renaming (const to SPred-const)
open import Relation.Binary public using (DecSetoid; module DecSetoid; Setoid)
open Setoid public using () renaming (Carrier to El)

Setoid₀ : Set (sℓ 0ℓ)
Setoid₀ = Setoid 0ℓ 0ℓ

DecSetoid₀ : Set (sℓ 0ℓ)
DecSetoid₀ = DecSetoid 0ℓ 0ℓ

SPred₀ : Setoid₀ → Set (sℓ 0ℓ)
SPred₀ S = S ⟶ ⇔-setoid 0ℓ

SRel₀ : Setoid₀ → Setoid₀ → Set (sℓ 0ℓ)
SRel₀ S T = S ⟶ T ⇨ ⇔-setoid 0ℓ
