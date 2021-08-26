open import Level using (0ℓ) renaming (suc to sℓ)
open import net.cruhland.axioms.DecEq using (DecEq)
open import net.cruhland.axioms.Eq as Eq using (_≃_)

module net.cruhland.models.Setoid where

-- Export standard library definitions
open import Function.Equivalence public
  using (Equivalence; ⇔-setoid) renaming (id to equivalence-id)
open import Function.Equality public
  using (_⟶_; _⇨_; _⟨$⟩_; cong; Π) renaming (const to SPred-const)
open import Relation.Binary public using (Setoid)
open Setoid public using () renaming (Carrier to El)

Setoid₀ : Set (sℓ 0ℓ)
Setoid₀ = Setoid 0ℓ 0ℓ

-- Replace standard library DecSetoid with one that uses our version
-- of decidable equality
record DecSetoid : Set₁ where
  field
    Carrier : Set
    {{decEq}} : DecEq Carrier

  setoid : Setoid₀
  setoid =
    let isEquiv = record { refl = Eq.refl ; sym = Eq.sym ; trans = Eq.trans }
     in record { Carrier = Carrier ; _≈_ = _≃_ ; isEquivalence = isEquiv }

DecSetoid₀ : Set (sℓ 0ℓ)
DecSetoid₀ = DecSetoid

SPred₀ : Setoid₀ → Set (sℓ 0ℓ)
SPred₀ S = S ⟶ ⇔-setoid 0ℓ

SRel₀ : Setoid₀ → Setoid₀ → Set (sℓ 0ℓ)
SRel₀ S T = S ⟶ T ⇨ ⇔-setoid 0ℓ
