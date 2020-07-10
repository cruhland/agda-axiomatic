module net.cruhland.axiomatic.Sets.Singleton where

open import Level using (_⊔_; Setω)
open import net.cruhland.axiomatic.Logic using (_↔_; ↔-elimᴿ; ↔-sym; ↔-trans)
open import net.cruhland.axiomatic.Sets.Base using
  (α; El; S; SetAxioms; Setoid; σ₁; σ₂)
import net.cruhland.axiomatic.Sets.Equality as Equality

module SingletonDef (SA : SetAxioms) where
  open SetAxioms SA using (_∈_; PSet)

  is-singleton : {S : Setoid σ₁ σ₂} → El S → PSet S α → Set (σ₁ ⊔ σ₂ ⊔ α)
  is-singleton {S = S} a A = ∀ {x} → x ∈ A ↔ x ≈ a
    where open Setoid S using (_≈_)

record SingletonSet (SA : SetAxioms) : Setω where
  open Equality SA using (_≗_; ≗-intro)
  open SetAxioms SA using (_∈_; PSet)
  open SingletonDef SA using (is-singleton)

  field
    singleton : El S → PSet S α
    x∈sa↔x≈a :
      {S : Setoid σ₁ σ₂} {a : El S} → is-singleton {α = α} {S} a (singleton a)

  a∈sa : {S : Setoid σ₁ σ₂} {a : El S} → a ∈ singleton {S = S} {α} a
  a∈sa {S = S} = ↔-elimᴿ x∈sa↔x≈a S.refl
    where module S = Setoid S

  singleton-unique :
    {S : Setoid σ₁ σ₂} {a : El S} {A : PSet S α} →
      is-singleton a A → A ≗ singleton a
  singleton-unique {S = S} x∈A↔x≈a = ≗-intro (↔-trans x∈A↔x≈a (↔-sym x∈sa↔x≈a))
    where open Setoid S using (_≈_)
