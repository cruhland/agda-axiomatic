module net.cruhland.axioms.Sets.Singleton where

open import Level using (_⊔_; Setω)
open import net.cruhland.axioms.Sets.Base using
  (α; El; S; SetAxioms; Setoid; σ₁; σ₂)
import net.cruhland.axioms.Sets.Equality as Equality
open import net.cruhland.models.Logic using
  (_↔_; ↔-elimᴸ; ↔-elimᴿ; ↔-sym; ↔-trans)

module SingletonDef (SA : SetAxioms) where
  open SetAxioms SA using (_∈_; PSet)

  is-singleton : {S : Setoid σ₁ σ₂} → El S → PSet S α → Set (σ₁ ⊔ σ₂ ⊔ α)
  is-singleton {S = S} a A = ∀ {x} → x ∈ A ↔ x ≈ a
    where open Setoid S using (_≈_)

record SingletonSet (SA : SetAxioms) : Setω where
  open Equality SA using (_≃_; ≃-intro)
  open SetAxioms SA using (_∈_; PSet)
  open SingletonDef SA using (is-singleton)

  field
    singleton : El S → PSet S α
    x∈sa↔x≈a :
      {S : Setoid σ₁ σ₂} {a : El S} → is-singleton {α = α} {S} a (singleton a)

  module _ {S : Setoid σ₁ σ₂} where
    open Setoid S using (_≈_)
    module S = Setoid S

    x∈sa-elim : {x a : El S} → x ∈ singleton {S = S} {α} a → x ≈ a
    x∈sa-elim = ↔-elimᴸ x∈sa↔x≈a

    x∈sa-intro : {x a : El S} → x ≈ a → x ∈ singleton {α = α} a
    x∈sa-intro = ↔-elimᴿ x∈sa↔x≈a

    a∈sa : {a : El S} → a ∈ singleton {S = S} {α} a
    a∈sa = x∈sa-intro S.refl

    singleton-unique :
      {a : El S} {A : PSet S α} → is-singleton a A → singleton a ≃ A
    singleton-unique x∈A↔x≈a = ≃-intro (↔-trans x∈sa↔x≈a (↔-sym x∈A↔x≈a))
