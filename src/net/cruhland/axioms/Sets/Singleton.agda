module net.cruhland.axioms.Sets.Singleton where

open import Level using (_⊔_; Setω)
open import net.cruhland.axioms.Sets.Base using
  (El; S; SetAxioms; Setoid; σ₁; σ₂)
import net.cruhland.axioms.Sets.Equality as Equality
open import net.cruhland.models.Logic using
  (_↔_; ↔-elimᴸ; ↔-elimᴿ; ↔-sym; ↔-trans)

module SingletonDef (SA : SetAxioms) where
  open SetAxioms SA using (_∈_; PSet)

  is-singleton : {S : Setoid σ₁ σ₂} → El S → PSet S σ₂ → Set (σ₁ ⊔ σ₂)
  is-singleton {S = S} a A = ∀ {x} → x ∈ A ↔ a ≈ x
    where open Setoid S using (_≈_)

record SingletonSet (SA : SetAxioms) : Setω where
  open Equality SA using (_≃_; ≃-intro)
  open SetAxioms SA using (_∈_; PSet)
  open SingletonDef SA using (is-singleton)

  field
    singleton : {S : Setoid σ₁ σ₂} → El S → PSet S σ₂
    x∈sa↔a≈x :
      {S : Setoid σ₁ σ₂} {a : El S} → is-singleton {S = S} a (singleton a)

  module _ {S : Setoid σ₁ σ₂} where
    open Setoid S using (_≈_)
    module S = Setoid S

    x∈sa-elim : {x a : El S} → x ∈ singleton {S = S} a → a ≈ x
    x∈sa-elim = ↔-elimᴸ x∈sa↔a≈x

    x∈sa-intro : {x a : El S} → a ≈ x → x ∈ singleton a
    x∈sa-intro = ↔-elimᴿ x∈sa↔a≈x

    a∈sa : {a : El S} → a ∈ singleton {S = S} a
    a∈sa = x∈sa-intro S.refl

    singleton-unique :
      {a : El S} {A : PSet S σ₂} → is-singleton a A → singleton a ≃ A
    singleton-unique x∈A↔a≈x = ≃-intro (↔-trans x∈sa↔a≈x (↔-sym x∈A↔a≈x))
