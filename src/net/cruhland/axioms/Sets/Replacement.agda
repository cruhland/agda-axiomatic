module net.cruhland.axioms.Sets.Replacement where

open import Level using (_⊔_; Setω)
open import net.cruhland.axioms.Sets.Base using
  (α; β; σ₁; σ₂; S; El; SetAxioms; Setoid)
open import net.cruhland.models.Logic using (⊤; _↔_)

module ReplacementDefs (SA : SetAxioms) where
  open SetAxioms SA using (_∈_; PSet)

  replProp :
    ∀ {τ₁ τ₂ ψ} {S : Setoid σ₁ σ₂} {T : Setoid τ₁ τ₂} {A : PSet S α} →
      (El S → El T → Set ψ) → Set (α ⊔ σ₁ ⊔ τ₁ ⊔ τ₂ ⊔ ψ)
  replProp {T = T} {A} P = ∀ {x y} → x ∈ A → P x y → ∀ {z} → P x z → y ≈ᵀ z
    where open Setoid T using () renaming (_≈_ to _≈ᵀ_)

  record ReplMembership
    {τ₁ τ₂ ψ} {S : Setoid σ₁ σ₂} {T : Setoid τ₁ τ₂} {A : PSet S α}
      (x : El T) (P : El S → El T → Set ψ) : Set (σ₁ ⊔ α ⊔ ψ) where
    field
      a : El S
      a∈A : a ∈ A
      Pax : P a x

record Replacement (SA : SetAxioms) : Setω where
  open ReplacementDefs SA using (ReplMembership; replProp)
  open SetAxioms SA using (_∈_; PSet)

  field
    map :
      ∀ {τ₁ τ₂ ψ} {S : Setoid σ₁ σ₂} {T : Setoid τ₁ τ₂} →
        (P : El S → El T → Set ψ) → (A : PSet S α) → replProp {T = T} {A} P →
          PSet T (σ₁ ⊔ α ⊔ ψ)

    x∈map↔Pax :
      ∀ {τ₁ τ₂ ψ} {S : Setoid σ₁ σ₂} {T : Setoid τ₁ τ₂} {x : El T}
        {A : PSet S α} {P : El S → El T → Set ψ} {rp : replProp {T = T} P} →
          x ∈ map {T = T} P A rp ↔ ReplMembership {T = T} {A} x P
