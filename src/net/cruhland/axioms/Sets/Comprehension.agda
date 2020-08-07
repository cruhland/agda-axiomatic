module net.cruhland.axioms.Sets.Comprehension where

open import Level using (_⊔_; Setω)
open import net.cruhland.axioms.Sets.Base using
  (α; σ₁; σ₂; El; S; SetAxioms; Setoid)
open import net.cruhland.models.Logic using (_↔_; ↔-elimᴸ; ↔-elimᴿ)

module ComprehensionDefs where

  congProp : {S : Setoid σ₁ σ₂} → (El S → Set α) → Set (σ₁ ⊔ σ₂ ⊔ α)
  congProp {S = S} P = ∀ {x y} → x ≈ y → P x → P y
    where open Setoid S using (_≈_)

record Comprehension (SA : SetAxioms) : Setω where
  open ComprehensionDefs public using (congProp)
  open SetAxioms SA using (_∈_; PSet)

  field
    ⟨_~_⟩ :
      let open Setoid S using (_≈_)
       in (P : El S → Set α) → congProp {S = S} P → PSet S α

    x∈⟨P⟩↔Px :
      {S : Setoid σ₁ σ₂} {P : El S → Set α} {P-cong : congProp {S = S} P} →
        ∀ {x} → x ∈ ⟨_~_⟩ {S = S} P P-cong ↔ P x

  x∈⟨P⟩-elim :
    {S : Setoid σ₁ σ₂} {P : El S → Set α} {P-cong : congProp {S = S} P} →
      ∀ {x} → x ∈ ⟨_~_⟩ {S = S} P P-cong → P x
  x∈⟨P⟩-elim = ↔-elimᴸ x∈⟨P⟩↔Px

  x∈⟨P⟩-intro :
    {S : Setoid σ₁ σ₂} {P : El S → Set α} {P-cong : congProp {S = S} P} →
      ∀ {x} → P x → x ∈ ⟨_~_⟩ {S = S} P P-cong
  x∈⟨P⟩-intro = ↔-elimᴿ x∈⟨P⟩↔Px
