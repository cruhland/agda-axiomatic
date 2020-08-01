open import net.cruhland.axioms.Sets.Base using (SetAxioms)
import net.cruhland.axioms.Sets.Equality as Equality

module net.cruhland.axioms.Sets.Subset (SA : SetAxioms) where
  open Equality SA using (_≃_; ≃-elimᴸ; ≃-elimᴿ; ≃-intro)
  open SetAxioms SA using (_∈_; PSet)

  open import Function using (_∘_)
  open import Level using (_⊔_)
  open import net.cruhland.axioms.Sets.Base using (α; β; S; Setoid; σ₁; σ₂)
  open import net.cruhland.models.Logic using (_↔_; ↔-intro; ¬_)

  infix 4 _⊆_ _⊈_

  record _⊆_ {S : Setoid σ₁ σ₂} (A : PSet S α) (B : PSet S β)
      : Set (σ₁ ⊔ α ⊔ β) where
    constructor ⊆-intro
    field
      ⊆-elim : ∀ {x} → x ∈ A → x ∈ B

  _⊈_ : {S : Setoid σ₁ σ₂} → PSet S α → PSet S β → Set (σ₁ ⊔ α ⊔ β)
  A ⊈ B = ¬ (A ⊆ B)

  ⊆-antisym : {A B : PSet S α} → A ⊆ B → B ⊆ A → A ≃ B
  ⊆-antisym (⊆-intro x∈A→x∈B) (⊆-intro x∈B→x∈A) =
    ≃-intro (↔-intro x∈A→x∈B x∈B→x∈A)

  ≃→⊆ᴸ : {A B : PSet S α} → A ≃ B → A ⊆ B
  ≃→⊆ᴸ = ⊆-intro ∘ ≃-elimᴸ

  ≃→⊆ᴿ : {A B : PSet S α} → A ≃ B → B ⊆ A
  ≃→⊆ᴿ = ⊆-intro ∘ ≃-elimᴿ
