open import net.cruhland.axioms.Sets.Base using (SetAxioms)
open import net.cruhland.axioms.Sets.Union using (PairwiseUnion)

module net.cruhland.axioms.Sets.Properties
    (SA : SetAxioms) (PU : PairwiseUnion SA) where
  open PairwiseUnion PU using (_∪_; x∈A∪B↔x∈A∨x∈B)
  open SetAxioms SA using (_∈_; PSet)

  open import Function using (_∘_)
  open import net.cruhland.axioms.Sets.Base using (α; β; χ; El; S)
  open import net.cruhland.axioms.Sets.Equality SA using
    (_≃_; ≃-elimᴸ; ≃-elimᴿ; ≃-intro)
  open import net.cruhland.axioms.Sets.Subset SA using (_⊆_; ⊆-intro)
  open import net.cruhland.models.Logic using
    (_∨_; ∨-introᴸ; ∨-introᴿ; _↔_; ↔-elimᴸ; ↔-elimᴿ; ↔-intro)

  ⊆-antisym : {A B : PSet S α} → A ⊆ B → B ⊆ A → A ≃ B
  ⊆-antisym (⊆-intro x∈A→x∈B) (⊆-intro x∈B→x∈A) =
    ≃-intro (↔-intro x∈A→x∈B x∈B→x∈A)

  ≃→⊆ᴸ : {A B : PSet S α} → A ≃ B → A ⊆ B
  ≃→⊆ᴸ = ⊆-intro ∘ ≃-elimᴸ

  ≃→⊆ᴿ : {A B : PSet S α} → A ≃ B → B ⊆ A
  ≃→⊆ᴿ = ⊆-intro ∘ ≃-elimᴿ

  ∪-⊆ᴸ : {A : PSet S α} {B : PSet S β} {C : PSet S χ} → A ∪ B ⊆ C → A ⊆ C
  ∪-⊆ᴸ (⊆-intro x∈A∪B→x∈C) =
    ⊆-intro (x∈A∪B→x∈C ∘ ↔-elimᴿ x∈A∪B↔x∈A∨x∈B ∘ ∨-introᴸ)

  ∪-⊆ᴿ : {A : PSet S α} {B : PSet S β} {C : PSet S χ} → A ∪ B ⊆ C → B ⊆ C
  ∪-⊆ᴿ (⊆-intro x∈A∪B→x∈C) =
    ⊆-intro (x∈A∪B→x∈C ∘ ↔-elimᴿ x∈A∪B↔x∈A∨x∈B ∘ ∨-introᴿ)
