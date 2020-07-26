open import net.cruhland.axioms.Sets.Base using (SetAxioms)

module net.cruhland.axioms.Sets.Subset (SA : SetAxioms) where
  open SetAxioms SA using (_∈_; PSet)

  open import Level using (_⊔_)
  open import net.cruhland.axioms.Sets.Base using (α; β; S; Setoid; σ₁; σ₂)
  open import net.cruhland.models.Logic using (¬_)

  infix 4 _⊆_ _⊈_

  record _⊆_ {S : Setoid σ₁ σ₂} (A : PSet S α) (B : PSet S β)
      : Set (σ₁ ⊔ α ⊔ β) where
    constructor ⊆-intro
    field
      ⊆-elim : ∀ {x} → x ∈ A → x ∈ B

  _⊈_ : {S : Setoid σ₁ σ₂} → PSet S α → PSet S β → Set (σ₁ ⊔ α ⊔ β)
  A ⊈ B = ¬ (A ⊆ B)
