open import net.cruhland.axioms.Sets.Base using (SetAxioms)

module net.cruhland.axioms.Sets.Equality (SA : SetAxioms) where
  open SetAxioms SA using (_∈_; PSet; PSet-cong)

  open import Level using (_⊔_) renaming (suc to lsuc)
  open import Relation.Binary using (IsEquivalence)
  open import net.cruhland.axioms.Sets.Base using
    (α; β; El; S; Setoid; σ₁; σ₂)
  open import net.cruhland.models.Logic using
    (¬_; _↔_; ↔-elimᴸ; ↔-refl; ↔-sym; ↔-trans)

  infix 4 _≃_ _≄_

  record _≃_ {S : Setoid σ₁ σ₂} (A B : PSet S α) : Set (σ₁ ⊔ α) where
    constructor ≃-intro
    field
      ≃-elim : ∀ {x} → x ∈ A ↔ x ∈ B

  _≄_ : {S : Setoid σ₁ σ₂} → PSet S α → PSet S α → Set (σ₁ ⊔ α)
  A ≄ B = ¬ (A ≃ B)

  ≃-refl : {A : PSet S α} → A ≃ A
  ≃-refl = ≃-intro ↔-refl

  ≃-sym : {A B : PSet S α} → A ≃ B → B ≃ A
  ≃-sym (≃-intro x∈A↔x∈B) = ≃-intro (↔-sym x∈A↔x∈B)

  ≃-trans : {A B C : PSet S α} → A ≃ B → B ≃ C → A ≃ C
  ≃-trans (≃-intro x∈A↔x∈B) (≃-intro x∈B↔x∈C) =
    ≃-intro (↔-trans x∈A↔x∈B x∈B↔x∈C)

  ≃-IsEquivalence : IsEquivalence (_≃_ {σ₁} {σ₂} {α} {S})
  ≃-IsEquivalence = record { refl = ≃-refl ; sym = ≃-sym ; trans = ≃-trans }

  PSet-Setoid : Setoid σ₁ σ₂ → ∀ α → Setoid (σ₁ ⊔ σ₂ ⊔ lsuc α) (σ₁ ⊔ α)
  PSet-Setoid S α =
    record { Carrier = PSet S α ; _≈_ = _≃_ ; isEquivalence = ≃-IsEquivalence }

  ∈-substᴿ :
    {S : Setoid σ₁ σ₂} {A B : PSet S α} {x : El S} → A ≃ B → x ∈ A → x ∈ B
  ∈-substᴿ (≃-intro x∈A↔x∈B) = ↔-elimᴸ x∈A↔x∈B

  ∈-substᴸ :
    {A B : PSet S α} {C : PSet (PSet-Setoid S α) β} → A ≃ B → A ∈ C → B ∈ C
  ∈-substᴸ A≃B = ↔-elimᴸ (PSet-cong A≃B)
