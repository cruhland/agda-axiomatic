open import Level using (_⊔_; 0ℓ) renaming (suc to sℓ)
open import Relation.Binary using (IsEquivalence)
open import net.cruhland.axioms.Sets.Base using (α; β; S; σ₁; σ₂; SetAxioms)
open import net.cruhland.models.Logic using
  (¬_; _↔_; ↔-elimᴸ; ↔-elimᴿ; ↔-refl; ↔-sym; ↔-trans)
open import net.cruhland.models.Setoid using (El; Setoid; Setoid₀)

module net.cruhland.axioms.Sets.Equality (SA : SetAxioms) where
  open SetAxioms SA using (_∈_; _∉_; PSet; PSet-cong)

  infix 4 _≃_ _≄_

  record _≃_ {S : Setoid σ₁ σ₂} (A B : PSet S α) : Set (σ₁ ⊔ α) where
    constructor ≃-intro
    field
      ≃-elim : ∀ {x} → x ∈ A ↔ x ∈ B

  _≄_ : {S : Setoid σ₁ σ₂} → PSet S α → PSet S α → Set (σ₁ ⊔ α)
  A ≄ B = ¬ (A ≃ B)

  ≃-elimᴸ : {S : Setoid σ₁ σ₂} {A B : PSet S α} → A ≃ B → ∀ {x} → x ∈ A → x ∈ B
  ≃-elimᴸ (≃-intro x∈A↔x∈B) = ↔-elimᴸ x∈A↔x∈B

  ≃-elimᴿ : {S : Setoid σ₁ σ₂} {A B : PSet S α} → A ≃ B → ∀ {x} → x ∈ B → x ∈ A
  ≃-elimᴿ (≃-intro x∈A↔x∈B) = ↔-elimᴿ x∈A↔x∈B

  ≃-refl : {A : PSet S α} → A ≃ A
  ≃-refl = ≃-intro ↔-refl

  ≃-sym : {A B : PSet S α} → A ≃ B → B ≃ A
  ≃-sym (≃-intro x∈A↔x∈B) = ≃-intro (↔-sym x∈A↔x∈B)

  ≃-trans : {A B C : PSet S α} → A ≃ B → B ≃ C → A ≃ C
  ≃-trans (≃-intro x∈A↔x∈B) (≃-intro x∈B↔x∈C) =
    ≃-intro (↔-trans x∈A↔x∈B x∈B↔x∈C)

  ≃-IsEquivalence : IsEquivalence (_≃_ {σ₁} {σ₂} {α} {S})
  ≃-IsEquivalence = record { refl = ≃-refl ; sym = ≃-sym ; trans = ≃-trans }

  PSet-Setoid : Setoid σ₁ σ₂ → ∀ α → Setoid (σ₁ ⊔ σ₂ ⊔ sℓ α) (σ₁ ⊔ α)
  PSet-Setoid S α =
    record { Carrier = PSet S α ; _≈_ = _≃_ ; isEquivalence = ≃-IsEquivalence }

  PSet-Setoid₀ : Setoid σ₁ 0ℓ → Setoid (σ₁ ⊔ sℓ 0ℓ) σ₁
  PSet-Setoid₀ S = PSet-Setoid S 0ℓ

  ∈-substᴿ :
    {S : Setoid σ₁ σ₂} {A B : PSet S α} {x : El S} → A ≃ B → x ∈ A → x ∈ B
  ∈-substᴿ (≃-intro x∈A↔x∈B) = ↔-elimᴸ x∈A↔x∈B

  ∈-substᴸ :
    {A B : PSet S α} {C : PSet (PSet-Setoid S α) β} → A ≃ B → A ∈ C → B ∈ C
  ∈-substᴸ = PSet-cong

  ∉-substᴿ :
    {S : Setoid σ₁ σ₂} {A B : PSet S α} {x : El S} → A ≃ B → x ∉ A → x ∉ B
  ∉-substᴿ A≃B x∉A x∈B = x∉A (∈-substᴿ (≃-sym A≃B) x∈B)

  ∉-substᴸ :
    {A B : PSet S α} {C : PSet (PSet-Setoid S α) β} → A ≃ B → A ∉ C → B ∉ C
  ∉-substᴸ A≃B A∉C B∈C = A∉C (∈-substᴸ (≃-sym A≃B) B∈C)

  module ≃-Reasoning where

    infix 3 _∎
    infixr 2 _≃⟨⟩_ step-≃ step-≃˘
    infix 1 begin_

    begin_ : {A B : PSet S α} → A ≃ B → A ≃ B
    begin A≃B = A≃B

    _≃⟨⟩_ : (A {B} : PSet S α) → A ≃ B → A ≃ B
    _ ≃⟨⟩ A≃B = A≃B

    step-≃ : (A {B C} : PSet S α) → B ≃ C → A ≃ B → A ≃ C
    step-≃ _ B≃C A≃B = ≃-trans A≃B B≃C

    step-≃˘ : (A {B C} : PSet S α) → B ≃ C → B ≃ A → A ≃ C
    step-≃˘ _ B≃C B≃A = ≃-trans (≃-sym B≃A) B≃C

    _∎ : (A : PSet S α) → A ≃ A
    _ ∎ = ≃-refl

    syntax step-≃ A B≃C A≃B = A ≃⟨ A≃B ⟩ B≃C
    syntax step-≃˘ A B≃C B≃A = A ≃˘⟨ B≃A ⟩ B≃C
