open import Function using (_∘_; id)
open import Level using (_⊔_)
open import net.cruhland.axioms.Sets.Base using (α; β; χ; S; σ₁; σ₂; SetAxioms)
import net.cruhland.axioms.Sets.Equality as Equality
open import net.cruhland.models.Logic using (_↔_; ↔-intro; ¬_)
open import net.cruhland.models.Setoid using (El; Setoid)

module net.cruhland.axioms.Sets.Subset (SA : SetAxioms) where
  open Equality SA using
    (_≃_; ≃-elimᴸ; ≃-elimᴿ; ≃-intro; ∈-substᴿ; ∉-substᴿ; ≃-sym)
  open SetAxioms SA using (_∈_; _∉_; PSet)

  infix 4 _⊆_ _⊈_ _⊊_

  record _⊆_ {S : Setoid σ₁ σ₂} (A : PSet S α) (B : PSet S β)
      : Set (σ₁ ⊔ α ⊔ β) where
    constructor ⊆-intro
    field
      ⊆-elim : ∀ {x} → x ∈ A → x ∈ B

  open _⊆_ public

  _⊈_ : {S : Setoid σ₁ σ₂} → PSet S α → PSet S β → Set (σ₁ ⊔ α ⊔ β)
  A ⊈ B = ¬ (A ⊆ B)

  ⊆-substᴸ : {A₁ A₂ : PSet S α} {B : PSet S β} → A₁ ≃ A₂ → A₁ ⊆ B → A₂ ⊆ B
  ⊆-substᴸ A₁≃A₂ (⊆-intro x∈A₁→x∈B) =
    ⊆-intro (x∈A₁→x∈B ∘ (∈-substᴿ (≃-sym A₁≃A₂)))

  ⊆-substᴿ : {A : PSet S α} {B₁ B₂ : PSet S β} → B₁ ≃ B₂ → A ⊆ B₁ → A ⊆ B₂
  ⊆-substᴿ B₁≃B₂ (⊆-intro x∈A→x∈B₁) = ⊆-intro (∈-substᴿ B₁≃B₂ ∘ x∈A→x∈B₁)

  ⊆-refl : {A : PSet S α} → A ⊆ A
  ⊆-refl = ⊆-intro id

  ⊆-trans : {A : PSet S α} {B : PSet S β} {C : PSet S χ} → A ⊆ B → B ⊆ C → A ⊆ C
  ⊆-trans (⊆-intro x∈A→x∈B) (⊆-intro x∈B→x∈C) = ⊆-intro (x∈B→x∈C ∘ x∈A→x∈B)

  ⊆-antisym : {A B : PSet S α} → A ⊆ B → B ⊆ A → A ≃ B
  ⊆-antisym (⊆-intro x∈A→x∈B) (⊆-intro x∈B→x∈A) =
    ≃-intro (↔-intro x∈A→x∈B x∈B→x∈A)

  ≃→⊆ᴸ : {A B : PSet S α} → A ≃ B → A ⊆ B
  ≃→⊆ᴸ = ⊆-intro ∘ ≃-elimᴸ

  ≃→⊆ᴿ : {A B : PSet S α} → A ≃ B → B ⊆ A
  ≃→⊆ᴿ = ⊆-intro ∘ ≃-elimᴿ

  record _⊊_ {S : Setoid σ₁ σ₂} (A : PSet S α) (B : PSet S β)
      : Set (σ₁ ⊔ α ⊔ β) where
    constructor ⊊-intro
    field
      ⊊-subset : A ⊆ B
      ⊊-point : El S
      ⊊-pointᴸ : ⊊-point ∉ A
      ⊊-pointᴿ : ⊊-point ∈ B

  ⊊-substᴸ : {A₁ A₂ : PSet S α} {B : PSet S β} → A₁ ≃ A₂ → A₁ ⊊ B → A₂ ⊊ B
  ⊊-substᴸ A₁≃A₂ (⊊-intro A₁⊆B b b∉A₁ b∈B) =
    ⊊-intro (⊆-substᴸ A₁≃A₂ A₁⊆B) b (∉-substᴿ A₁≃A₂ b∉A₁) b∈B

  ⊊-substᴿ : {A : PSet S α} {B₁ B₂ : PSet S β} → B₁ ≃ B₂ → A ⊊ B₁ → A ⊊ B₂
  ⊊-substᴿ B₁≃B₂ (⊊-intro A⊆B₁ b b∉A b∈B₁) =
    ⊊-intro (⊆-substᴿ B₁≃B₂ A⊆B₁) b b∉A (∈-substᴿ B₁≃B₂ b∈B₁)

  ⊊-trans : {A : PSet S α} {B : PSet S β} {C : PSet S χ} → A ⊊ B → B ⊊ C → A ⊊ C
  ⊊-trans (⊊-intro A⊆B@(⊆-intro x∈A→x∈B) b b∉A b∈B) (⊊-intro B⊆C c c∉B c∈C) =
    ⊊-intro (⊆-trans A⊆B B⊆C) c (c∉B ∘ x∈A→x∈B) c∈C
