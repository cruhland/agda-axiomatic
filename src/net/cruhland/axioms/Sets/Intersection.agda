module net.cruhland.axioms.Sets.Intersection where

open import Function using (_∘_)
open import Level using (_⊔_; Setω)
open import net.cruhland.axioms.Sets.Base using
  (α; β; χ; El; S; SetAxioms; Setoid; σ₁; σ₂)
import net.cruhland.axioms.Sets.Equality as Equality
import net.cruhland.axioms.Sets.Subset as Subset
open import net.cruhland.models.Logic using
  (_∧_; ∧-comm; ∧-elimᴸ; ∧-elimᴿ; ∧-intro; _↔_; ↔-elimᴸ; ↔-elimᴿ; curry)

record PairwiseIntersection (SA : SetAxioms) : Setω where
  open Equality SA using (_≃_; ∈-substᴿ; ≃-sym; ≃-trans)
  open SetAxioms SA using (_∈_; PSet)
  open Subset SA using (_⊆_; ⊆-antisym; ⊆-intro)

  infixl 7 _∩_

  field
    _∩_ : PSet S α → PSet S β → PSet S (α ⊔ β)

  is-intersection :
    {S : Setoid σ₁ σ₂} → PSet S α → PSet S β → PSet S (α ⊔ β) → Set (σ₁ ⊔ α ⊔ β)
  is-intersection A B A∩B = ∀ {x} → x ∈ A∩B ↔ x ∈ A ∧ x ∈ B

  field
    x∈A∩B↔x∈A∧x∈B : {A : PSet S α} {B : PSet S β} → is-intersection A B (A ∩ B)

  x∈A∩B-elim :
    {S : Setoid σ₁ σ₂} {A : PSet S α} {B : PSet S β} →
      ∀ {x} → x ∈ A ∩ B → x ∈ A ∧ x ∈ B
  x∈A∩B-elim = ↔-elimᴸ x∈A∩B↔x∈A∧x∈B

  x∈A∩B-elimᴸ :
    {S : Setoid σ₁ σ₂} {A : PSet S α} {B : PSet S β} →
      ∀ {x} → x ∈ A ∩ B → x ∈ A
  x∈A∩B-elimᴸ = ∧-elimᴸ ∘ x∈A∩B-elim

  x∈A∩B-elimᴿ :
    {S : Setoid σ₁ σ₂} {A : PSet S α} {B : PSet S β} →
      ∀ {x} → x ∈ A ∩ B → x ∈ B
  x∈A∩B-elimᴿ = ∧-elimᴿ ∘ x∈A∩B-elim

  x∈A∩B-intro :
    {S : Setoid σ₁ σ₂} {A : PSet S α} {B : PSet S β} →
      ∀ {x} → x ∈ A ∧ x ∈ B → x ∈ A ∩ B
  x∈A∩B-intro = ↔-elimᴿ x∈A∩B↔x∈A∧x∈B

  x∈A∩B-intro₂ :
    {S : Setoid σ₁ σ₂} {A : PSet S α} {B : PSet S β} →
      ∀ {x} → x ∈ A → x ∈ B → x ∈ A ∩ B
  x∈A∩B-intro₂ = curry x∈A∩B-intro

  ∩-comm : {A : PSet S α} {B : PSet S β} → A ∩ B ≃ B ∩ A
  ∩-comm = ⊆-antisym AB⊆BA BA⊆AB
    where
      AB⊆BA = ⊆-intro (x∈A∩B-intro ∘ ∧-comm ∘ x∈A∩B-elim)
      BA⊆AB = ⊆-intro (x∈A∩B-intro ∘ ∧-comm ∘ x∈A∩B-elim)

  ∩-assoc :
    {A : PSet S α} {B : PSet S β} {C : PSet S χ} → (A ∩ B) ∩ C ≃ A ∩ (B ∩ C)
  ∩-assoc {A = A} {B} {C} = ⊆-antisym (⊆-intro forward) (⊆-intro backward)
    where
      forward : ∀ {x} → x ∈ (A ∩ B) ∩ C → x ∈ A ∩ (B ∩ C)
      forward x∈[AB]C =
        let ∧-intro x∈AB x∈C = x∈A∩B-elim x∈[AB]C
            ∧-intro x∈A x∈B = x∈A∩B-elim x∈AB
         in x∈A∩B-intro₂ x∈A (x∈A∩B-intro₂ x∈B x∈C)

      backward : ∀ {x} → x ∈ A ∩ (B ∩ C) → x ∈ (A ∩ B) ∩ C
      backward x∈A[BC] =
        let ∧-intro x∈A x∈BC = x∈A∩B-elim x∈A[BC]
            ∧-intro x∈B x∈C = x∈A∩B-elim x∈BC
         in x∈A∩B-intro₂ (x∈A∩B-intro₂ x∈A x∈B) x∈C

  ∩-substᴸ : {A₁ A₂ : PSet S α} {B : PSet S β} → A₁ ≃ A₂ → A₁ ∩ B ≃ A₂ ∩ B
  ∩-substᴸ {A₁ = A₁} {A₂} {B} A₁≃A₂ =
    ⊆-antisym (⊆-intro forward) (⊆-intro backward)
      where
        forward : ∀ {x} → x ∈ A₁ ∩ B → x ∈ A₂ ∩ B
        forward x∈A₁B =
          let ∧-intro x∈A₁ x∈B = x∈A∩B-elim x∈A₁B
           in x∈A∩B-intro₂ (∈-substᴿ A₁≃A₂ x∈A₁) x∈B

        backward : ∀ {x} → x ∈ A₂ ∩ B → x ∈ A₁ ∩ B
        backward x∈A₂B =
          let ∧-intro x∈A₂ x∈B = x∈A∩B-elim x∈A₂B
           in x∈A∩B-intro₂ (∈-substᴿ (≃-sym A₁≃A₂) x∈A₂) x∈B

  ∩-substᴿ : {A : PSet S α} {B₁ B₂ : PSet S β} → B₁ ≃ B₂ → A ∩ B₁ ≃ A ∩ B₂
  ∩-substᴿ B₁≃B₂ = ≃-trans ∩-comm (≃-trans (∩-substᴸ B₁≃B₂) ∩-comm)
