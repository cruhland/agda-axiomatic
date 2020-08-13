module net.cruhland.axioms.Sets.Union where

open import Function using (_∘_)
open import Level using (_⊔_; Setω)
open import net.cruhland.axioms.Sets.Base using
  (α; β; χ; S; SetAxioms; Setoid; σ₁; σ₂)
open import net.cruhland.axioms.Sets.Empty using (EmptySet)
import net.cruhland.axioms.Sets.Decidable as Decidable
import net.cruhland.axioms.Sets.Equality as Equality
import net.cruhland.axioms.Sets.Subset as Subset
open import net.cruhland.models.Logic using
  ( _∨_; _∨?_; ∨-comm; ∨-forceᴿ; ∨-introᴸ; ∨-introᴿ
  ; _↔_; ↔-elimᴸ; ↔-elimᴿ
  ; Dec; dec-map
  )

record PairwiseUnion (SA : SetAxioms) (ES : EmptySet SA) : Setω where
  open Decidable SA using (_∈?_; DecMembership; ∈?-intro)
  open Equality SA using (_≃_; ≃-intro; ∈-substᴿ; ≃-sym; ≃-trans)
  open EmptySet ES using (∅; x∉∅)
  open SetAxioms SA using (_∈_; PSet)
  open Subset SA using (_⊆_; ⊆-antisym; ⊆-intro)

  infixl 6 _∪_

  field
    _∪_ : PSet S α → PSet S β → PSet S (α ⊔ β)

  is-union :
    {S : Setoid σ₁ σ₂} → PSet S α → PSet S β → PSet S (α ⊔ β) → Set (σ₁ ⊔ α ⊔ β)
  is-union A B A∪B = ∀ {x} → x ∈ A∪B ↔ x ∈ A ∨ x ∈ B

  field
    x∈A∪B↔x∈A∨x∈B : {A : PSet S α} {B : PSet S β} → is-union A B (A ∪ B)

  x∈A∪B-elim :
    {S : Setoid σ₁ σ₂} {A : PSet S α} {B : PSet S β} →
      ∀ {x} → x ∈ A ∪ B → x ∈ A ∨ x ∈ B
  x∈A∪B-elim = ↔-elimᴸ x∈A∪B↔x∈A∨x∈B

  x∈A∪B-intro :
    {S : Setoid σ₁ σ₂} {A : PSet S α} {B : PSet S β} →
      ∀ {x} → x ∈ A ∨ x ∈ B → x ∈ A ∪ B
  x∈A∪B-intro = ↔-elimᴿ x∈A∪B↔x∈A∨x∈B

  x∈A∪B-introᴸ :
    {S : Setoid σ₁ σ₂} {A : PSet S α} {B : PSet S β} → ∀ {x} → x ∈ A → x ∈ A ∪ B
  x∈A∪B-introᴸ = x∈A∪B-intro ∘ ∨-introᴸ

  x∈A∪B-introᴿ :
    {S : Setoid σ₁ σ₂} {A : PSet S α} {B : PSet S β} → ∀ {x} → x ∈ B → x ∈ A ∪ B
  x∈A∪B-introᴿ = x∈A∪B-intro ∘ ∨-introᴿ

  ∪-comm : {A : PSet S α} {B : PSet S β} → A ∪ B ≃ B ∪ A
  ∪-comm = ⊆-antisym AB⊆BA BA⊆AB
    where
      AB⊆BA = ⊆-intro (x∈A∪B-intro ∘ ∨-comm ∘ x∈A∪B-elim)
      BA⊆AB = ⊆-intro (x∈A∪B-intro ∘ ∨-comm ∘ x∈A∪B-elim)

  ∪-assoc :
    {A : PSet S α} {B : PSet S β} {C : PSet S χ} → (A ∪ B) ∪ C ≃ A ∪ (B ∪ C)
  ∪-assoc {A = A} {B} {C} = ⊆-antisym (⊆-intro forward) (⊆-intro backward)
    where
      forward : ∀ {x} → x ∈ (A ∪ B) ∪ C → x ∈ A ∪ (B ∪ C)
      forward x∈[AB]C with x∈A∪B-elim x∈[AB]C
      forward x∈[AB]C | ∨-introᴸ x∈A∪B with x∈A∪B-elim x∈A∪B
      forward x∈[AB]C | ∨-introᴸ x∈A∪B | ∨-introᴸ x∈A =
        x∈A∪B-introᴸ x∈A
      forward x∈[AB]C | ∨-introᴸ x∈A∪B | ∨-introᴿ x∈B =
        x∈A∪B-introᴿ (x∈A∪B-introᴸ x∈B)
      forward x∈[AB]C | ∨-introᴿ x∈C =
        x∈A∪B-introᴿ (x∈A∪B-introᴿ x∈C)

      backward : ∀ {x} → x ∈ A ∪ (B ∪ C) → x ∈ (A ∪ B) ∪ C
      backward x∈A[BC] with x∈A∪B-elim x∈A[BC]
      backward x∈A[BC] | ∨-introᴸ x∈A =
        x∈A∪B-introᴸ (x∈A∪B-introᴸ x∈A)
      backward x∈A[BC] | ∨-introᴿ x∈B∪C with x∈A∪B-elim x∈B∪C
      backward x∈A[BC] | ∨-introᴿ x∈B∪C | ∨-introᴸ x∈B =
        x∈A∪B-introᴸ (x∈A∪B-introᴿ x∈B)
      backward x∈A[BC] | ∨-introᴿ x∈B∪C | ∨-introᴿ x∈C =
        x∈A∪B-introᴿ x∈C

  ∪-substᴸ : {A₁ A₂ : PSet S α} {B : PSet S β} → A₁ ≃ A₂ → A₁ ∪ B ≃ A₂ ∪ B
  ∪-substᴸ {A₁ = A₁} {A₂} {B} A₁≃A₂ =
    ⊆-antisym (⊆-intro forward) (⊆-intro backward)
      where
        forward : ∀ {x} → x ∈ A₁ ∪ B → x ∈ A₂ ∪ B
        forward x∈A₁∪B with x∈A∪B-elim x∈A₁∪B
        ... | ∨-introᴸ x∈A₁ = x∈A∪B-introᴸ (∈-substᴿ A₁≃A₂ x∈A₁)
        ... | ∨-introᴿ x∈B = x∈A∪B-introᴿ x∈B

        backward : ∀ {x} → x ∈ A₂ ∪ B → x ∈ A₁ ∪ B
        backward x∈A₂∪B with x∈A∪B-elim x∈A₂∪B
        ... | ∨-introᴸ x∈A₂ = x∈A∪B-introᴸ (∈-substᴿ (≃-sym A₁≃A₂) x∈A₂)
        ... | ∨-introᴿ x∈B = x∈A∪B-introᴿ x∈B

  ∪-substᴿ : {A : PSet S α} {B₁ B₂ : PSet S β} → B₁ ≃ B₂ → A ∪ B₁ ≃ A ∪ B₂
  ∪-substᴿ B₁≃B₂ = ≃-trans ∪-comm (≃-trans (∪-substᴸ B₁≃B₂) ∪-comm)

  ∪-∅ᴸ : {A : PSet S α} → (∅ {α = α}) ∪ A ≃ A
  ∪-∅ᴸ {A = A} = ⊆-antisym (⊆-intro x∈∅∪A→x∈A) (⊆-intro x∈A∪B-introᴿ)
    where
      x∈∅∪A→x∈A : ∀ {x} → x ∈ (∅ {α = α}) ∪ A → x ∈ A
      x∈∅∪A→x∈A = ∨-forceᴿ x∉∅ ∘ x∈A∪B-elim

  ∪-∅ᴿ : {A : PSet S α} → A ∪ (∅ {α = α}) ≃ A
  ∪-∅ᴿ = ≃-trans ∪-comm ∪-∅ᴸ

  instance
    ∪-∈? :
      {A : PSet S α} {B : PSet S β} →
        {{DecMembership A}} → {{DecMembership B}} → DecMembership (A ∪ B)
    ∪-∈? {A = A} {B} =
      ∈?-intro
        (λ {x} → dec-map x∈A∪B-intro x∈A∪B-elim (x ∈? A ∨? x ∈? B))
