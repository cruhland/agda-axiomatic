module net.cruhland.axiomatic.Sets where

open import Function using (id)
open import Level using (_⊔_; Setω) renaming (suc to lsuc)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)
open import net.cruhland.axiomatic.Logic using
  (¬_; _↔_; ↔-elimᴸ; ↔-refl; ↔-sym; ↔-trans)

-- Export standard library definitions
open import Relation.Binary public using (Setoid)
open Setoid public using () renaming (Carrier to El)

record SetTheory : Setω where
  infix 5 _∈_ _∉_

  field
    PSet : ∀ {σ₁ σ₂} → Setoid σ₁ σ₂ → ∀ α → Set (σ₁ ⊔ σ₂ ⊔ lsuc α)
    _∈_ : ∀ {σ₁ σ₂ α} {S : Setoid σ₁ σ₂} → El S → PSet S α → Set α

    PSet-cong : ∀ {σ₁ σ₂ α} {S : Setoid σ₁ σ₂} {x y : El S} {A : PSet S α} →
      let open Setoid S using (_≈_) in x ≈ y → x ∈ A ↔ y ∈ A

  _∉_ : ∀ {α₁ α₂ β} {A : Setoid α₁ α₂} → El A → PSet A β → Set β
  x ∉ A = ¬ (x ∈ A)

module _ (ST : SetTheory) where
  open SetTheory ST using (_∈_; PSet; PSet-cong)

  infix 4 _≗_ _≗̸_

  record _≗_ {σ₁ σ₂ α} {S : Setoid σ₁ σ₂} (A B : PSet S α) : Set (σ₁ ⊔ α) where
    constructor ≗-intro
    field
      ≗-elim : ∀ {x} → x ∈ A ↔ x ∈ B

  _≗̸_ : ∀ {σ₁ σ₂ α} {S : Setoid σ₁ σ₂} → PSet S α → PSet S α → Set (σ₁ ⊔ α)
  A ≗̸ B = ¬ (A ≗ B)

  ≗-refl : ∀ {σ₁ σ₂ α} {S : Setoid σ₁ σ₂} {A : PSet S α} → A ≗ A
  ≗-refl = ≗-intro ↔-refl

  ≗-sym : ∀ {σ₁ σ₂ α} {S : Setoid σ₁ σ₂} {A B : PSet S α} → A ≗ B → B ≗ A
  ≗-sym (≗-intro x∈A↔x∈B) = ≗-intro (↔-sym x∈A↔x∈B)

  ≗-trans :
    ∀ {σ₁ σ₂ α} {S : Setoid σ₁ σ₂} {A B C : PSet S α} → A ≗ B → B ≗ C → A ≗ C
  ≗-trans (≗-intro x∈A↔x∈B) (≗-intro x∈B↔x∈C) =
    ≗-intro (↔-trans x∈A↔x∈B x∈B↔x∈C)

  ≗-IsEquivalence :
    ∀ {σ₁ σ₂ α} {S : Setoid σ₁ σ₂} → IsEquivalence (_≗_ {σ₁} {σ₂} {α} {S})
  ≗-IsEquivalence = record { refl = ≗-refl ; sym = ≗-sym ; trans = ≗-trans }

  PSet-Setoid :
    ∀ {σ₁ σ₂} → Setoid σ₁ σ₂ → ∀ α → Setoid (σ₁ ⊔ σ₂ ⊔ lsuc α) (σ₁ ⊔ α)
  PSet-Setoid S α =
    record { Carrier = PSet S α ; _≈_ = _≗_ ; isEquivalence = ≗-IsEquivalence }

  ∈-substᴿ :
    ∀ {σ₁ σ₂ α} {S : Setoid σ₁ σ₂} {A B : PSet S α} {x : El S} →
      A ≗ B → x ∈ A → x ∈ B
  ∈-substᴿ (≗-intro x∈A↔x∈B) = ↔-elimᴸ x∈A↔x∈B

  ∈-substᴸ :
    ∀ {σ₁ σ₂ α β} {S : Setoid σ₁ σ₂}
      {A B : PSet S α} {C : PSet (PSet-Setoid S α) β} →
        A ≗ B → A ∈ C → B ∈ C
  ∈-substᴸ A≗B = ↔-elimᴸ (PSet-cong A≗B)
