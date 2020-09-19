open import Level using (_⊔_; Level; 0ℓ) renaming (suc to sℓ)
open import Relation.Binary using (IsEquivalence)
open import net.cruhland.axioms.Sets.Base using (SetAxioms)
open import net.cruhland.models.Logic using
  (¬_; _↔_; ↔-elimᴸ; ↔-elimᴿ; ↔-refl; ↔-sym; ↔-trans)
open import net.cruhland.models.Setoid using (El; Setoid; Setoid₀)

module net.cruhland.axioms.Sets.Equality (SA : SetAxioms) where
  open SetAxioms SA using (_∈_; _∉_; PSet; PSet₀; PSet-cong)

  private
    variable
      σ₁ σ₂ : Level

  infix 4 _≃_

  -- Comparing nested sets means the first level parameter can
  -- vary. And doubly-nested sets require the second level parameter
  -- to vary.
  record _≃_ {S : Setoid σ₁ σ₂} (A B : PSet S) : Set (σ₁ ⊔ σ₂) where
    constructor ≃-intro
    field
      ≃-elim : ∀ {x} → x ∈ A ↔ x ∈ B

  module _ {S : Setoid σ₁ σ₂} where
    private
      variable
        A B C : PSet S

    infix 4 _≄_

    _≄_ : PSet S → PSet S → Set (σ₁ ⊔ σ₂)
    A ≄ B = ¬ (A ≃ B)

    ≃-elimᴸ : A ≃ B → ∀ {x} → x ∈ A → x ∈ B
    ≃-elimᴸ (≃-intro x∈A↔x∈B) = ↔-elimᴸ x∈A↔x∈B

    ≃-elimᴿ : A ≃ B → ∀ {x} → x ∈ B → x ∈ A
    ≃-elimᴿ (≃-intro x∈A↔x∈B) = ↔-elimᴿ x∈A↔x∈B

    ≃-refl : A ≃ A
    ≃-refl = ≃-intro ↔-refl

    ≃-sym : A ≃ B → B ≃ A
    ≃-sym (≃-intro x∈A↔x∈B) = ≃-intro (↔-sym x∈A↔x∈B)

    ≃-trans : A ≃ B → B ≃ C → A ≃ C
    ≃-trans (≃-intro x∈A↔x∈B) (≃-intro x∈B↔x∈C) =
      ≃-intro (↔-trans x∈A↔x∈B x∈B↔x∈C)

    ≃-IsEquivalence : IsEquivalence (_≃_ {σ₁} {σ₂} {S})
    ≃-IsEquivalence = record { refl = ≃-refl ; sym = ≃-sym ; trans = ≃-trans }

  -- Because PSet S has type Set (σ₁ ⊔ sℓ 0ℓ), the result Setoid must
  -- also have it. And because _≃_ then has type Set σ₁, that must be
  -- reflected in the second level parameter of the result Setoid
  PSet-Setoid : Setoid σ₁ 0ℓ → Setoid (σ₁ ⊔ sℓ 0ℓ) σ₁
  PSet-Setoid S =
    record { Carrier = PSet S ; _≈_ = _≃_ ; isEquivalence = ≃-IsEquivalence }

  private
    variable
      S : Setoid₀
      A B C : PSet₀ S

  ∈-substᴿ : {A B : PSet₀ S} {x : El S} → A ≃ B → x ∈ A → x ∈ B
  ∈-substᴿ (≃-intro x∈A↔x∈B) = ↔-elimᴸ x∈A↔x∈B

  ∈-substᴸ : {C : PSet (PSet-Setoid S)} → A ≃ B → A ∈ C → B ∈ C
  ∈-substᴸ = PSet-cong

  ∉-substᴿ : {A B : PSet₀ S} {x : El S} → A ≃ B → x ∉ A → x ∉ B
  ∉-substᴿ A≃B x∉A x∈B = x∉A (∈-substᴿ (≃-sym A≃B) x∈B)

  ∉-substᴸ : {C : PSet (PSet-Setoid S)} → A ≃ B → A ∉ C → B ∉ C
  ∉-substᴸ A≃B A∉C B∈C = A∉C (∈-substᴸ (≃-sym A≃B) B∈C)

  module ≃-Reasoning where

    infix 3 _∎
    infixr 2 _≃⟨⟩_ step-≃ step-≃˘
    infix 1 begin_

    begin_ : A ≃ B → A ≃ B
    begin A≃B = A≃B

    _≃⟨⟩_ : (A : PSet₀ S) → A ≃ B → A ≃ B
    _ ≃⟨⟩ A≃B = A≃B

    step-≃ : (A : PSet₀ S) → B ≃ C → A ≃ B → A ≃ C
    step-≃ _ B≃C A≃B = ≃-trans A≃B B≃C

    step-≃˘ : (A : PSet₀ S) → B ≃ C → B ≃ A → A ≃ C
    step-≃˘ _ B≃C B≃A = ≃-trans (≃-sym B≃A) B≃C

    _∎ : (A : PSet₀ S) → A ≃ A
    _ ∎ = ≃-refl

    syntax step-≃ A B≃C A≃B = A ≃⟨ A≃B ⟩ B≃C
    syntax step-≃˘ A B≃C B≃A = A ≃˘⟨ B≃A ⟩ B≃C
