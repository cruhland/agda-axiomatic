open import Level using (_⊔_; Level) renaming (suc to sℓ)
open import Relation.Binary using (IsEquivalence)
open import net.cruhland.axioms.Eq as Eq using (_≃_; Eq)
open import net.cruhland.axioms.Sets.Base using (SetAxioms)
open import net.cruhland.models.Logic
  using (contrapositive; _↔_; ↔-elimᴸ; ↔-elimᴿ; ↔-refl; ↔-sym; ↔-trans)
open import net.cruhland.models.Setoid using (El; Setoid; Setoid₀)

module net.cruhland.axioms.Sets.Equality (SA : SetAxioms) where
  open SetAxioms SA using (_∈_; _∉_; PSet; PSet₀; PSet-cong)

  private
    variable
      σ₁ σ₂ : Level

  infix 4 _≃₀_

  -- Comparing nested sets means the first level parameter can
  -- vary. And doubly-nested sets require the second level parameter
  -- to vary.
  record _≃₀_ {S : Setoid σ₁ σ₂} (A B : PSet S) : Set (sℓ (σ₁ ⊔ σ₂)) where
    constructor ≃-intro
    field
      ≃-elim : ∀ {x} → x ∈ A ↔ x ∈ B

  module _ {S : Setoid σ₁ σ₂} where
    private
      variable
        A B C : PSet S

    ≃-elimᴸ : A ≃₀ B → ∀ {x} → x ∈ A → x ∈ B
    ≃-elimᴸ (≃-intro x∈A↔x∈B) = ↔-elimᴸ x∈A↔x∈B

    ≃-elimᴿ : A ≃₀ B → ∀ {x} → x ∈ B → x ∈ A
    ≃-elimᴿ (≃-intro x∈A↔x∈B) = ↔-elimᴿ x∈A↔x∈B

    ≃₀-refl : A ≃₀ A
    ≃₀-refl = ≃-intro ↔-refl

    ≃₀-sym : A ≃₀ B → B ≃₀ A
    ≃₀-sym (≃-intro x∈A↔x∈B) = ≃-intro (↔-sym x∈A↔x∈B)

    ≃₀-trans : A ≃₀ B → B ≃₀ C → A ≃₀ C
    ≃₀-trans (≃-intro x∈A↔x∈B) (≃-intro x∈B↔x∈C) =
      ≃-intro (↔-trans x∈A↔x∈B x∈B↔x∈C)

    instance
      ≃₀-reflexive : Eq.Reflexive _≃₀_
      ≃₀-reflexive = Eq.reflexive ≃₀-refl

      ≃₀-symmetric : Eq.Symmetric _≃₀_
      ≃₀-symmetric = Eq.symmetric ≃₀-sym

      ≃₀-transitive : Eq.Transitive _≃₀_
      ≃₀-transitive = Eq.transitive ≃₀-trans

      eq : Eq (PSet S)
      eq = Eq.equivalence _≃₀_

    ≃₀-IsEquivalence : IsEquivalence (_≃₀_)
    ≃₀-IsEquivalence = record { refl = ≃₀-refl ; sym = ≃₀-sym ; trans = ≃₀-trans }

  -- Because PSet S has type Set (sℓ (σ₁ ⊔ σ₂)), the result Setoid
  -- must also have it. And because _≃₀_ also has type
  -- Set (sℓ (σ₁ ⊔ σ₂)), that must be reflected in the second level
  -- parameter of the result Setoid
  PSet-Setoid : Setoid σ₁ σ₂ → Setoid (sℓ (σ₁ ⊔ σ₂)) (sℓ (σ₁ ⊔ σ₂))
  PSet-Setoid S =
    record { Carrier = PSet S ; _≈_ = _≃₀_ ; isEquivalence = ≃₀-IsEquivalence }

  private
    variable
      S : Setoid₀
      A B C : PSet₀ S

  ∈-substᴿ : {A B : PSet₀ S} {x : El S} → A ≃ B → x ∈ A → x ∈ B
  ∈-substᴿ (≃-intro x∈A↔x∈B) = ↔-elimᴸ x∈A↔x∈B

  ∈-substᴸ : {C : PSet (PSet-Setoid S)} → A ≃ B → A ∈ C → B ∈ C
  ∈-substᴸ = PSet-cong

  ∉-substᴿ : {A B : PSet₀ S} {x : El S} → A ≃ B → x ∉ A → x ∉ B
  ∉-substᴿ A≃B x∉A = contrapositive (∈-substᴿ (Eq.sym A≃B)) x∉A

  ∉-substᴸ : {C : PSet (PSet-Setoid S)} → A ≃ B → A ∉ C → B ∉ C
  ∉-substᴸ A≃B A∉C = contrapositive (∈-substᴸ (Eq.sym A≃B)) A∉C
