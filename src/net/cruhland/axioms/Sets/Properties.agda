open import net.cruhland.axioms.Sets.Base using (SetAxioms)
open import net.cruhland.axioms.Sets.Empty using (EmptySet)
open import net.cruhland.axioms.Sets.Intersection using (PairwiseIntersection)
open import net.cruhland.axioms.Sets.Union using (PairwiseUnion)

module net.cruhland.axioms.Sets.Properties
    (SA : SetAxioms)
    (ES : EmptySet SA)
    (PI : PairwiseIntersection SA)
    (PU : PairwiseUnion SA ES) where
  open EmptySet ES using (∅; x∉∅)
  open PairwiseIntersection PI using
    (_∩_; ∩-comm; x∈A∩B-elim; x∈A∩B-elimᴸ; x∈A∩B-intro₂)
  open PairwiseUnion PU using
    (_∪_; x∈A∪B-elim; x∈A∪B-intro; x∈A∪B-introᴸ; x∈A∪B-introᴿ)
  open SetAxioms SA using (_∈_; PSet)

  open import Function using (_∘_; flip)
  open import net.cruhland.axioms.Sets.Base using
    (α; β; χ; σ₁; σ₂; El; S; Setoid)
  open import net.cruhland.axioms.Sets.Equality SA using (_≃_; ≃-trans)
  open import net.cruhland.axioms.Sets.Subset SA using (_⊆_; ⊆-antisym; ⊆-intro)
  open import net.cruhland.models.Logic using
    (∧-intro; _∨_; ∨-introᴸ; ∨-introᴿ; ∨-map; ⊥-elim)

  ∅-⊆ : {A : PSet S α} → (∅ {α = α}) ⊆ A
  ∅-⊆ = ⊆-intro (⊥-elim ∘ x∉∅)

  A⊆∅→A≃∅ : {A : PSet S α} → A ⊆ (∅ {α = α}) → A ≃ ∅
  A⊆∅→A≃∅ A⊆∅ = ⊆-antisym A⊆∅ ∅-⊆

  ∪-⊆ᴸ : {A : PSet S α} {B : PSet S β} {C : PSet S χ} → A ∪ B ⊆ C → A ⊆ C
  ∪-⊆ᴸ (⊆-intro x∈A∪B→x∈C) = ⊆-intro (x∈A∪B→x∈C ∘ x∈A∪B-introᴸ)

  ∪-⊆ᴿ : {A : PSet S α} {B : PSet S β} {C : PSet S χ} → A ∪ B ⊆ C → B ⊆ C
  ∪-⊆ᴿ (⊆-intro x∈A∪B→x∈C) = ⊆-intro (x∈A∪B→x∈C ∘ x∈A∪B-introᴿ)

  ∩-∅ᴸ : {S : Setoid σ₁ σ₂} {A : PSet S α} → ∅ ∩ A ≃ (∅ {α = α})
  ∩-∅ᴸ = A⊆∅→A≃∅ (⊆-intro x∈A∩B-elimᴸ)

  ∩-∅ᴿ : {S : Setoid σ₁ σ₂} {A : PSet S α} → A ∩ ∅ ≃ (∅ {α = α})
  ∩-∅ᴿ = ≃-trans ∩-comm ∩-∅ᴸ

  ∩-over-∪ᴿ :
    {A : PSet S α} {B : PSet S β} {C : PSet S χ} → (A ∪ B) ∩ C ≃ A ∩ C ∪ B ∩ C
  ∩-over-∪ᴿ {A = A} {B} {C} = ⊆-antisym (⊆-intro forward) (⊆-intro backward)
    where
      forward : ∀ {x} → x ∈ (A ∪ B) ∩ C → x ∈ A ∩ C ∪ B ∩ C
      forward x∈[A∪B]∩C =
        let ∧-intro x∈A∪B x∈C = x∈A∩B-elim x∈[A∪B]∩C
            x∈A∨x∈B = x∈A∪B-elim x∈A∪B
            x∈A∩C∨x∈B∩C =
              ∨-map (flip x∈A∩B-intro₂ x∈C) (flip x∈A∩B-intro₂ x∈C) x∈A∨x∈B
         in x∈A∪B-intro x∈A∩C∨x∈B∩C

      backward : ∀ {x} → x ∈ A ∩ C ∪ B ∩ C → x ∈ (A ∪ B) ∩ C
      backward x∈A∩C∪B∩C with x∈A∪B-elim x∈A∩C∪B∩C
      ... | ∨-introᴸ x∈A∩C =
        let ∧-intro x∈A x∈C = x∈A∩B-elim x∈A∩C
         in x∈A∩B-intro₂ (x∈A∪B-introᴸ x∈A) x∈C
      ... | ∨-introᴿ x∈B∩C =
        let ∧-intro x∈B x∈C = x∈A∩B-elim x∈B∩C
         in x∈A∩B-intro₂ (x∈A∪B-introᴿ x∈B) x∈C
