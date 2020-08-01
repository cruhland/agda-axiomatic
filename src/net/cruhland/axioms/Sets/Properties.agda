open import net.cruhland.axioms.Sets.Base using (SetAxioms)
open import net.cruhland.axioms.Sets.Empty using (EmptySet)
open import net.cruhland.axioms.Sets.Union using (PairwiseUnion)

module net.cruhland.axioms.Sets.Properties
    (SA : SetAxioms) (ES : EmptySet SA) (PU : PairwiseUnion SA ES) where
  open PairwiseUnion PU using (_∪_; x∈A∪B-introᴸ; x∈A∪B-introᴿ)
  open SetAxioms SA using (PSet)

  open import Function using (_∘_)
  open import net.cruhland.axioms.Sets.Base using (α; β; χ; S)
  open import net.cruhland.axioms.Sets.Subset SA using (_⊆_; ⊆-intro)

  ∪-⊆ᴸ : {A : PSet S α} {B : PSet S β} {C : PSet S χ} → A ∪ B ⊆ C → A ⊆ C
  ∪-⊆ᴸ (⊆-intro x∈A∪B→x∈C) = ⊆-intro (x∈A∪B→x∈C ∘ x∈A∪B-introᴸ)

  ∪-⊆ᴿ : {A : PSet S α} {B : PSet S β} {C : PSet S χ} → A ∪ B ⊆ C → B ⊆ C
  ∪-⊆ᴿ (⊆-intro x∈A∪B→x∈C) = ⊆-intro (x∈A∪B→x∈C ∘ x∈A∪B-introᴿ)
