open import net.cruhland.axioms.Sets.Base using (SetAxioms)
open import net.cruhland.axioms.Sets.Complement using (Complement)
open import net.cruhland.axioms.Sets.Difference using (Difference)
open import net.cruhland.axioms.Sets.Empty using (EmptySet)
open import net.cruhland.axioms.Sets.Intersection using (PairwiseIntersection)
open import net.cruhland.axioms.Sets.Union using (PairwiseUnion)

module net.cruhland.axioms.Sets.Properties
    (SA : SetAxioms)
    (CM : Complement SA)
    (ES : EmptySet SA)
    (PI : PairwiseIntersection SA)
    (PU : PairwiseUnion SA ES)
    (SD : Difference SA) where
  open Complement CM using (∁; x∈∁A-elim; x∈∁A-intro)
  open Difference SD using (_∖_; x∈A∖B-elim; x∈A∖B-intro)
  open EmptySet ES using (∅; x∉∅)
  open PairwiseIntersection PI using
    ( _∩_; ∩-comm; x∈A∩B-elim; x∈A∩B-elimᴸ; x∈A∩B-elimᴿ; x∈A∩B-intro₂
    ; ∩-substᴸ; ∩-substᴿ
    )
  open PairwiseUnion PU using
    ( _∪_; ∪-comm; x∈A∪B-elim; x∈A∪B-intro; x∈A∪B-introᴸ; x∈A∪B-introᴿ
    ; ∪-substᴸ; ∪-substᴿ
    )
  open SetAxioms SA using (_∈_; _∉_; PSet)

  open import Function using (_∘_; flip)
  open import net.cruhland.axioms.Sets.Base using
    (α; β; χ; σ₁; σ₂; El; S; Setoid)
  open import net.cruhland.axioms.Sets.Equality SA using
    (_≃_; ≃-trans; module ≃-Reasoning)
  open ≃-Reasoning
  open import net.cruhland.axioms.Sets.Subset SA using (_⊆_; ⊆-antisym; ⊆-intro)
  open import net.cruhland.models.Logic using
    (_∧_; ∧-intro; _∨_; ∨-introᴸ; ∨-introᴿ; ∨-map; ⊥-elim)

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

  ∩-over-∪ᴸ :
    {A : PSet S α} {B : PSet S β} {C : PSet S χ} → A ∩ (B ∪ C) ≃ A ∩ B ∪ A ∩ C
  ∩-over-∪ᴸ {A = A} {B} {C} =
    begin
      A ∩ (B ∪ C)
    ≃⟨ ∩-comm ⟩
      (B ∪ C) ∩ A
    ≃⟨ ∩-over-∪ᴿ ⟩
      B ∩ A ∪ C ∩ A
    ≃⟨ ∪-substᴸ ∩-comm ⟩
      A ∩ B ∪ C ∩ A
    ≃⟨ ∪-substᴿ ∩-comm ⟩
      A ∩ B ∪ A ∩ C
    ∎

  ∪-over-∩ᴸ :
    {A : PSet S α} {B : PSet S β} {C : PSet S χ} →
      A ∪ (B ∩ C) ≃ (A ∪ B) ∩ (A ∪ C)
  ∪-over-∩ᴸ {A = A} {B} {C} = ⊆-antisym (⊆-intro forward) (⊆-intro backward)
    where
      forward : ∀ {x} → x ∈ A ∪ (B ∩ C) → x ∈ (A ∪ B) ∩ (A ∪ C)
      forward x∈A∪[B∩C] with x∈A∪B-elim x∈A∪[B∩C]
      ... | ∨-introᴸ x∈A = x∈A∩B-intro₂ (x∈A∪B-introᴸ x∈A) (x∈A∪B-introᴸ x∈A)
      ... | ∨-introᴿ x∈B∩C =
        let ∧-intro x∈B x∈C = x∈A∩B-elim x∈B∩C
         in x∈A∩B-intro₂ (x∈A∪B-introᴿ x∈B) (x∈A∪B-introᴿ x∈C)

      backward : ∀ {x} → x ∈ (A ∪ B) ∩ (A ∪ C) → x ∈ A ∪ (B ∩ C)
      backward x∈[A∪B]∩[A∪C] with x∈A∪B-elim x∈A∪B | x∈A∪B-elim x∈A∪C
        where
          x∈A∪B = x∈A∩B-elimᴸ x∈[A∪B]∩[A∪C]
          x∈A∪C = x∈A∩B-elimᴿ x∈[A∪B]∩[A∪C]
      ... | ∨-introᴸ x∈A | ac = x∈A∪B-introᴸ x∈A
      ... | ∨-introᴿ x∈B | ∨-introᴸ x∈A = x∈A∪B-introᴸ x∈A
      ... | ∨-introᴿ x∈B | ∨-introᴿ x∈C = x∈A∪B-introᴿ (x∈A∩B-intro₂ x∈B x∈C)

  ∪-over-∩ᴿ :
    {A : PSet S α} {B : PSet S β} {C : PSet S χ} →
      (A ∩ B) ∪ C ≃ (A ∪ C) ∩ (B ∪ C)
  ∪-over-∩ᴿ {A = A} {B} {C} =
    begin
      (A ∩ B) ∪ C
    ≃⟨ ∪-comm ⟩
      C ∪ (A ∩ B)
    ≃⟨ ∪-over-∩ᴸ ⟩
      (C ∪ A) ∩ (C ∪ B)
    ≃⟨ ∩-substᴸ ∪-comm ⟩
      (A ∪ C) ∩ (C ∪ B)
    ≃⟨ ∩-substᴿ ∪-comm ⟩
      (A ∪ C) ∩ (B ∪ C)
    ∎

  A∖B≃A∩∁B : {A : PSet S α} {B : PSet S β} → A ∖ B ≃ A ∩ ∁ B
  A∖B≃A∩∁B {A = A} {B} = ⊆-antisym (⊆-intro forward) (⊆-intro backward)
    where
      forward : ∀ {x} → x ∈ A ∖ B → x ∈ A ∩ ∁ B
      forward x∈A∖B =
        let ∧-intro x∈A x∉B = x∈A∖B-elim x∈A∖B
         in x∈A∩B-intro₂ x∈A (x∈∁A-intro x∉B)

      backward : ∀ {x} → x ∈ A ∩ ∁ B → x ∈ A ∖ B
      backward x∈A∩∁B =
        let ∧-intro x∈A x∈∁B = x∈A∩B-elim x∈A∩∁B
         in x∈A∖B-intro (∧-intro x∈A (x∈∁A-elim x∈∁B))
