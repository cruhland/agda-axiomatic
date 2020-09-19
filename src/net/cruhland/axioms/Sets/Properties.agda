open import Function using (_∘_; flip)
open import Level using (0ℓ)
open import net.cruhland.axioms.Sets.Base using (SetAxioms)
open import net.cruhland.axioms.Sets.Complement using (Complement)
open import net.cruhland.axioms.Sets.Difference using (Difference)
open import net.cruhland.axioms.Sets.Empty using (EmptySet)
import net.cruhland.axioms.Sets.Equality as Equality
open import net.cruhland.axioms.Sets.Intersection using (PairwiseIntersection)
open import net.cruhland.axioms.Sets.Pair using (PairSet)
open import net.cruhland.axioms.Sets.Singleton using (SingletonSet)
import net.cruhland.axioms.Sets.Subset as Subset
open import net.cruhland.axioms.Sets.Union using (PairwiseUnion)
open import net.cruhland.models.Logic using
  (_∧_; ∧-intro; _∨_; ∨-introᴸ; ∨-introᴿ; ∨-map; ∨-rec; ⊥-elim)
open import net.cruhland.models.Setoid using (El; Setoid; Setoid₀)

module net.cruhland.axioms.Sets.Properties
    (SA : SetAxioms)
    (CM : Complement SA)
    (ES : EmptySet SA)
    (PI : PairwiseIntersection SA)
    (PS : PairSet SA)
    (PU : PairwiseUnion SA ES)
    (SD : Difference SA)
    (SS : SingletonSet SA) where
  open Complement CM using (∁; x∈∁A-elim; x∈∁A-intro)
  open Difference SD using (_∖_; x∈A∖B-elim; x∈A∖B-elimᴸ; x∈A∖B-intro)
  open EmptySet ES using (∅; x∉∅)
  open Equality SA using (_≃_; ≃-trans; module ≃-Reasoning)
  open ≃-Reasoning
  open PairSet PS using (pair; x∈pab-elimᴿ; x∈pab-introᴸ; x∈pab-introᴿ)
  open PairwiseIntersection PI using
    ( _∩_; ∩-comm; x∈A∩B-elim; x∈A∩B-elimᴸ; x∈A∩B-elimᴿ; x∈A∩B-intro₂
    ; ∩-substᴸ; ∩-substᴿ
    )
  open PairwiseUnion PU using
    ( _∪_; ∪-comm; x∈A∪B-elim; x∈A∪B-intro; x∈A∪B-introᴸ; x∈A∪B-introᴿ
    ; ∪-substᴸ; ∪-substᴿ
    )
  open SetAxioms SA using (_∈_; _∉_; PSet; PSet₀)
  open SingletonSet SS using (singleton; x∈sa-elim; x∈sa-intro)
  open Subset SA using (_⊆_; ⊆-antisym; ⊆-intro)

  private
    variable
      S : Setoid₀
      A B C : PSet₀ S

  ∅-⊆ : ∅ ⊆ A
  ∅-⊆ = ⊆-intro (⊥-elim ∘ x∉∅)

  A⊆∅→A≃∅ : A ⊆ ∅ → A ≃ ∅
  A⊆∅→A≃∅ A⊆∅ = ⊆-antisym A⊆∅ ∅-⊆

  ∪⊆-elimᴸ : A ∪ B ⊆ C → A ⊆ C
  ∪⊆-elimᴸ (⊆-intro x∈A∪B→x∈C) = ⊆-intro (x∈A∪B→x∈C ∘ x∈A∪B-introᴸ)

  ∪⊆-elimᴿ : A ∪ B ⊆ C → B ⊆ C
  ∪⊆-elimᴿ (⊆-intro x∈A∪B→x∈C) = ⊆-intro (x∈A∪B→x∈C ∘ x∈A∪B-introᴿ)

  ∪⊆-elim : A ∪ B ⊆ C → A ⊆ C ∧ B ⊆ C
  ∪⊆-elim A∪B⊆C = ∧-intro (∪⊆-elimᴸ A∪B⊆C) (∪⊆-elimᴿ A∪B⊆C)

  ⊆∪-introᴸ : A ⊆ A ∪ B
  ⊆∪-introᴸ = ⊆-intro x∈A∪B-introᴸ

  ⊆∪-introᴿ : B ⊆ A ∪ B
  ⊆∪-introᴿ = ⊆-intro x∈A∪B-introᴿ

  ∪⊆-intro₂ : A ⊆ C → B ⊆ C → A ∪ B ⊆ C
  ∪⊆-intro₂ (⊆-intro x∈A→x∈C) (⊆-intro x∈B→x∈C) =
    ⊆-intro (∨-rec x∈A→x∈C x∈B→x∈C ∘ x∈A∪B-elim)

  pab≃sa∪sb : {a b : El S} → pair a b ≃ singleton {S = S} a ∪ singleton b
  pab≃sa∪sb {S = S} {a} {b} = ⊆-antisym (⊆-intro forward) (⊆-intro backward)
    where
      open Setoid S using (_≈_)

      forward : ∀ {x} → x ∈ pair a b → x ∈ singleton a ∪ singleton b
      forward x∈pab with x∈pab-elimᴿ x∈pab
      ... | ∨-introᴸ x≈a = x∈A∪B-introᴸ (x∈sa-intro x≈a)
      ... | ∨-introᴿ x≈b = x∈A∪B-introᴿ (x∈sa-intro x≈b)

      backward : ∀ {x} → x ∈ singleton a ∪ singleton b → x ∈ pair a b
      backward x∈sa∪sb with x∈A∪B-elim x∈sa∪sb
      ... | ∨-introᴸ x∈sa = x∈pab-introᴸ (x∈sa-elim x∈sa)
      ... | ∨-introᴿ x∈sb = x∈pab-introᴿ (x∈sa-elim x∈sb)

  ∩-∅ᴸ : ∅ ∩ A ≃ ∅
  ∩-∅ᴸ = A⊆∅→A≃∅ (⊆-intro x∈A∩B-elimᴸ)

  ∩-∅ᴿ : A ∩ ∅ ≃ ∅
  ∩-∅ᴿ = ≃-trans ∩-comm ∩-∅ᴸ

  ∩⊆-introᴸ : A ∩ B ⊆ A
  ∩⊆-introᴸ = ⊆-intro x∈A∩B-elimᴸ

  ∩⊆-introᴿ : A ∩ B ⊆ B
  ∩⊆-introᴿ = ⊆-intro x∈A∩B-elimᴿ

  ⊆∩-intro₂ : C ⊆ A → C ⊆ B → C ⊆ A ∩ B
  ⊆∩-intro₂ (⊆-intro x∈C→x∈A) (⊆-intro x∈C→x∈B) =
    ⊆-intro λ x∈C → x∈A∩B-intro₂ (x∈C→x∈A x∈C) (x∈C→x∈B x∈C)

  ⊆∩-elimᴸ : C ⊆ A ∩ B → C ⊆ A
  ⊆∩-elimᴸ (⊆-intro x∈C→x∈A∩B) = ⊆-intro (x∈A∩B-elimᴸ ∘ x∈C→x∈A∩B)

  ⊆∩-elimᴿ : C ⊆ A ∩ B → C ⊆ B
  ⊆∩-elimᴿ (⊆-intro x∈C→x∈A∩B) = ⊆-intro (x∈A∩B-elimᴿ ∘ x∈C→x∈A∩B)

  ⊆∩-elim : C ⊆ A ∩ B → C ⊆ A ∧ C ⊆ B
  ⊆∩-elim C⊆A∩B = ∧-intro (⊆∩-elimᴸ C⊆A∩B) (⊆∩-elimᴿ C⊆A∩B)

  ∩-preserves-⊆ᴸ : A ⊆ B → C ∩ A ⊆ C ∩ B
  ∩-preserves-⊆ᴸ {A = A} {B} {C} (⊆-intro x∈A→x∈B) = ⊆-intro x∈C∩A→x∈C∩B
    where
      x∈C∩A→x∈C∩B : ∀ {x} → x ∈ C ∩ A → x ∈ C ∩ B
      x∈C∩A→x∈C∩B x∈C∩A =
        let ∧-intro x∈C x∈A = x∈A∩B-elim x∈C∩A
         in x∈A∩B-intro₂ x∈C (x∈A→x∈B x∈A)

  ∩-over-∪ᴿ : (A ∪ B) ∩ C ≃ A ∩ C ∪ B ∩ C
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

  ∩-over-∪ᴸ : A ∩ (B ∪ C) ≃ A ∩ B ∪ A ∩ C
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

  ∪-over-∩ᴸ : A ∪ (B ∩ C) ≃ (A ∪ B) ∩ (A ∪ C)
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

  ∪-over-∩ᴿ : (A ∩ B) ∪ C ≃ (A ∪ C) ∩ (B ∪ C)
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

  A∖B≃A∩∁B : A ∖ B ≃ A ∩ ∁ B
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

  A∖B⊆A : A ∖ B ⊆ A
  A∖B⊆A = ⊆-intro x∈A∖B-elimᴸ
