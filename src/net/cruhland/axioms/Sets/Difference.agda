open import net.cruhland.axioms.Sets.Base using (SetAxioms)
open import net.cruhland.axioms.Sets.Comprehension using (Comprehension)

module net.cruhland.axioms.Sets.Difference
  (SA : SetAxioms) (SC : Comprehension SA) where
open SetAxioms SA using (_∈_; _∉_; PSet; PSet-cong)
open Comprehension SC using (⟨_~_⟩; x∈⟨P⟩↔Px; congProp)

open import Function using (_∘_)
open import Level using (_⊔_)
open import net.cruhland.axioms.Sets.Base using (α; β; σ₁; σ₂; El; S; Setoid)
open import net.cruhland.models.Logic using
  (_∧_; ∧-elimᴸ; ∧-map; ↔-elimᴸ; ↔-elimᴿ; curry)

infixl 5 _∖_
_∖_ : {S : Setoid σ₁ σ₂} → PSet S α → PSet S β → PSet S (α ⊔ β)
_∖_ {α = α} {β = β} {S = S} A B = ⟨ in-diff ~ diff-cong ⟩
  where
    open Setoid S using (_≈_) renaming (sym to ≈-sym)

    in-diff : El S → Set (α ⊔ β)
    in-diff x = x ∈ A ∧ x ∉ B

    diff-cong : congProp {S = S} in-diff
    diff-cong x≈y = ∧-map (PSet-cong x≈y) (_∘ PSet-cong (≈-sym x≈y))

x∈A∖B-elim :
  {S : Setoid σ₁ σ₂} {A : PSet S α} {B : PSet S β} →
    ∀ {x} → x ∈ A ∖ B → x ∈ A ∧ x ∉ B
x∈A∖B-elim = ↔-elimᴸ x∈⟨P⟩↔Px

x∈A∖B-elimᴸ :
  {S : Setoid σ₁ σ₂} {A : PSet S α} {B : PSet S β} → ∀ {x} → x ∈ A ∖ B → x ∈ A
x∈A∖B-elimᴸ = ∧-elimᴸ ∘ x∈A∖B-elim

x∈A∖B-intro :
  {S : Setoid σ₁ σ₂} {A : PSet S α} {B : PSet S β} →
    ∀ {x} → x ∈ A ∧ x ∉ B → x ∈ A ∖ B
x∈A∖B-intro = ↔-elimᴿ x∈⟨P⟩↔Px

x∈A∖B-intro₂ :
  {S : Setoid σ₁ σ₂} {A : PSet S α} {B : PSet S β} →
    ∀ {x} → x ∈ A → x ∉ B → x ∈ A ∖ B
x∈A∖B-intro₂ = curry x∈A∖B-intro
