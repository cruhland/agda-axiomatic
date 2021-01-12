module net.cruhland.axioms.Sets.Intersection where

open import Level using (Setω)
open import net.cruhland.axioms.Eq using (_≃_; sym; trans)
open import net.cruhland.axioms.Sets.Base using (SetAxioms)
import net.cruhland.axioms.Sets.Decidable as Decidable
import net.cruhland.axioms.Sets.Equality as Equality
import net.cruhland.axioms.Sets.Subset as Subset
open import net.cruhland.models.Function using (_∘_)
open import net.cruhland.models.Logic using
  ( _∧_; _∧?_; ∧-comm; ∧-dup; ∧-elimᴸ; ∧-elimᴿ; ∧-intro
  ; _↔_; ↔-elimᴸ; ↔-elimᴿ
  ; curry; Dec; dec-map
  )
open import net.cruhland.models.Setoid using (Setoid₀)

private
  variable
    S : Setoid₀

record PairwiseIntersection (SA : SetAxioms) : Setω where
  open Decidable SA using (_∈?_; DecMembership; ∈?-intro)
  private module ≃-SA = Equality SA
  open ≃-SA using (∈-substᴿ)
  open SetAxioms SA using (_∈_; PSet₀)
  open Subset SA using (_⊆_; ⊆-antisym; ⊆-intro)

  infixl 6 _∩_

  field
    _∩_ : PSet₀ S → PSet₀ S → PSet₀ S

  is-intersection : PSet₀ S → PSet₀ S → PSet₀ S → Set
  is-intersection A B A∩B = ∀ {x} → x ∈ A∩B ↔ x ∈ A ∧ x ∈ B

  field
    x∈A∩B↔x∈A∧x∈B : {A B : PSet₀ S} → is-intersection A B (A ∩ B)

  module _ {A B : PSet₀ S} where
    x∈A∩B-elim : ∀ {x} → x ∈ A ∩ B → x ∈ A ∧ x ∈ B
    x∈A∩B-elim = ↔-elimᴸ x∈A∩B↔x∈A∧x∈B

    x∈A∩B-elimᴸ : ∀ {x} → x ∈ A ∩ B → x ∈ A
    x∈A∩B-elimᴸ = ∧-elimᴸ ∘ x∈A∩B-elim

    x∈A∩B-elimᴿ : ∀ {x} → x ∈ A ∩ B → x ∈ B
    x∈A∩B-elimᴿ = ∧-elimᴿ ∘ x∈A∩B-elim

    x∈A∩B-intro : ∀ {x} → x ∈ A ∧ x ∈ B → x ∈ A ∩ B
    x∈A∩B-intro = ↔-elimᴿ x∈A∩B↔x∈A∧x∈B

    x∈A∩B-intro₂ : ∀ {x} → x ∈ A → x ∈ B → x ∈ A ∩ B
    x∈A∩B-intro₂ = curry x∈A∩B-intro

  private
    variable
      A B C : PSet₀ S

  ∩-comm : A ∩ B ≃ B ∩ A
  ∩-comm = ⊆-antisym AB⊆BA BA⊆AB
    where
      AB⊆BA = ⊆-intro (x∈A∩B-intro ∘ ∧-comm ∘ x∈A∩B-elim)
      BA⊆AB = ⊆-intro (x∈A∩B-intro ∘ ∧-comm ∘ x∈A∩B-elim)

  ∩-assoc : (A ∩ B) ∩ C ≃ A ∩ (B ∩ C)
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

  ∩-substᴸ : {A₁ A₂ : PSet₀ S} → A₁ ≃ A₂ → A₁ ∩ B ≃ A₂ ∩ B
  ∩-substᴸ {B = B} {A₁} {A₂} A₁≃A₂ =
    ⊆-antisym (⊆-intro forward) (⊆-intro backward)
      where
        forward : ∀ {x} → x ∈ A₁ ∩ B → x ∈ A₂ ∩ B
        forward x∈A₁B =
          let ∧-intro x∈A₁ x∈B = x∈A∩B-elim x∈A₁B
           in x∈A∩B-intro₂ (∈-substᴿ A₁≃A₂ x∈A₁) x∈B

        backward : ∀ {x} → x ∈ A₂ ∩ B → x ∈ A₁ ∩ B
        backward x∈A₂B =
          let ∧-intro x∈A₂ x∈B = x∈A∩B-elim x∈A₂B
           in x∈A∩B-intro₂ (∈-substᴿ (sym A₁≃A₂) x∈A₂) x∈B

  ∩-substᴿ : {B₁ B₂ : PSet₀ S} → B₁ ≃ B₂ → A ∩ B₁ ≃ A ∩ B₂
  ∩-substᴿ B₁≃B₂ = trans ∩-comm (trans (∩-substᴸ B₁≃B₂) ∩-comm)

  ∩-idempotent : A ∩ A ≃ A
  ∩-idempotent = ⊆-antisym (⊆-intro x∈A∩B-elimᴸ) (⊆-intro (x∈A∩B-intro ∘ ∧-dup))

  instance
    ∩-∈? :
      {{_ : DecMembership A}} {{_ : DecMembership B}} → DecMembership (A ∩ B)
    ∩-∈? {A = A} {B} =
      ∈?-intro
        (λ {x} → dec-map x∈A∩B-intro x∈A∩B-elim (x ∈? A ∧? x ∈? B))
