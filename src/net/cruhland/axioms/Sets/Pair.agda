open import Level using (_⊔_; Level; Setω)
open import net.cruhland.axioms.DecEq using (_≃?_)
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Sets.Base using (SetAxioms)
import net.cruhland.axioms.Sets.Decidable as Decidable
import net.cruhland.axioms.Sets.Equality as Equality
open import net.cruhland.models.Function using (_∘_)
open import net.cruhland.models.Logic
  using ( _∨_; _∨?_; ∨-introᴸ; ∨-introᴿ; ∨-map
        ; _↔_; ↔-elimᴸ; ↔-elimᴿ; ↔-sym; ↔-trans; dec-map)
open import net.cruhland.models.Setoid using (DecSetoid; DecSetoid₀; El; Setoid)

module net.cruhland.axioms.Sets.Pair where

-- This Setoid also needs level parameters, to support nested sets
private
  variable
    σ₁ σ₂ : Level
    S : Setoid σ₁ σ₂

module PairDef (SA : SetAxioms) where
  open SetAxioms SA using (_∈_; PSet)

  is-pair : {S : Setoid σ₁ σ₂} → El S → El S → PSet S → Set (σ₁ ⊔ σ₂)
  is-pair {S = S} a b A = ∀ {x} → x ∈ A ↔ a ≈ x ∨ b ≈ x
    where open Setoid S using (_≈_)

record PairSet (SA : SetAxioms) : Setω where
  open Decidable SA using (DecMembership; ∈?-intro)
  private
    open module SE = Equality SA using (≃-intro)
  open PairDef SA using (is-pair)
  open SetAxioms SA using (_∈_; PSet)

  field
    pair : El S → El S → PSet S
    x∈pab↔a≈x∨b≈x :
      {S : Setoid σ₁ σ₂} {a b : El S} → is-pair {S = S} a b (pair a b)

  module _ {S : Setoid σ₁ σ₂} where
    open Setoid S using (_≈_) renaming (refl to ≈-refl; sym to ≈-sym)

    private
      variable
        a b x : El S

    x∈pab-elimᴸ : x ∈ pair {S = S} a b → x ≈ a ∨ x ≈ b
    x∈pab-elimᴸ = ∨-map ≈-sym ≈-sym ∘ (↔-elimᴸ x∈pab↔a≈x∨b≈x)

    x∈pab-elimᴿ : x ∈ pair {S = S} a b → a ≈ x ∨ b ≈ x
    x∈pab-elimᴿ = ↔-elimᴸ x∈pab↔a≈x∨b≈x

    x∈pab-intro : a ≈ x ∨ b ≈ x → x ∈ pair {S = S} a b
    x∈pab-intro = ↔-elimᴿ x∈pab↔a≈x∨b≈x

    x∈pab-introᴸ : a ≈ x → x ∈ pair {S = S} a b
    x∈pab-introᴸ = x∈pab-intro ∘ ∨-introᴸ

    x∈pab-introᴿ : b ≈ x → x ∈ pair {S = S} a b
    x∈pab-introᴿ = x∈pab-intro ∘ ∨-introᴿ

    a∈pab : a ∈ pair {S = S} a b
    a∈pab = x∈pab-introᴸ ≈-refl

    b∈pab : b ∈ pair {S = S} a b
    b∈pab = x∈pab-introᴿ ≈-refl

    pair-unique : {A : PSet S} → is-pair a b A → pair a b ≃ A
    pair-unique x∈A↔x≈a∨x≈b =
      ≃-intro (↔-trans x∈pab↔a≈x∨b≈x (↔-sym x∈A↔x≈a∨x≈b))

  instance
    pair-∈? :
      {{DS : DecSetoid₀}} →
        ∀ {a b} → DecMembership (pair {S = DecSetoid.setoid DS} a b)
    pair-∈? {{DS}} {a} {b} =
      ∈?-intro (λ {x} → dec-map x∈pab-intro x∈pab-elimᴿ (a ≃? x ∨? b ≃? x))
