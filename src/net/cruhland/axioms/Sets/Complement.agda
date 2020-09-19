module net.cruhland.axioms.Sets.Complement where

open import Level using (Setω)
open import net.cruhland.axioms.Sets.Base using (SetAxioms)
import net.cruhland.axioms.Sets.Decidable as Decidable
open import net.cruhland.models.Logic using
  (_↔_; ↔-elimᴸ; ↔-elimᴿ; ¬?; Dec; dec-map)
open import net.cruhland.models.Setoid using (Setoid₀)

private
  variable
    S : Setoid₀

record Complement (SA : SetAxioms) : Setω where
  open Decidable SA using (_∈?_; DecMembership; ∈?-intro)
  open SetAxioms SA using (_∈_; _∉_; PSet₀)

  field
    ∁ : PSet₀ S → PSet₀ S

  is-complement : PSet₀ S → PSet₀ S → Set
  is-complement A ∁A = ∀ {x} → x ∈ ∁A ↔ x ∉ A

  field
    x∈∁A↔x∉A : {A : PSet₀ S} → is-complement A (∁ A)

  x∈∁A-elim : {A : PSet₀ S} → ∀ {x} → x ∈ ∁ A → x ∉ A
  x∈∁A-elim = ↔-elimᴸ x∈∁A↔x∉A

  x∈∁A-intro : {A : PSet₀ S} → ∀ {x} → x ∉ A → x ∈ ∁ A
  x∈∁A-intro = ↔-elimᴿ x∈∁A↔x∉A

  instance
    ∁-∈? : {A : PSet₀ S} {{_ : DecMembership A}} → DecMembership (∁ A)
    ∁-∈? {A = A} = ∈?-intro (λ {x} → dec-map x∈∁A-intro x∈∁A-elim (¬? (x ∈? A)))
