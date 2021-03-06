module net.cruhland.axioms.Sets.Comprehension where

open import Level using (Setω)
open import net.cruhland.axioms.Sets.Base using (SetAxioms)
import net.cruhland.axioms.Sets.Decidable as Decidable
open import net.cruhland.models.Logic using
  (_↔_; ↔-elimᴸ; ↔-elimᴿ; Dec; dec-map)
open import net.cruhland.models.Setoid using (_⟨$⟩_; Setoid₀; SPred₀)

private
  variable
    S : Setoid₀
    P : SPred₀ S

record Comprehension (SA : SetAxioms) : Setω where
  open Decidable SA using (DecMembership; ∈?-intro)
  open SetAxioms SA using (_∈_; PSet₀)

  field
    ⟨_⟩ : SPred₀ S → PSet₀ S
    x∈⟨P⟩↔Px : {P : SPred₀ S} → ∀ {x} → x ∈ ⟨ P ⟩ ↔ P ⟨$⟩ x

  x∈⟨P⟩-elim : {P : SPred₀ S} → ∀ {x} → x ∈ ⟨ P ⟩ → P ⟨$⟩ x
  x∈⟨P⟩-elim = ↔-elimᴸ x∈⟨P⟩↔Px

  x∈⟨P⟩-intro : {P : SPred₀ S} → ∀ {x} → P ⟨$⟩ x → x ∈ ⟨ P ⟩
  x∈⟨P⟩-intro = ↔-elimᴿ x∈⟨P⟩↔Px

  instance
    ⟨P⟩-∈? : {{decP : ∀ {x} → Dec (P ⟨$⟩ x)}} → DecMembership ⟨ P ⟩
    ⟨P⟩-∈? {{decP}} = ∈?-intro (dec-map x∈⟨P⟩-intro x∈⟨P⟩-elim decP)
