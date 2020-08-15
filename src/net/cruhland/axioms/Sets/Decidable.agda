open import Level using (_⊔_)
open import Relation.Nullary using (Dec)
open import net.cruhland.axioms.Sets.Base using
  (α; σ₁; σ₂; El; S; SetAxioms; Setoid)

module net.cruhland.axioms.Sets.Decidable (SA : SetAxioms) where
open SetAxioms SA using (_∈_; PSet)

record DecMembership {S : Setoid σ₁ σ₂} (A : PSet S α) : Set (σ₁ ⊔ α) where
  constructor ∈?-intro
  field
    ∈?-elim : ∀ {x} → Dec (x ∈ A)

open DecMembership {{...}} public

_∈?_ :
  {S : Setoid σ₁ σ₂} (x : El S) (A : PSet S α) →
    {{_ : DecMembership A}} → Dec (x ∈ A)
x ∈? A = ∈?-elim
