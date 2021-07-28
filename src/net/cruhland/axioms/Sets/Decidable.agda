open import net.cruhland.axioms.Sets.Base using (SetAxioms)
open import net.cruhland.models.Logic using (Dec)
open import net.cruhland.models.Setoid using (El; Setoid₀)

module net.cruhland.axioms.Sets.Decidable (SA : SetAxioms) where
open SetAxioms SA using (_∈_; PSet₀)

record DecMembership {S : Setoid₀} (A : PSet₀ S) : Set where
  constructor ∈?-intro
  field
    ∈?-elim : ∀ {x} → Dec (x ∈ A)

open DecMembership {{...}} public

_∈?_ :
  {S : Setoid₀} (x : El S) (A : PSet₀ S) {{_ : DecMembership A}} → Dec (x ∈ A)
x ∈? A = ∈?-elim
