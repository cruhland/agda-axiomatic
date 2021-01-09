module net.cruhland.axioms.AbstractAlgebra.Inverse where

open import net.cruhland.axioms.AbstractAlgebra.Reductive using
  (Identityᴸ; Identityᴿ)
open import net.cruhland.axioms.Eq as Eq using (_≃_; Eq)

record Inverseᴸ {A : Set} {{_ : Eq A}} (inv : A → A) : Set where
  constructor inverseᴸ
  field
    {_⊙_} : A → A → A
    {e} : A
    {{idᴸ}} : Identityᴸ _⊙_ e
    {{idᴿ}} : Identityᴿ _⊙_ e
    invᴸ : ∀ {a} → inv a ⊙ a ≃ e

open Inverseᴸ {{...}} public using (invᴸ)
