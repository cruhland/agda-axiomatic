module net.cruhland.axioms.AbstractAlgebra.Inverse where

open import net.cruhland.axioms.AbstractAlgebra.Reductive using
  (Identityᴸ; Identityᴿ)
open import net.cruhland.axioms.Eq as Eq using (_≃_; Eq)
open import net.cruhland.models.Function using (ConstrainableFn; toConstrainedFn)

record Inverseᴸ {A F : Set} {{_ : Eq A}} (f : F) : Set₁ where
  constructor inverseᴸ
  field
    {{cf}} : ConstrainableFn F

  open ConstrainableFn cf using (C)
  inv = toConstrainedFn f

  field
    {_⊙_} : A → A → A
    {e} : A
    {{idᴸ}} : Identityᴸ _⊙_ e
    {{idᴿ}} : Identityᴿ _⊙_ e
    invᴸ : ∀ {a} {{c : C a}} → inv a ⊙ a ≃ e

open Inverseᴸ {{...}} public using (invᴸ)

record Inverseᴿ {A F : Set} {{_ : Eq A}} (f : F) : Set₁ where
  constructor inverseᴿ
  field
    {{cf}} : ConstrainableFn F

  open ConstrainableFn cf using (C)
  inv = toConstrainedFn f

  field
    {_⊙_} : A → A → A
    {e} : A
    {{idᴸ}} : Identityᴸ _⊙_ e
    {{idᴿ}} : Identityᴿ _⊙_ e
    invᴿ : ∀ {a} {{c : C a}} → a ⊙ inv a ≃ e

open Inverseᴿ {{...}} public using (invᴿ)
