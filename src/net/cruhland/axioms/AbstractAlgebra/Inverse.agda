module net.cruhland.axioms.AbstractAlgebra.Inverse where

open import net.cruhland.axioms.AbstractAlgebra.Base using
  (forHand; Hand; handᴸ; handᴿ)
open import net.cruhland.axioms.AbstractAlgebra.Reductive using
  (Identityᴸ; identᴸ; Identityᴿ; identᴿ)
open import net.cruhland.axioms.Eq as Eq using (_≃_; Eq)
open import net.cruhland.models.Function using
  (ConstrainableFn; flip; toConstrainedFn)

record Inverse (hand : Hand) {A F : Set} {{_ : Eq A}} (f : F) : Set₁ where
  constructor inverse
  field
    {_⊙_} : A → A → A
    {e} : A
    {{idᴸ}} : Identityᴸ _⊙_ e
    {{idᴿ}} : Identityᴿ _⊙_ e
    {{cf}} : ConstrainableFn F

  open ConstrainableFn cf using (C)
  invert = toConstrainedFn f
  _<⊙>_ = forHand hand _⊙_

  field
    inv : ∀ {a} {{c : C a}} → invert a <⊙> a ≃ e

open Inverse {{...}} public using (inv)

invᴸ = inv {handᴸ}
invᴿ = inv {handᴿ}

{--- Equivalences ---}

module _ {A F : Set} {f : F} {{_ : Eq A}} where

  inverseᴸ-flip-inverseᴿ : {{_ : Inverse handᴿ f}} → Inverse handᴸ f
  inverseᴸ-flip-inverseᴿ {{i}} =
    inverse
      {_⊙_ = flip (Inverse._⊙_ i)}
      {{idᴸ = record { identᴸ = identᴿ }}}
      {{idᴿ = record { identᴿ = identᴸ }}}
      inv

  inverseᴿ-flip-inverseᴸ : {{_ : Inverse handᴸ f}} → Inverse handᴿ f
  inverseᴿ-flip-inverseᴸ {{i}} =
    inverse
      {_⊙_ = flip (Inverse._⊙_ i)}
      {{idᴸ = record { identᴸ = identᴿ }}}
      {{idᴿ = record { identᴿ = identᴸ }}}
      inv
