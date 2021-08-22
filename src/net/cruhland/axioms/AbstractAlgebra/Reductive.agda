open import net.cruhland.axioms.Eq as Eq using (_≃_; Eq)
open import net.cruhland.models.Function using (flip)
open import net.cruhland.models.Literals

module net.cruhland.axioms.AbstractAlgebra.Reductive where

private
  module AA where
    open import net.cruhland.axioms.AbstractAlgebra.Base public
    open import net.cruhland.axioms.AbstractAlgebra.Swappable public

record Identity
    (hand : AA.Hand) {A : Set} {{_ : Eq A}} (_⊙_ : A → A → A) (e : A)
    : Set where
  constructor identity
  _<⊙>_ = AA.forHand hand _⊙_
  field
    ident : ∀ {a} → e <⊙> a ≃ a

open Identity {{...}} public using (ident)

identᴸ = ident {AA.handᴸ}
identᴿ = ident {AA.handᴿ}

identityᴿ-from-identityᴸ :
  {A : Set} {_⊙_ : A → A → A} {e : A} →
    ∀ {{_ : Eq A}} {{_ : AA.Commutative _⊙_}} {{_ : Identity AA.handᴸ _⊙_ e}} →
      Identity AA.handᴿ _⊙_ e
identityᴿ-from-identityᴸ = identity (Eq.trans AA.comm ident)

record Identity² {A : Set} {{_ : Eq A}} (_⊙_ : A → A → A) (e : A) : Set where
  constructor identity²
  field
    {{identityᴸ}} : Identity AA.handᴸ _⊙_ e
    {{identityᴿ}} : Identity AA.handᴿ _⊙_ e

record Absorptive
    (hand : AA.Hand) {A B : Set} {C : A → A → Set}
    {{_ : Eq B}} {{_ : FromNatLiteral A}} {{_ : FromNatLiteral B}}
    (_⊙_ : (x y : A) {{_ : C x y}} → B)
    : Set where
  constructor absorptive
  C˘ = AA.forHand hand C
  _⊙˘_ = AA.forHandᶜ hand _⊙_
  field
    absorb : ∀ {a} {{_ : C˘ 0 a}} → 0 ⊙˘ a ≃ 0

open Absorptive {{...}} public using (absorb)

absorbᴸ = absorb {AA.handᴸ}
absorbᴿ = absorb {AA.handᴿ}

absorptiveᴿ-from-absorptiveᴸ :
  {A : Set} {_⊙_ : A → A → A} {{_ : Eq A}} {{_ : FromNatLiteral A}}
  {{_ : AA.Commutative _⊙_}} {{_ : Absorptive AA.handᴸ (AA.tc₂ _⊙_)}} →
  Absorptive AA.handᴿ (AA.tc₂ _⊙_)
absorptiveᴿ-from-absorptiveᴸ = absorptive (Eq.trans AA.comm absorb)

record Absorptive²
    {A : Set} {C : A → A → Set} {{_ : Eq A}} {{_ : FromNatLiteral A}}
    (_⊙_ : (x y : A) {{_ : C x y}} → A)
    : Set where
  constructor absorptive²
  field
    {{absorptiveᴸ}} : Absorptive AA.handᴸ _⊙_
    {{absorptiveᴿ}} : Absorptive AA.handᴿ _⊙_

{--- Equivalences ---}

module _ {A : Set} {_⊙_ : A → A → A} {e : A} {{_ : Eq A}} where

  identityᴸ-flip :
    {{_ : Identity AA.handᴿ _⊙_ e}} → Identity AA.handᴸ (flip _⊙_) e
  identityᴸ-flip = identity ident

  identityᴿ-flip :
    {{_ : Identity AA.handᴸ _⊙_ e}} → Identity AA.handᴿ (flip _⊙_) e
  identityᴿ-flip = identity ident

  identity²-flip : {{_ : Identity² _⊙_ e}} → Identity² (flip _⊙_) e
  identity²-flip =
    identity² {{identityᴸ = identityᴸ-flip}} {{identityᴿ = identityᴿ-flip}}
