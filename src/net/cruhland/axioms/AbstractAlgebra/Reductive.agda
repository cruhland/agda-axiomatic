module net.cruhland.axioms.AbstractAlgebra.Reductive where

open import net.cruhland.axioms.Eq as Eq using (_≃_; Eq)
open import net.cruhland.models.Function using (flip)

open import net.cruhland.axioms.AbstractAlgebra.Base using
  (forHand; Hand; handᴸ; handᴿ)
open import net.cruhland.axioms.AbstractAlgebra.Swappable using
  (comm; Commutative)

record Identity
    (hand : Hand) {A : Set} {{_ : Eq A}} (_⊙_ : A → A → A) (e : A) : Set where
  constructor identity
  _<⊙>_ = forHand hand _⊙_
  field
    ident : ∀ {a} → e <⊙> a ≃ a

open Identity {{...}} public using (ident)

identᴸ = ident {handᴸ}
identᴿ = ident {handᴿ}

identityᴿ-from-identityᴸ :
  {A : Set} {_⊙_ : A → A → A} {e : A} →
    ∀ {{_ : Eq A}} {{_ : Commutative _⊙_}} {{_ : Identity handᴸ _⊙_ e}} →
      Identity handᴿ _⊙_ e
identityᴿ-from-identityᴸ = identity (Eq.trans comm ident)

record Identity₂ {A : Set} {{_ : Eq A}} (_⊙_ : A → A → A) (e : A) : Set where
  constructor identity₂
  field
    {{identityᴸ}} : Identity handᴸ _⊙_ e
    {{identityᴿ}} : Identity handᴿ _⊙_ e

record Absorptive
    (hand : Hand) {A : Set} {{_ : Eq A}} (_⊙_ : A → A → A) (z : A) : Set where
  constructor absorptive
  _<⊙>_ = forHand hand _⊙_
  field
    absorb : ∀ {a} → z <⊙> a ≃ z

open Absorptive {{...}} public using (absorb)

absorbᴸ = absorb {handᴸ}
absorbᴿ = absorb {handᴿ}

absorptiveᴿ-from-absorptiveᴸ :
  {A : Set} {_⊙_ : A → A → A} {z : A}
    {{_ : Eq A}} {{_ : Commutative _⊙_}} {{_ : Absorptive handᴸ _⊙_ z}} →
      Absorptive handᴿ _⊙_ z
absorptiveᴿ-from-absorptiveᴸ = absorptive (Eq.trans comm absorb)

{--- Equivalences ---}

module _ {A : Set} {_⊙_ : A → A → A} {e : A} {{_ : Eq A}} where

  identityᴸ-flip : {{_ : Identity handᴿ _⊙_ e}} → Identity handᴸ (flip _⊙_) e
  identityᴸ-flip = identity ident

  identityᴿ-flip : {{_ : Identity handᴸ _⊙_ e}} → Identity handᴿ (flip _⊙_) e
  identityᴿ-flip = identity ident

  identity₂-flip : {{_ : Identity₂ _⊙_ e}} → Identity₂ (flip _⊙_) e
  identity₂-flip =
    identity₂ {{identityᴸ = identityᴸ-flip}} {{identityᴿ = identityᴿ-flip}}
