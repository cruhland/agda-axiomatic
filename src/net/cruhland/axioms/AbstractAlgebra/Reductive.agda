module net.cruhland.axioms.AbstractAlgebra.Reductive where

open import net.cruhland.axioms.AbstractAlgebra.Base using
  (forHand; Hand; handᴸ; handᴿ)
open import net.cruhland.axioms.AbstractAlgebra.Commutative using
  (comm; Commutative)
open import net.cruhland.axioms.Eq as Eq using (_≃_; Eq)
open import net.cruhland.models.Function using (flip)

IsIdentity :
  (hand : Hand) {A : Set} {{_ : Eq A}} (_⊙_ : A → A → A) (e : A) → Set
IsIdentity hand _⊙_ e = let _<⊙>_ = forHand hand _⊙_ in ∀ {a} → e <⊙> a ≃ a

record Identity
    (hand : Hand) {A : Set} {{_ : Eq A}} (_⊙_ : A → A → A) : Set where
  constructor identity
  field
    {id-elem} : A
    ident : IsIdentity hand _⊙_ id-elem

open Identity {{...}} public using (ident; id-elem)

identᴸ = ident {handᴸ}
identᴿ = ident {handᴿ}

identityᴿ-from-identityᴸ :
  {A : Set} {_⊙_ : A → A → A} →
    ∀ {{_ : Eq A}} {{_ : Commutative _⊙_}} {{_ : Identity handᴸ _⊙_}} →
      Identity handᴿ _⊙_
identityᴿ-from-identityᴸ = identity (Eq.trans comm ident)

record Identity₂ {A : Set} {{_ : Eq A}} (_⊙_ : A → A → A) : Set where
  constructor identity₂
  field
    {{identityᴸ}} : Identity handᴸ _⊙_
    {{identityᴿ}} : Identity handᴿ _⊙_

  id₂-elem = id-elem {{r = identityᴸ}}

open Identity₂ {{...}} public using (id₂-elem)

IsAbsorptive :
  (hand : Hand) {A : Set} {{_ : Eq A}} (_⊙_ : A → A → A) (z : A) → Set
IsAbsorptive hand _⊙_ z = let _<⊙>_ = forHand hand _⊙_ in ∀ {a} → z <⊙> a ≃ z

record Absorptive
    (hand : Hand) {A : Set} {{_ : Eq A}} (_⊙_ : A → A → A) : Set where
  constructor absorptive
  field
    {z} : A
    absorb : IsAbsorptive hand _⊙_ z

open Absorptive {{...}} public using (absorb)

absorbᴸ = absorb {handᴸ}
absorbᴿ = absorb {handᴿ}

absorptiveᴿ-from-absorptiveᴸ :
  {A : Set} {_⊙_ : A → A → A}
    {{_ : Eq A}} {{_ : Commutative _⊙_}} {{_ : Absorptive handᴸ _⊙_}} →
      Absorptive handᴿ _⊙_
absorptiveᴿ-from-absorptiveᴸ = absorptive (Eq.trans comm absorb)

{--- Equivalences ---}

module _ {A : Set} {_⊙_ : A → A → A} {{_ : Eq A}} where

  identityᴸ-flip : {{_ : Identity handᴿ _⊙_}} → Identity handᴸ (flip _⊙_)
  identityᴸ-flip = identity ident

  identityᴿ-flip : {{_ : Identity handᴸ _⊙_}} → Identity handᴿ (flip _⊙_)
  identityᴿ-flip = identity ident

  identity₂-flip : {{_ : Identity₂ _⊙_}} → Identity₂ (flip _⊙_)
  identity₂-flip =
    identity₂ {{identityᴸ = identityᴸ-flip}} {{identityᴿ = identityᴿ-flip}}
