module net.cruhland.axioms.AbstractAlgebra.Swappable where

open import Level using (_⊔_)
open import net.cruhland.axioms.Eq as Eq using
  (_≃_; Eq; sym; Symmetric; symmetric)
open Eq.≃-Reasoning
open import net.cruhland.models.Function using (_⟨→⟩_; flip)

private
  record Swappable
      {α β} {A : Set α} {B : Set β} (_⊙_ : A → A → B) (_~_ : B → B → Set)
        : Set (α ⊔ β) where
    constructor swappable
    field
      swap : ∀ {x y} → (x ⊙ y) ~ (y ⊙ x)

open Swappable {{...}} using (swap)

record Commutative {A : Set} {{_ : Eq A}} (_⊙_ : A → A → A) : Set where
  constructor commutative
  field
    comm : ∀ {a b} → a ⊙ b ≃ b ⊙ a

open Commutative {{...}} public using (comm)

with-comm :
  {A : Set} {_⊙_ : A → A → A}
    {{_ : Eq A}} {{_ : Commutative _⊙_}} →
      ∀ {a b c d} → b ⊙ a ≃ d ⊙ c → a ⊙ b ≃ c ⊙ d
with-comm {A} {_⊙_} {a} {b} {c} {d} b⊙a≃d⊙c =
  begin
    a ⊙ b
  ≃⟨ comm ⟩
    b ⊙ a
  ≃⟨ b⊙a≃d⊙c ⟩
    d ⊙ c
  ≃⟨ comm ⟩
    c ⊙ d
  ∎

{--- Equivalences ---}

swappable-flip :
  {A B : Set} {_⊙_ : A → A → B} {_~_ : B → B → Set}
    {{_ : Swappable _⊙_ _~_}} → Swappable (flip _⊙_) _~_
swappable-flip = swappable swap

module _ {A : Set} {_⊙_ : A → A → A} {{_ : Eq A}} where

  swappable-from-commutative : {{_ : Commutative _⊙_}} → Swappable _⊙_ _≃_
  swappable-from-commutative = swappable comm

  commutative-from-swappable : {{_ : Swappable _⊙_ _≃_}} → Commutative _⊙_
  commutative-from-swappable = commutative swap

module _ {A : Set} {_~_ : A → A → Set} where

  swappable-from-symmetric : {{_ : Symmetric _~_}} → Swappable _~_ _⟨→⟩_
  swappable-from-symmetric = swappable sym

  symmetric-from-swappable : {{_ : Swappable _~_ _⟨→⟩_}} → Symmetric _~_
  symmetric-from-swappable = symmetric swap
