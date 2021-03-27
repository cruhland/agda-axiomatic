module net.cruhland.axioms.AbstractAlgebra.Swappable where

open import Level using (_⊔_)
open import net.cruhland.axioms.Eq as Eq using
  (_≃_; Eq; sym; Symmetric; symmetric)
open Eq.≃-Reasoning
open import net.cruhland.models.Function using (_⟨→⟩_; flip)

record Swappable
    {α β χ} {A : Set α} {B : Set β} (_⊙_ : A → A → B) (_~_ : B → B → Set χ)
      : Set (α ⊔ β ⊔ χ) where
  constructor swappable
  field
    swap : ∀ {x y} → (x ⊙ y) ~ (y ⊙ x)

open Swappable {{...}} public using (swap)

record Commutative
    {β} {A : Set} {B : Set β} {{_ : Eq B}} (_⊙_ : A → A → B) : Set β where
  constructor commutative
  field
    comm : ∀ {a b} → a ⊙ b ≃ b ⊙ a

open Commutative {{...}} public using (comm)

{--- Equivalences ---}

swappable-flip :
  {A B : Set} {_⊙_ : A → A → B} {_~_ : B → B → Set}
    {{_ : Swappable _⊙_ _~_}} → Swappable (flip _⊙_) _~_
swappable-flip = swappable swap

module _ {α β} {A : Set α} {_~_ : A → A → Set β} where

  swappable-from-symmetric : {{_ : Symmetric _~_}} → Swappable _~_ _⟨→⟩_
  swappable-from-symmetric = swappable sym

  symmetric-from-swappable : {{_ : Swappable _~_ _⟨→⟩_}} → Symmetric _~_
  symmetric-from-swappable = symmetric swap

with-swap :
  ∀ {α β χ} {A : Set α} {B : Set β} {_⊙_ : A → A → B} {_~_ : B → B → Set χ}
    {{_ : Eq.Transitive _~_}} {{_ : Swappable _⊙_ _~_}} →
      ∀ {a b c d} → (b ⊙ a) ~ (d ⊙ c) → (a ⊙ b) ~ (c ⊙ d)
with-swap b⊙a~d⊙c = Eq.trans swap (Eq.trans b⊙a~d⊙c swap)
