module net.cruhland.axioms.AbstractAlgebra.Reductive where

open import net.cruhland.axioms.Eq as Eq using (_≃_; Eq)

open import net.cruhland.axioms.AbstractAlgebra.Commutative

Keepᴸ : {A : Set} {{_ : Eq A}} → (A → A → A) → A → A → Set
Keepᴸ _⊙_ k d = k ⊙ d ≃ k

Keepᴿ : {A : Set} {{_ : Eq A}} → (A → A → A) → A → A → Set
Keepᴿ _⊙_ k d = d ⊙ k ≃ k

record Identityᴸ {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) (e : A) : Set where
  field
    identᴸ : ∀ {a} → Keepᴿ _⊙_ a e

open Identityᴸ {{...}} public using (identᴸ)

record Identityᴿ {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) (e : A) : Set where
  field
    identᴿ : ∀ {a} → Keepᴸ _⊙_ a e

open Identityᴿ {{...}} public using (identᴿ)

identityᴿ :
  {A : Set} {_⊙_ : A → A → A} →
    ∀ {e} {{_ : Eq A}} {{_ : Commutative _⊙_}} {{_ : Identityᴸ _⊙_ e}} →
      Identityᴿ _⊙_ e
identityᴿ = record { identᴿ = Eq.trans comm identᴸ }

record Absorptiveᴸ {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) (z : A) : Set where
  field
    absorbᴸ : ∀ {a} → Keepᴸ _⊙_ z a

open Absorptiveᴸ {{...}} public using (absorbᴸ)

record Absorptiveᴿ {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) (z : A) : Set where
  field
    absorbᴿ : ∀ {a} → Keepᴿ _⊙_ z a

open Absorptiveᴿ {{...}} public using (absorbᴿ)

absorptiveᴿ :
  {A : Set} {_⊙_ : A → A → A} →
    ∀ {z} {{_ : Eq A}} {{_ : Commutative _⊙_}} {{_ : Absorptiveᴸ _⊙_ z}} →
      Absorptiveᴿ _⊙_ z
absorptiveᴿ = record { absorbᴿ = Eq.trans comm absorbᴸ }
