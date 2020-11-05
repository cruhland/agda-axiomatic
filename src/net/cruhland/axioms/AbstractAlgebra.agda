module net.cruhland.axioms.AbstractAlgebra where

open import Function using (_∘_)
open import net.cruhland.axioms.Eq using
  (_≃_; _≄_; Eq; trans; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.models.Logic using (_∨_; ∨-rec)

record Substitutive₁ {A : Set} {{eq : Eq A}} (f : A → A) : Set where
  field
    subst : ∀ {a₁ a₂} → a₁ ≃ a₂ → f a₁ ≃ f a₂

open Substitutive₁ {{...}} public using (subst)

record Substitutiveᴸ {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) : Set where
  field
    substᴸ : ∀ {a₁ a₂ b} → a₁ ≃ a₂ → a₁ ⊙ b ≃ a₂ ⊙ b

open Substitutiveᴸ {{...}} public using (substᴸ)

record Substitutiveᴿ {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) : Set where
  field
    substᴿ : ∀ {a b₁ b₂} → b₁ ≃ b₂ → a ⊙ b₁ ≃ a ⊙ b₂

open Substitutiveᴿ {{...}} public using (substᴿ)

record Substitutive₂ {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) : Set where
  field
    {{subst₂ᴸ}} : Substitutiveᴸ _⊙_
    {{subst₂ᴿ}} : Substitutiveᴿ _⊙_

record Associative {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) : Set where
  field
    assoc : ∀ {a b c} → (a ⊙ b) ⊙ c ≃ a ⊙ (b ⊙ c)

open Associative {{...}} public using (assoc)

record Commutative {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) : Set where
  field
    comm : ∀ {a b} → a ⊙ b ≃ b ⊙ a

open Commutative {{...}} public using (comm)

record Identityᴸ {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) (e : A) : Set where
  field
    identᴸ : ∀ {a} → e ⊙ a ≃ a

open Identityᴸ {{...}} public using (identᴸ)

record Identityᴿ {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) (e : A) : Set where
  field
    identᴿ : ∀ {a} → a ⊙ e ≃ a

open Identityᴿ {{...}} public using (identᴿ)

record Cancellativeᴸ {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) : Set₁ where
  field
    Constraint : A → Set
    cancelᴸ : ∀ {a b₁ b₂} {{c : Constraint a}} → a ⊙ b₁ ≃ a ⊙ b₂ → b₁ ≃ b₂

open Cancellativeᴸ {{...}} public using (cancelᴸ)

record Cancellativeᴿ {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) : Set₁ where
  field
    Constraint : A → Set
    cancelᴿ : ∀ {a₁ a₂ b} {{c : Constraint b}} → a₁ ⊙ b ≃ a₂ ⊙ b → a₁ ≃ a₂

open Cancellativeᴿ {{...}} public using (cancelᴿ)

record Distributiveᴸ {A : Set} {{eq : Eq A}} (_⊙_ _⊕_ : A → A → A) : Set where
  field
    distribᴸ : ∀ {a b c} → a ⊙ (b ⊕ c) ≃ (a ⊙ b) ⊕ (a ⊙ c)

open Distributiveᴸ {{...}} public using (distribᴸ)

record Distributiveᴿ {A : Set} {{eq : Eq A}} (_⊙_ _⊕_ : A → A → A) : Set where
  field
    distribᴿ : ∀ {a b c} → (b ⊕ c) ⊙ a ≃ (b ⊙ a) ⊕ (c ⊙ a)

open Distributiveᴿ {{...}} public using (distribᴿ)

record ZeroProduct {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) (z : A) : Set where
  field
    zero-prod : ∀ {a b} → a ⊙ b ≃ z → a ≃ z ∨ b ≃ z

open ZeroProduct {{...}} public using (zero-prod)

record Absorptiveᴸ {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) (z : A) : Set where
  field
    absorbᴸ : ∀ {a} → z ⊙ a ≃ z

open Absorptiveᴸ {{...}} public using (absorbᴸ)

record Absorptiveᴿ {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) (z : A) : Set where
  field
    absorbᴿ : ∀ {a} → a ⊙ z ≃ z

open Absorptiveᴿ {{...}} public using (absorbᴿ)

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

substitutiveᴿ :
  {A : Set} {_⊙_ : A → A → A}
    {{_ : Eq A}} {{_ : Commutative _⊙_}} {{_ : Substitutiveᴸ _⊙_}} →
      Substitutiveᴿ _⊙_
substitutiveᴿ = record { substᴿ = with-comm ∘ substᴸ }

substitutive₂ :
  {A : Set} {_⊙_ : A → A → A}
    {{_ : Eq A}} {{_ : Substitutiveᴸ _⊙_}} {{_ : Substitutiveᴿ _⊙_}} →
      Substitutive₂ _⊙_
substitutive₂ = record {}

cancellativeᴿ :
  {A : Set} {_⊙_ : A → A → A}
    {{eq : Eq A}} {{⊙-comm : Commutative _⊙_}}
    {{⊙-cancelᴸ : Cancellativeᴸ _⊙_}} →
      Cancellativeᴿ _⊙_
cancellativeᴿ
  {{⊙-cancelᴸ = record { Constraint = Constraint ; cancelᴸ = cancelᴸ₀}}} =
    record { Constraint = Constraint ; cancelᴿ = cancelᴸ₀ ∘ with-comm }

distributiveᴿ :
  {A : Set} {_⊙_ _⊕_ : A → A → A}
    {{_ : Eq A}} {{_ : Commutative _⊙_}} {{_ : Distributiveᴸ _⊙_ _⊕_}}
    {{_ : Substitutive₂ _⊕_}} →
      Distributiveᴿ _⊙_ _⊕_
distributiveᴿ {A} {_⊙_} {_⊕_} = record { distribᴿ = distribᴿ₀ }
  where
    distribᴿ₀ : ∀ {a b c} → (a ⊕ b) ⊙ c ≃ (a ⊙ c) ⊕ (b ⊙ c)
    distribᴿ₀ {a} {b} {c} =
      begin
        (a ⊕ b) ⊙ c
      ≃⟨ comm ⟩
        c ⊙ (a ⊕ b)
      ≃⟨ distribᴸ ⟩
        (c ⊙ a) ⊕ (c ⊙ b)
      ≃⟨ substᴸ comm ⟩
        (a ⊙ c) ⊕ (c ⊙ b)
      ≃⟨ substᴿ comm ⟩
        (a ⊙ c) ⊕ (b ⊙ c)
      ∎

absorptiveᴿ :
  {A : Set} {_⊙_ : A → A → A} →
    ∀ {z} {{_ : Eq A}} {{_ : Commutative _⊙_}} {{_ : Absorptiveᴸ _⊙_ z}} →
      Absorptiveᴿ _⊙_ z
absorptiveᴿ = record { absorbᴿ = trans comm absorbᴸ }

[ab][cd]≃a[[bc]d] :
  {A : Set} {_⊙_ : A → A → A}
    {{_ : Eq A}} {{_ : Associative _⊙_}} {{_ : Substitutiveᴿ _⊙_}} →
      ∀ {a b c d} → (a ⊙ b) ⊙ (c ⊙ d) ≃ a ⊙ ((b ⊙ c) ⊙ d)
[ab][cd]≃a[[bc]d] {A} {_⊙_} {a} {b} {c} {d} =
  begin
    (a ⊙ b) ⊙ (c ⊙ d)
  ≃⟨ assoc ⟩
    a ⊙ (b ⊙ (c ⊙ d))
  ≃˘⟨ substᴿ assoc ⟩
    a ⊙ ((b ⊙ c) ⊙ d)
  ∎

swap-middle :
  {A : Set} {_⊙_ : A → A → A}
    {{_ : Eq A}} {{_ : Commutative _⊙_}} {{_ : Substitutive₂ _⊙_}} →
      ∀ {a b c d} → a ⊙ ((b ⊙ c) ⊙ d) ≃ a ⊙ ((c ⊙ b) ⊙ d)
swap-middle = substᴿ (substᴸ comm)

regroup :
  {A : Set} {_⊙_ : A → A → A}
    {{_ : Eq A}} {{_ : Associative _⊙_}}
    {{_ : Commutative _⊙_}} {{_ : Substitutiveᴿ _⊙_}} →
      ∀ a b c d → (a ⊙ b) ⊙ (c ⊙ d) ≃ a ⊙ ((b ⊙ d) ⊙ c)
regroup {A} {_⊙_} a b c d =
  begin
    (a ⊙ b) ⊙ (c ⊙ d)
  ≃⟨ substᴿ comm ⟩
    (a ⊙ b) ⊙ (d ⊙ c)
  ≃⟨ [ab][cd]≃a[[bc]d] ⟩
    a ⊙ ((b ⊙ d) ⊙ c)
  ∎

perm-adcb :
  {A : Set} {_⊙_ : A → A → A}
    {{_ : Eq A}} {{_ : Associative _⊙_}} {{_ : Commutative _⊙_}}
    {{_ : Substitutive₂ _⊙_}} →
      ∀ {a b c d} → (a ⊙ d) ⊙ (c ⊙ b) ≃ (a ⊙ b) ⊙ (c ⊙ d)
perm-adcb {A} {_⊙_} {a} {b} {c} {d} =
  begin
    (a ⊙ d) ⊙ (c ⊙ b)
  ≃⟨ regroup a d c b ⟩
    a ⊙ ((d ⊙ b) ⊙ c)
  ≃⟨ swap-middle ⟩
    a ⊙ ((b ⊙ d) ⊙ c)
  ≃˘⟨ regroup a b c d ⟩
    (a ⊙ b) ⊙ (c ⊙ d)
  ∎

[a≃b][c≃d] :
  {A : Set} {_⊙_ : A → A → A} {{_ : Eq A}} {{_ : Substitutive₂ _⊙_}} →
    ∀ {a b c d} → a ≃ b → c ≃ d → a ⊙ c ≃ b ⊙ d
[a≃b][c≃d] {A} {_⊙_} {a} {b} {c} {d} a≃b c≃d =
  begin
    a ⊙ c
  ≃⟨ substᴸ a≃b ⟩
    b ⊙ c
  ≃⟨ substᴿ c≃d ⟩
    b ⊙ d
  ∎

transpose :
  {A : Set} {_⊙_ : A → A → A}
    {{_ : Eq A}} {{_ : Associative _⊙_}} {{_ : Commutative _⊙_}}
    {{_ : Substitutive₂ _⊙_}} →
      ∀ {w x y z} → (w ⊙ x) ⊙ (y ⊙ z) ≃ (w ⊙ y) ⊙ (x ⊙ z)
transpose {A} {_⊙_} {w} {x} {y} {z} =
  begin
    (w ⊙ x) ⊙ (y ⊙ z)
  ≃⟨ [ab][cd]≃a[[bc]d] ⟩
    w ⊙ ((x ⊙ y) ⊙ z)
  ≃⟨ swap-middle ⟩
    w ⊙ ((y ⊙ x) ⊙ z)
  ≃˘⟨ [ab][cd]≃a[[bc]d] ⟩
    (w ⊙ y) ⊙ (x ⊙ z)
  ∎

distrib-twoᴸ :
  {A : Set} {_⊙_ _⊕_ : A → A → A}
    {{_ : Eq A}} {{_ : Distributiveᴸ _⊙_ _⊕_}} {{_ : Substitutive₂ _⊕_}} →
      ∀ {a b c d e f} →
        (a ⊙ (b ⊕ c)) ⊕ (d ⊙ (e ⊕ f)) ≃
          ((a ⊙ b) ⊕ (a ⊙ c)) ⊕ ((d ⊙ e) ⊕ (d ⊙ f))
distrib-twoᴸ {A} {_⊙_} {_⊕_} {a} {b} {c} {d} {e} {f} =
  begin
    (a ⊙ (b ⊕ c)) ⊕ (d ⊙ (e ⊕ f))
  ≃⟨ substᴸ distribᴸ ⟩
    ((a ⊙ b) ⊕ (a ⊙ c)) ⊕ (d ⊙ (e ⊕ f))
  ≃⟨ substᴿ distribᴸ ⟩
    ((a ⊙ b) ⊕ (a ⊙ c)) ⊕ ((d ⊙ e) ⊕ (d ⊙ f))
  ∎

distrib-twoᴿ :
  {A : Set} {_⊙_ _⊕_ : A → A → A}
    {{_ : Eq A}} {{_ : Distributiveᴿ _⊙_ _⊕_}} {{_ : Substitutive₂ _⊕_}} →
      ∀ {a b c d e f} →
        ((a ⊕ b) ⊙ c) ⊕ ((d ⊕ e) ⊙ f) ≃
          ((a ⊙ c) ⊕ (b ⊙ c)) ⊕ ((d ⊙ f) ⊕ (e ⊙ f))
distrib-twoᴿ {A} {_⊙_} {_⊕_} {a} {b} {c} {d} {e} {f} =
  begin
    ((a ⊕ b) ⊙ c) ⊕ ((d ⊕ e) ⊙ f)
  ≃⟨ substᴸ distribᴿ ⟩
    ((a ⊙ c) ⊕ (b ⊙ c)) ⊕ ((d ⊕ e) ⊙ f)
  ≃⟨ substᴿ distribᴿ ⟩
    ((a ⊙ c) ⊕ (b ⊙ c)) ⊕ ((d ⊙ f) ⊕ (e ⊙ f))
  ∎

nonzero-prod :
  {A : Set} {_⊙_ : A → A → A} →
    ∀ {a b z} {{_ : Eq A}} {{_ : ZeroProduct _⊙_ z}} →
      a ≄ z → b ≄ z → a ⊙ b ≄ z
nonzero-prod a≄z b≄z = ∨-rec a≄z b≄z ∘ zero-prod
