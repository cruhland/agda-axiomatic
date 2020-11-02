module net.cruhland.axioms.AbstractAlgebra where

open import Function using (_∘_)
open import net.cruhland.axioms.Eq using (_≃_; Eq; module ≃-Reasoning)
open ≃-Reasoning

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

record Cancellativeᴸ {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) : Set where
  field
    cancelᴸ : ∀ {a b₁ b₂} → a ⊙ b₁ ≃ a ⊙ b₂ → b₁ ≃ b₂

open Cancellativeᴸ {{...}} public using (cancelᴸ)

record Cancellativeᴿ {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) : Set where
  field
    cancelᴿ : ∀ {a₁ a₂ b} → a₁ ⊙ b ≃ a₂ ⊙ b → a₁ ≃ a₂

open Cancellativeᴿ {{...}} public using (cancelᴿ)

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

cancellativeᴿ :
  {A : Set} {_⊙_ : A → A → A}
    {{_ : Eq A}} {{_ : Commutative _⊙_}} {{_ : Cancellativeᴸ _⊙_}} →
      Cancellativeᴿ _⊙_
cancellativeᴿ = record { cancelᴿ = cancelᴸ ∘ with-comm }

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
    {{_ : Eq A}} {{_ : Commutative _⊙_}}
    {{_ : Substitutiveᴸ _⊙_}} {{_ : Substitutiveᴿ _⊙_}} →
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
    {{_ : Substitutiveᴸ _⊙_}} {{_ : Substitutiveᴿ _⊙_}} →
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
  {A : Set} {_⊙_ : A → A → A}
    {{_ : Eq A}} {{_ : Substitutiveᴸ _⊙_}} {{_ : Substitutiveᴿ _⊙_}} →
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
    {{_ : Substitutiveᴸ _⊙_}} {{_ : Substitutiveᴿ _⊙_}} →
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
