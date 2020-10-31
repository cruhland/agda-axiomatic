module net.cruhland.axioms.AbstractAlgebra where

open import net.cruhland.axioms.Eq using (_≃_; Eq; module ≃-Reasoning)
open ≃-Reasoning

record Substitutive₁ {A : Set} {{eq : Eq A}} (f : A → A) : Set₁ where
  field
    subst : ∀ {a₁ a₂} → a₁ ≃ a₂ → f a₁ ≃ f a₂

open Substitutive₁ {{...}} public using (subst)

record Substitutive₂ {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) : Set₁ where
  field
    substᴸ : ∀ {a₁ a₂ b} → a₁ ≃ a₂ → a₁ ⊙ b ≃ a₂ ⊙ b
    substᴿ : ∀ {a b₁ b₂} → b₁ ≃ b₂ → a ⊙ b₁ ≃ a ⊙ b₂

open Substitutive₂ {{...}} public using (substᴸ; substᴿ)

record Associative {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) : Set₁ where
  field
    assoc : ∀ {a b c} → (a ⊙ b) ⊙ c ≃ a ⊙ (b ⊙ c)

open Associative {{...}} public using (assoc)

record Commutative {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) : Set₁ where
  field
    comm : ∀ {a b} → a ⊙ b ≃ b ⊙ a

open Commutative {{...}} public using (comm)

[ab][cd]≃a[[bc]d] :
  {A : Set} {_⊙_ : A → A → A}
    {{_ : Eq A}} {{_ : Associative _⊙_}} {{_ : Substitutive₂ _⊙_}} →
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
