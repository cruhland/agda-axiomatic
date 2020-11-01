module net.cruhland.axioms.AbstractAlgebra where

open import net.cruhland.axioms.Eq using (_≃_; Eq; module ≃-Reasoning)
open ≃-Reasoning

record Substitutive₁ {A : Set} {{eq : Eq A}} (f : A → A) : Set₁ where
  field
    subst : ∀ {a₁ a₂} → a₁ ≃ a₂ → f a₁ ≃ f a₂

open Substitutive₁ {{...}} public using (subst)

record Substitutiveᴸ {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) : Set₁ where
  field
    substᴸ : ∀ {a₁ a₂ b} → a₁ ≃ a₂ → a₁ ⊙ b ≃ a₂ ⊙ b

open Substitutiveᴸ {{...}} public using (substᴸ)

record Substitutiveᴿ {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) : Set₁ where
  field
    substᴿ : ∀ {a b₁ b₂} → b₁ ≃ b₂ → a ⊙ b₁ ≃ a ⊙ b₂

open Substitutiveᴿ {{...}} public using (substᴿ)

record Associative {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) : Set₁ where
  field
    assoc : ∀ {a b c} → (a ⊙ b) ⊙ c ≃ a ⊙ (b ⊙ c)

open Associative {{...}} public using (assoc)

record Commutative {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) : Set₁ where
  field
    comm : ∀ {a b} → a ⊙ b ≃ b ⊙ a

open Commutative {{...}} public using (comm)

record Identityᴸ {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) (e : A) : Set₁ where
  field
    identᴸ : ∀ {a} → e ⊙ a ≃ a

open Identityᴸ {{...}} public using (identᴸ)

record Identityᴿ {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) (e : A) : Set₁ where
  field
    identᴿ : ∀ {a} → a ⊙ e ≃ a

open Identityᴿ {{...}} public using (identᴿ)

substitutiveᴿ :
  {A : Set} {_⊙_ : A → A → A}
    {{_ : Eq A}} {{_ : Commutative _⊙_}} {{_ : Substitutiveᴸ _⊙_}} →
      Substitutiveᴿ _⊙_
substitutiveᴿ {A} {_⊙_} = record { substᴿ = substᴿ₀ }
  where
    substᴿ₀ : ∀ {a b₁ b₂} → b₁ ≃ b₂ → a ⊙ b₁ ≃ a ⊙ b₂
    substᴿ₀ {a} {b₁} {b₂} b₁≃b₂ =
      begin
        a ⊙ b₁
      ≃⟨ comm ⟩
        b₁ ⊙ a
      ≃⟨ substᴸ b₁≃b₂ ⟩
        b₂ ⊙ a
      ≃⟨ comm ⟩
        a ⊙ b₂
      ∎

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
