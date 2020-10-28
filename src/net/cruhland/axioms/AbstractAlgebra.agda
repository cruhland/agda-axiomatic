module net.cruhland.axioms.AbstractAlgebra where

open import net.cruhland.axioms.Eq using (_≃_; Eq; module ≃-Reasoning)
open ≃-Reasoning

record Substitutive (A : Set) {{eq : Eq A}} (_⊙_ : A → A → A) : Set₁ where
  field
    substᴸ : ∀ {a₁ a₂ b} → a₁ ≃ a₂ → a₁ ⊙ b ≃ a₂ ⊙ b
    substᴿ : ∀ {a b₁ b₂} → b₁ ≃ b₂ → a ⊙ b₁ ≃ a ⊙ b₂

open Substitutive {{...}} public using (substᴸ; substᴿ)

record Associative (A : Set) {{eq : Eq A}} (_⊙_ : A → A → A) : Set₁ where
  field
    assoc : ∀ {a b c} → (a ⊙ b) ⊙ c ≃ a ⊙ (b ⊙ c)

open Associative {{...}} public using (assoc)

[ab][cd]≃a[[bc]d] :
  {A : Set} {_⊙_ : A → A → A}
    {{_ : Eq A}} {{_ : Associative A _⊙_}} {{_ : Substitutive A _⊙_}} →
      ∀ {a b c d} → (a ⊙ b) ⊙ (c ⊙ d) ≃ a ⊙ ((b ⊙ c) ⊙ d)
[ab][cd]≃a[[bc]d] {A} {_⊙_} {a} {b} {c} {d} =
  begin
    (a ⊙ b) ⊙ (c ⊙ d)
  ≃⟨ assoc ⟩
    a ⊙ (b ⊙ (c ⊙ d))
  ≃˘⟨ substᴿ assoc ⟩
    a ⊙ ((b ⊙ c) ⊙ d)
  ∎
