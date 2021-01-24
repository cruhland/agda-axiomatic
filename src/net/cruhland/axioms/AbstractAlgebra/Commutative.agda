module net.cruhland.axioms.AbstractAlgebra.Commutative where

open import net.cruhland.axioms.Eq as Eq using (_≃_; Eq)
open Eq.≃-Reasoning

record Commutative {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) : Set where
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
