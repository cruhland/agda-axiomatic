module net.cruhland.axioms.AbstractAlgebra.Commutative where

open import net.cruhland.axioms.Eq as Eq using (_≃_; Eq)
open Eq.≃-Reasoning

record Commutative {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) : Set where
  field
    comm : ∀ {a b} → a ⊙ b ≃ b ⊙ a

open Commutative {{...}} public using (comm)

record Commutativeᴸ
    {A : Set} {{eq : Eq A}} (f : A → A) (_⊙_ : A → A → A) : Set where
  field
    commᴸ : ∀ {a b} → f a ⊙ b ≃ f (a ⊙ b)

open Commutativeᴸ {{...}} public using (commᴸ)

record Commutativeᴿ
    {A : Set} {{eq : Eq A}} (f : A → A) (_⊙_ : A → A → A) : Set where
  field
    commᴿ : ∀ {a b} → a ⊙ f b ≃ f (a ⊙ b)

open Commutativeᴿ {{...}} public using (commᴿ)

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

comm-swap :
  {A : Set} {f : A → A} {_⊙_ : A → A → A}
    {{_ : Eq A}} {{_ : Commutativeᴸ f _⊙_}} {{_ : Commutativeᴿ f _⊙_}} →
      ∀ {a b} → f a ⊙ b ≃ a ⊙ f b
comm-swap = Eq.trans commᴸ (Eq.sym commᴿ)
