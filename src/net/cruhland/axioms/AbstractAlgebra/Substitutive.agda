module net.cruhland.axioms.AbstractAlgebra.Substitutive where

open import net.cruhland.axioms.Eq as Eq using (_≃_; Eq)
open Eq.≃-Reasoning
open import net.cruhland.models.Function using (_∘_)
open import net.cruhland.models.Logic using (⊤)

open import net.cruhland.axioms.AbstractAlgebra.Base using (handᴸ; handᴿ)
open import net.cruhland.axioms.AbstractAlgebra.Commutative using
  (comm; Commutative; with-comm)
open import net.cruhland.axioms.AbstractAlgebra.Compatible using
  (fnOpComm; FnOpCommutative; fnOpCommutative)

record Substitutiveⁱ
    {β} {A : Set} {B : A → Set β} {C : A → Set} (f : (a : A) {{c : C a}} → B a)
      (_~_ : A → A → Set) (_≈_ : ∀ {a₁ a₂} → B a₁ → B a₂ → Set)
        : Set β where
  field
    substⁱ : ∀ {a₁ a₂} {{c₁ : C a₁}} {{c₂ : C a₂}} → a₁ ~ a₂ → f a₁ ≈ f a₂

open Substitutiveⁱ {{...}} public using (substⁱ)

Substitutive₁ :
  ∀ {β} {A : Set} {B : A → Set β} (f : (a : A) → B a)
    (_~_ : A → A → Set) (_≈_ : ∀ {a₁ a₂} → B a₁ → B a₂ → Set) →
      Set β
Substitutive₁ {A = A} {B} f = Substitutiveⁱ f-with-trivial-constraint
  where
    f-with-trivial-constraint : (a : A) {{_ : ⊤}} → B a
    f-with-trivial-constraint a = f a

substitutive₁ :
  ∀ {β} {A : Set} {B : A → Set β} {f : (a : A) → B a}
    {_~_ : A → A → Set} {_≈_ : ∀ {a₁ a₂} → B a₁ → B a₂ → Set} →
      (∀ {a₁ a₂} → a₁ ~ a₂ → f a₁ ≈ f a₂) → Substitutive₁ f _~_ _≈_
substitutive₁ substFn = record { substⁱ = substFn }

subst :
  ∀ {β} {A : Set} {B : A → Set β} {f : (a : A) → B a}
    {_~_ : A → A → Set} {_≈_ : ∀ {a₁ a₂} → B a₁ → B a₂ → Set}
      {{r : Substitutive₁ f _~_ _≈_}} →
        ∀ {a₁ a₂} → a₁ ~ a₂ → f a₁ ≈ f a₂
subst = substⁱ

Substitutiveᴸ : {A B : Set} {{_ : Eq A}} {{_ : Eq B}} → (A → A → B) → Set
Substitutiveᴸ _⊙_ = ∀ {y} → Substitutive₁ (_⊙ y) _≃_ _≃_

Substitutiveᴿ : {A B : Set} {{_ : Eq A}} {{_ : Eq B}} → (A → A → B) → Set
Substitutiveᴿ _⊙_ = ∀ {x} → Substitutive₁ (x ⊙_) _≃_ _≃_

substitutiveᴿ :
  {A : Set} {_⊙_ : A → A → A}
    {{_ : Eq A}} {{_ : Commutative _⊙_}} {{_ : Substitutiveᴸ _⊙_}} →
      Substitutiveᴿ _⊙_
substitutiveᴿ = substitutive₁ (with-comm ∘ subst)

record Substitutive₂
    {A B : Set} {{eqA : Eq A}} {{eqB : Eq B}} (_⊙_ : A → A → B) : Set where
  field
    {{subst₂ᴸ}} : Substitutiveᴸ _⊙_
    {{subst₂ᴿ}} : Substitutiveᴿ _⊙_

substitutive₂ :
  {A : Set} {_⊙_ : A → A → A}
    {{_ : Eq A}} {{_ : Substitutiveᴸ _⊙_}} {{_ : Substitutiveᴿ _⊙_}} →
      Substitutive₂ _⊙_
substitutive₂ = record {}

[a≃b][c≃d] :
  {A B : Set} {_⊙_ : A → A → B}
    {{_ : Eq A}} {{_ : Eq B}} {{_ : Substitutive₂ _⊙_}} →
      ∀ {a b c d} → a ≃ b → c ≃ d → a ⊙ c ≃ b ⊙ d
[a≃b][c≃d] {A} {B} {_⊙_} {a} {b} {c} {d} a≃b c≃d =
  begin
    a ⊙ c
  ≃⟨ subst a≃b ⟩
    b ⊙ c
  ≃⟨ subst c≃d ⟩
    b ⊙ d
  ∎

fnOpCommutativeᴿ-from-fnOpCommutativeᴸ :
  {A : Set} {f : A → A} {_⊙_ : A → A → A}
    {{_ : Eq A}} {{_ : Substitutive₁ f _≃_ _≃_}}
    {{_ : Commutative _⊙_}} {{_ : FnOpCommutative handᴸ f _⊙_}} →
      FnOpCommutative handᴿ f _⊙_
fnOpCommutativeᴿ-from-fnOpCommutativeᴸ {A} {f} {_⊙_} = fnOpCommutative commᴿ₀
  where
    commᴿ₀ : ∀ {a b} → f (a ⊙ b) ≃ a ⊙ f b
    commᴿ₀ {a} {b} =
      begin
        f (a ⊙ b)
      ≃⟨ subst comm ⟩
        f (b ⊙ a)
      ≃⟨ fnOpComm ⟩
        f b ⊙ a
      ≃⟨ comm ⟩
        a ⊙ f b
      ∎
