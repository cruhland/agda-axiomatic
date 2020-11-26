module net.cruhland.axioms.AbstractAlgebra where

open import Function using (_∘_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_; Eq)
open Eq.≃-Reasoning
open import net.cruhland.models.Logic using (_∨_; ∨-rec; ¬_)

record Substitutive₁
    {β} {A : Set} {B : A → Set β} (f : (a : A) → B a)
      (_~_ : A → A → Set) (_≈_ : ∀ {a₁ a₂} → B a₁ → B a₂ → Set)
        : Set β where
  field
    subst : ∀ {a₁ a₂} → a₁ ~ a₂ → f a₁ ≈ f a₂

open Substitutive₁ {{...}} public using (subst)

record Substitutiveⁱ₁
    {A B : Set} {C : A → Set} {{eqA : Eq A}} {{eqB : Eq B}}
      (f : (a : A) {{c : C a}} → B) : Set where
  field
    substⁱ : ∀ {a₁ a₂} {{c₁ : C a₁}} {{c₂ : C a₂}} → a₁ ≃ a₂ → f a₁ ≃ f a₂

open Substitutiveⁱ₁ {{...}} public using (substⁱ)

record Substitutiveᴸ
    {A B : Set} (_~_ : A → A → Set) (_≈_ : B → B → Set) (_⊙_ : A → A → B)
      : Set where
  field
    substᴸ : ∀ {a b₁ b₂} → b₁ ~ b₂ → (b₁ ⊙ a) ≈ (b₂ ⊙ a)

open Substitutiveᴸ {{...}} public using (substᴸ)

record Substitutiveᴿ
    {A B : Set} {{eqA : Eq A}} {{eqB : Eq B}} (_⊙_ : A → A → B) : Set where
  field
    substᴿ : ∀ {a b₁ b₂} → b₁ ≃ b₂ → a ⊙ b₁ ≃ a ⊙ b₂

open Substitutiveᴿ {{...}} public using (substᴿ)

record Substitutive₂
    {A B : Set} {{eqA : Eq A}} {{eqB : Eq B}} (_⊙_ : A → A → B) : Set where
  field
    {{subst₂ᴸ}} : Substitutiveᴸ _≃_ _≃_ _⊙_
    {{subst₂ᴿ}} : Substitutiveᴿ _⊙_

record Associative {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) : Set where
  field
    assoc : ∀ {a b c} → (a ⊙ b) ⊙ c ≃ a ⊙ (b ⊙ c)

open Associative {{...}} public using (assoc)

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

record Identityᴸ {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) (e : A) : Set where
  field
    identᴸ : ∀ {a} → e ⊙ a ≃ a

open Identityᴸ {{...}} public using (identᴸ)

record Identityᴿ {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) (e : A) : Set where
  field
    identᴿ : ∀ {a} → a ⊙ e ≃ a

open Identityᴿ {{...}} public using (identᴿ)

record Injective
    {A B : Set} (_~_ : A → A → Set) (_≈_ : B → B → Set) (f : A → B) : Set where
  field
    inject : ∀ {a₁ a₂} → f a₁ ≈ f a₂ → a₁ ~ a₂

open Injective {{...}} public using (inject)

record Cancellativeᴸ {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) : Set₁ where
  field
    Constraint : A → Set
    cancelᴸ : ∀ {a b₁ b₂} {{c : Constraint a}} → a ⊙ b₁ ≃ a ⊙ b₂ → b₁ ≃ b₂

open Cancellativeᴸ {{...}} public using (cancelᴸ)

record Cancellativeᴿ
    {A : Set} (_~_ : A → A → Set) (_⊙_ : A → A → A) : Set₁ where
  field
    Constraint : A → Set
    cancelᴿ : ∀ {a₁ a₂ b} {{c : Constraint b}} → (a₁ ⊙ b) ~ (a₂ ⊙ b) → a₁ ~ a₂

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

record Compatible₁
    {A B : Set} {{_ : Eq B}} (f : A → B) (g : A → A) (h : B → B) : Set where
  field
    compat₁ : ∀ {a} → f (g a) ≃ h (f a)

open Compatible₁ {{...}} public using (compat₁)

record Compatible₂
    {A B : Set} {{_ : Eq B}}
      (f : A → B) (_⊙_ : A → A → A) (_⊕_ : B → B → B) : Set where
  field
    compat₂ : ∀ {a b} → f (a ⊙ b) ≃ f a ⊕ f b

open Compatible₂ {{...}} public using (compat₂)

record Inverseᴸ
    {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) (inv : A → A) (e : A) : Set where
  field
    invᴸ : ∀ {a} → inv a ⊙ a ≃ e

open Inverseᴸ {{...}} public using (invᴸ)

record Inverseᴿ
    {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) (inv : A → A) (e : A) : Set where
  field
    invᴿ : ∀ {a} → a ⊙ inv a ≃ e

open Inverseᴿ {{...}} public using (invᴿ)

record Inverseⁱᴸ
    {A : Set} {C : A → Set} {{eq : Eq A}}
      (_⊙_ : A → A → A) (inv : (a : A) {{c : C a}} → A) (e : A) : Set where
  field
    invⁱᴸ : ∀ {a} {{c : C a}} → inv a ⊙ a ≃ e

open Inverseⁱᴸ {{...}} public using (invⁱᴸ)

record Inverseⁱᴿ
    {A : Set} {C : A → Set} {{eq : Eq A}}
      (_⊙_ : A → A → A) (inv : (a : A) {{c : C a}} → A) (e : A) : Set where
  field
    invⁱᴿ : ∀ {a} {{c : C a}} → a ⊙ inv a ≃ e

open Inverseⁱᴿ {{...}} public using (invⁱᴿ)

record Antisymmetric {A : Set} {{eq : Eq A}} (_~_ : A → A → Set) : Set where
  field
    antisym : ∀ {a b} → a ~ b → b ~ a → a ≃ b

open Antisymmetric {{...}} public using (antisym)

data OneOfThree (A B C : Set) : Set where
  1st : A → OneOfThree A B C
  2nd : B → OneOfThree A B C
  3rd : C → OneOfThree A B C

data TwoOfThree (A B C : Set) : Set where
  1∧2 : A → B → TwoOfThree A B C
  1∧3 : A → C → TwoOfThree A B C
  2∧3 : B → C → TwoOfThree A B C

record ExactlyOneOfThree (A B C : Set) : Set where
  field
    at-least-one : OneOfThree A B C
    at-most-one : ¬ TwoOfThree A B C

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
    {{_ : Eq A}} {{_ : Commutative _⊙_}} {{_ : Substitutiveᴸ _≃_ _≃_ _⊙_}} →
      Substitutiveᴿ _⊙_
substitutiveᴿ = record { substᴿ = with-comm ∘ substᴸ }

substitutive₂ :
  {A : Set} {_⊙_ : A → A → A}
    {{_ : Eq A}} {{_ : Substitutiveᴸ _≃_ _≃_ _⊙_}} {{_ : Substitutiveᴿ _⊙_}} →
      Substitutive₂ _⊙_
substitutive₂ = record {}

commutativeᴿ :
  {A : Set} {f : A → A} {_⊙_ : A → A → A}
    {{_ : Eq A}} {{_ : Substitutive₁ f _≃_ _≃_}}
    {{_ : Commutative _⊙_}} {{_ : Commutativeᴸ f _⊙_}} →
      Commutativeᴿ f _⊙_
commutativeᴿ {A} {f} {_⊙_} = record { commᴿ = commᴿ₀ }
  where
    commᴿ₀ : ∀ {a b} → a ⊙ f b ≃ f (a ⊙ b)
    commᴿ₀ {a} {b} =
      begin
        a ⊙ f b
      ≃⟨ comm ⟩
        f b ⊙ a
      ≃⟨ commᴸ ⟩
        f (b ⊙ a)
      ≃⟨ subst comm ⟩
        f (a ⊙ b)
      ∎

identityᴿ :
  {A : Set} {_⊙_ : A → A → A} →
    ∀ {e} {{_ : Eq A}} {{_ : Commutative _⊙_}} {{_ : Identityᴸ _⊙_ e}} →
      Identityᴿ _⊙_ e
identityᴿ = record { identᴿ = Eq.trans comm identᴸ }

cancellativeᴿ :
  {A : Set} {_⊙_ : A → A → A}
    {{eq : Eq A}} {{⊙-comm : Commutative _⊙_}}
    {{⊙-cancelᴸ : Cancellativeᴸ _⊙_}} →
      Cancellativeᴿ _≃_ _⊙_
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
absorptiveᴿ = record { absorbᴿ = Eq.trans comm absorbᴸ }

inverseᴿ :
  {A : Set} {_⊙_ : A → A → A} {inv : A → A} →
    ∀ {e} {{_ : Eq A}} {{_ : Commutative _⊙_}} {{_ : Inverseᴸ _⊙_ inv e}} →
      Inverseᴿ _⊙_ inv e
inverseᴿ = record { invᴿ = Eq.trans comm invᴸ }

inverseⁱᴿ :
  {A : Set} {C : A → Set} {_⊙_ : A → A → A} {inv : (a : A) {{c : C a}} → A} →
    ∀ {e} {{_ : Eq A}} {{_ : Commutative _⊙_}} {{_ : Inverseⁱᴸ _⊙_ inv e}} →
      Inverseⁱᴿ _⊙_ inv e
inverseⁱᴿ = record { invⁱᴿ = Eq.trans comm invⁱᴸ }

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

perm-adcb :
  {A : Set} {_⊙_ : A → A → A}
    {{_ : Eq A}} {{_ : Associative _⊙_}} {{_ : Commutative _⊙_}}
    {{_ : Substitutive₂ _⊙_}} →
      ∀ {a b c d} → (a ⊙ d) ⊙ (c ⊙ b) ≃ (a ⊙ b) ⊙ (c ⊙ d)
perm-adcb {A} {_⊙_} {a} {b} {c} {d} =
  begin
    (a ⊙ d) ⊙ (c ⊙ b)
  ≃⟨ substᴿ comm ⟩
    (a ⊙ d) ⊙ (b ⊙ c)
  ≃⟨ transpose ⟩
    (a ⊙ b) ⊙ (d ⊙ c)
  ≃⟨ substᴿ comm ⟩
    (a ⊙ b) ⊙ (c ⊙ d)
  ∎

[a≃b][c≃d] :
  {A B : Set} {_⊙_ : A → A → B}
    {{_ : Eq A}} {{_ : Eq B}} {{_ : Substitutive₂ _⊙_}} →
      ∀ {a b c d} → a ≃ b → c ≃ d → a ⊙ c ≃ b ⊙ d
[a≃b][c≃d] {A} {B} {_⊙_} {a} {b} {c} {d} a≃b c≃d =
  begin
    a ⊙ c
  ≃⟨ substᴸ a≃b ⟩
    b ⊙ c
  ≃⟨ substᴿ c≃d ⟩
    b ⊙ d
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

≄-subst :
  {A B : Set} {f : A → B}
    {{_ : Eq A}} {{_ : Eq B}} {{_ : Injective _≃_ _≃_ f}} →
      ∀ {a₁ a₂} → a₁ ≄ a₂ → f a₁ ≄ f a₂
≄-subst a₁≄a₂ fa₁≃fa₂ = a₁≄a₂ (inject fa₁≃fa₂)

substᴿ-with-assoc :
  {A : Set} {_⊙_ : A → A → A}
    {{_ : Eq A}} {{_ : Associative _⊙_}} {{_ : Substitutiveᴿ _⊙_}} →
      ∀ {a b c d e} → b ⊙ c ≃ d ⊙ e → (a ⊙ b) ⊙ c ≃ (a ⊙ d) ⊙ e
substᴿ-with-assoc {A} {_⊙_} {a} {b} {c} {d} {e} bc≃de =
  begin
    (a ⊙ b) ⊙ c
  ≃⟨ assoc ⟩
    a ⊙ (b ⊙ c)
  ≃⟨ substᴿ bc≃de ⟩
    a ⊙ (d ⊙ e)
  ≃˘⟨ assoc ⟩
    (a ⊙ d) ⊙ e
  ∎

a[bc]-chain :
  {A : Set} {_⊙_ : A → A → A}
    {{_ : Eq A}} {{_ : Associative _⊙_}} {{_ : Substitutiveᴸ _≃_ _≃_ _⊙_}} →
      ∀ {a b c d e} → a ⊙ b ≃ d → d ⊙ c ≃ e → a ⊙ (b ⊙ c) ≃ e
a[bc]-chain {A} {_⊙_} {a} {b} {c} {d} {e} ab≃d dc≃e =
  begin
    a ⊙ (b ⊙ c)
  ≃˘⟨ assoc ⟩
    (a ⊙ b) ⊙ c
  ≃⟨ substᴸ ab≃d ⟩
    d ⊙ c
  ≃⟨ dc≃e ⟩
    e
  ∎

comm-swap :
  {A : Set} {f : A → A} {_⊙_ : A → A → A}
    {{_ : Eq A}} {{_ : Commutativeᴸ f _⊙_}} {{_ : Commutativeᴿ f _⊙_}} →
      ∀ {a b} → f a ⊙ b ≃ a ⊙ f b
comm-swap = Eq.trans commᴸ (Eq.sym commᴿ)

eq→idᴿ :
  {A : Set} {_⊙_ : A → A → A} {a b d e : A}
    {{_ : Eq A}} {{_ : Identityᴿ _⊙_ e}}
    {{cancel : Cancellativeᴸ _⊙_}} {{_ : Cancellativeᴸ.Constraint cancel a}} →
      a ⊙ d ≃ b → a ≃ b → d ≃ e
eq→idᴿ {A} {_⊙_} {a} {b} {d} {e} ad≃b a≃b = cancelᴸ ad≃ae
  where
    ad≃ae =
      begin
        a ⊙ d
      ≃⟨ ad≃b ⟩
        b
      ≃˘⟨ a≃b ⟩
        a
      ≃˘⟨ identᴿ ⟩
        a ⊙ e
      ∎

idᴿ→eq :
  {A : Set} {_⊙_ : A → A → A} {a b d e : A}
    {{_ : Eq A}} {{_ : Identityᴿ _⊙_ e}} {{_ : Substitutiveᴿ _⊙_}} →
      a ⊙ d ≃ b → d ≃ e → a ≃ b
idᴿ→eq {A} {_⊙_} {a} {b} {d} {e} ad≃b d≃e =
  begin
    a
  ≃˘⟨ identᴿ ⟩
    a ⊙ e
  ≃˘⟨ substᴿ d≃e ⟩
    a ⊙ d
  ≃⟨ ad≃b ⟩
    b
  ∎
