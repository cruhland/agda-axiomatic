import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast as Cast using (_As_; _as_)
open import net.cruhland.axioms.DecEq using (_≃?_; DecEq; DecEq-intro)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_; Eq)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators using (_*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Function using (_⟨→⟩_; const)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (⊤; Dec; dec-map)

module net.cruhland.models.Rationals.IntPair.BaseImpl
  (PA : PeanoArithmetic) (Z : Integers PA) where

private open module ℕ = PeanoArithmetic PA using (ℕ)
private open module ℤ = Integers Z using (ℤ)

infix 8 _//_
record ℚ : Set where
  constructor _//_
  field
    numerator denominator : ℤ

    -- Having this as an instance field is convenient when
    -- implementing functions on ℚ, because it's automatically
    -- available as an instance in scope. It does mean there's less
    -- flexibility in the constructor, which can affect pattern
    -- matching.
    {{denominator≄0}} : denominator ≄ 0

open ℚ public using (numerator; denominator)

record _≃₀_ (p q : ℚ) : Set where
  constructor ≃₀-intro

  open ℚ p using () renaming (numerator to p↑; denominator to p↓)
  open ℚ q using () renaming (numerator to q↑; denominator to q↓)

  field
    elim : p↑ * q↓ ≃ q↑ * p↓

instance
  ≃₀-reflexive : Eq.Reflexive _≃₀_
  ≃₀-reflexive = Eq.reflexive ≃₀-refl
    where
      ≃₀-refl : ∀ {q} → q ≃₀ q
      ≃₀-refl q@{q↑ // q↓} =
        let q↑q↓≃q↑q↓ = Eq.refl
         in ≃₀-intro q↑q↓≃q↑q↓

  ≃₀-symmetric : Eq.Symmetric _≃₀_
  ≃₀-symmetric = Eq.symmetric ≃₀-sym
    where
      ≃₀-sym : ∀ {p q} → p ≃₀ q → q ≃₀ p
      ≃₀-sym p@{p↑ // p↓} q@{q↑ // q↓} (≃₀-intro p↑q↓≃q↑p↓) =
        let q↑p↓≃p↑q↓ = Eq.sym p↑q↓≃q↑p↓
         in ≃₀-intro q↑p↓≃p↑q↓

  ≃₀-transitive : Eq.Transitive _≃₀_
  ≃₀-transitive = Eq.transitive ≃₀-trans
    where
      ≃₀-trans : ∀ {p q r} → p ≃₀ q → q ≃₀ r → p ≃₀ r
      ≃₀-trans
          p@{p↑ // p↓} q@{q↑ // q↓} r@{r↑ // r↓}
          (≃₀-intro p↑q↓≃q↑p↓) (≃₀-intro q↑r↓≃r↑q↓) =
        let [p↑r↓]q↓≃[r↑p↓]q↓ =
              begin
                (p↑ * r↓) * q↓
              ≃⟨ AA.assoc ⟩
                p↑ * (r↓ * q↓)
              ≃⟨ AA.subst₂ AA.comm ⟩
                p↑ * (q↓ * r↓)
              ≃˘⟨ AA.assoc ⟩
                (p↑ * q↓) * r↓
              ≃⟨ AA.subst₂ p↑q↓≃q↑p↓ ⟩
                (q↑ * p↓) * r↓
              ≃⟨ AA.subst₂ AA.comm ⟩
                (p↓ * q↑) * r↓
              ≃⟨ AA.assoc ⟩
                p↓ * (q↑ * r↓)
              ≃⟨ AA.subst₂ q↑r↓≃r↑q↓ ⟩
                p↓ * (r↑ * q↓)
              ≃˘⟨ AA.assoc ⟩
                (p↓ * r↑) * q↓
              ≃⟨ AA.subst₂ AA.comm  ⟩
                (r↑ * p↓) * q↓
              ∎
            p↑r↓≃r↑p↓ = AA.cancel [p↑r↓]q↓≃[r↑p↓]q↓
         in ≃₀-intro p↑r↓≃r↑p↓

  eq : Eq ℚ
  eq = Eq.equivalence _≃₀_

  decEq : DecEq ℚ
  decEq = DecEq-intro _≃?₀_
    where
      _≃?₀_ : (p q : ℚ) {{_ : ⊤}} → Dec (p ≃ q)
      (p↑ // p↓) ≃?₀ (q↑ // q↓) =
        dec-map ≃₀-intro _≃₀_.elim (p↑ * q↓ ≃? q↑ * p↓)

  from-ℤ : ℤ As ℚ
  from-ℤ = Cast.As-intro (_// 1)

  //-substitutiveᴸ : AA.Substitutive₂ᶜ AA.handᴸ _//_ _≃_ _≃_
  //-substitutiveᴸ = AA.substitutive₂ //-substᴸ
    where
      //-substᴸ :
        {a₁ a₂ b : ℤ} {{c₁ : b ≄ 0}} {{c₂ : b ≄ 0}} →
        a₁ ≃ a₂ → (a₁ // b) {{c₁}} ≃ (a₂ // b) {{c₂}}
      //-substᴸ {a₁} {a₂} {b} a₁≃a₂ =
        let componentEq =
              begin
                a₁ * b
              ≃⟨ AA.subst₂ a₁≃a₂ ⟩
                a₂ * b
              ∎
         in ≃₀-intro componentEq

  //-substitutiveᴿ : AA.Substitutive₂ᶜ AA.handᴿ _//_ _≃_ _≃_
  //-substitutiveᴿ = AA.substitutive₂ //-substᴿ
    where
      //-substᴿ :
        {a₁ a₂ b : ℤ} {{_ : a₁ ≄ 0}} {{_ : a₂ ≄ 0}} →
        a₁ ≃ a₂ → b // a₁ ≃ b // a₂
      //-substᴿ {a₁} {a₂} {b} a₁≃a₂ =
        let componentEq =
              begin
                b * a₂
              ≃˘⟨ AA.subst₂ a₁≃a₂ ⟩
                b * a₁
              ∎
         in ≃₀-intro componentEq

  //-substitutive : AA.Substitutive²ᶜ _//_ _≃_ _≃_
  //-substitutive = AA.substitutive²

  //-cancellativeᴸ :
    AA.Cancellativeᶜ AA.handᴸ _//_ (AA.tc₂ _≃_) (AA.tc₂ _≃_) _⟨→⟩_ (_≄ 0)
  //-cancellativeᴸ = AA.cancellative //-cancelᴸ
    where
      //-cancelᴸ :
        {a : ℤ} {{_ : a ≄ 0}} {b₁ b₂ : ℤ} {{c₁ : b₁ ≄ 0}} {{c₂ : b₂ ≄ 0}} →
        a // b₁ ≃ a // b₂ → b₁ ≃ b₂
      //-cancelᴸ (≃₀-intro ab₂≃ab₁) = AA.cancelᴸ {B = ℤ} (Eq.sym ab₂≃ab₁)

  //-cancellativeᴿ :
    AA.Cancellativeᶜ AA.handᴿ _//_ (AA.tc₂ _≃_) (AA.tc₂ _≃_) _⟨→⟩_ (const ⊤)
  //-cancellativeᴿ = AA.cancellative //-cancelᴿ
    where
      //-cancelᴿ :
        {a b₁ b₂ : ℤ} {{c₁ : a ≄ 0}} {{c₂ : a ≄ 0}} →
        (b₁ // a) {{c₁}} ≃ (b₂ // a) {{c₂}} → b₁ ≃ b₂
      //-cancelᴿ {{c₁ = c₁}} (≃₀-intro b₁a≃b₂a) = AA.cancel {{cx = c₁}} b₁a≃b₂a

  //-cancellative :
    AA.Cancellative²ᶜ _//_ (AA.tc₂ _≃_) (AA.tc₂ _≃_) _⟨→⟩_ (_≄ 0) (const ⊤)
  //-cancellative = AA.cancellative²

  from-ℤ-substitutive : AA.Substitutive₁ (_as ℚ) _≃_ _≃_
  from-ℤ-substitutive = AA.substitutive₁ from-ℤ-subst
    where
      from-ℤ-subst : {a₁ a₂ : ℤ} → a₁ ≃ a₂ → (a₁ as ℚ) ≃ (a₂ as ℚ)
      from-ℤ-subst {a₁} {a₂} a₁≃a₂ =
        begin
          (a₁ as ℚ)
        ≃⟨⟩
          a₁ // 1
        ≃⟨ AA.subst₂ a₁≃a₂ ⟩
          a₂ // 1
        ≃⟨⟩
          (a₂ as ℚ)
        ∎

  from-ℤ-injective : AA.Injective (_as ℚ) _≃_ _≃_
  from-ℤ-injective = AA.injective from-ℤ-inject
    where
      from-ℤ-inject : {a₁ a₂ : ℤ} → (a₁ as ℚ) ≃ (a₂ as ℚ) → a₁ ≃ a₂
      from-ℤ-inject {a₁} {a₂} a₁-as-ℚ≃a₂-as-ℚ =
        let a₁//1≃a₂//1 =
              begin
                a₁ // 1
              ≃⟨⟩
                (a₁ as ℚ)
              ≃⟨ a₁-as-ℚ≃a₂-as-ℚ ⟩
                (a₂ as ℚ)
              ≃⟨⟩
                a₂ // 1
              ∎
         in AA.cancel a₁//1≃a₂//1

-- Create Base instance so we can import literals
private
  open import net.cruhland.axioms.Rationals.BaseDecl PA Z using (Base)

  base : Base
  base = record { ℚ = ℚ }

import net.cruhland.axioms.Rationals.LiteralImpl PA Z base as LiteralImpl

q≃0-from-q↑≃0 : {q : ℚ} → numerator q ≃ 0 → q ≃ 0
q≃0-from-q↑≃0 q@{q↑ // q↓} q↑≃0 =
    begin
      q
    ≃⟨⟩
      q↑ // q↓
    ≃⟨ AA.subst₂ q↑≃0 ⟩
      0 // q↓
    ≃⟨ ≃₀-intro componentEq ⟩
      0 // 1
    ≃⟨⟩
      0
    ∎
  where
    componentEq =
      begin
        0 * 1
      ≃⟨ AA.absorb ⟩
        0
      ≃˘⟨ AA.absorb ⟩
        0 * q↓
      ∎

q↑≃0-from-q≃0 : {q : ℚ} → q ≃ 0 → numerator q ≃ 0
q↑≃0-from-q≃0 q@{q↑ // q↓} (≃₀-intro q↑*1≃0*q↓) =
  begin
    numerator q
  ≃⟨⟩
    q↑
  ≃˘⟨ AA.ident ⟩
    q↑ * 1
  ≃⟨ q↑*1≃0*q↓ ⟩
    0 * q↓
  ≃⟨ AA.absorb ⟩
    0
  ∎

a//a≃1 : {a : ℤ} {{_ : a ≄ 0}} → a // a ≃ 1
a//a≃1 {a} =
    begin
      a // a
    ≃⟨ ≃₀-intro componentEq ⟩
      1 // 1
    ≃⟨⟩
      1
    ∎
  where
    componentEq =
      begin
        a * 1
      ≃⟨ AA.comm ⟩
        1 * a
      ∎
