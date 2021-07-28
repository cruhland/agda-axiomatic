import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.DecEq using (_≃?_; DecEq; DecEq-intro)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_; Eq)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators using (_*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Function using (_∘_)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (⊤; Dec; dec-map)

module net.cruhland.models.Rationals.Equality
  (PA : PeanoArithmetic) (Z : Integers PA) where

private open module ℕ = PeanoArithmetic PA using (ℕ)
private open module ℤ = Integers Z using (ℤ)
open import net.cruhland.models.Rationals.Base PA Z as ℚ using (_//_~_; ℚ)

infix 4 _≃₀_
record _≃₀_ (p q : ℚ) : Set where
  constructor ≃₀-intro
  field
    elim : ℚ.n p * ℚ.d q ≃ ℚ.n q * ℚ.d p

instance
  ≃₀-reflexive : Eq.Reflexive _≃₀_
  ≃₀-reflexive = Eq.reflexive (≃₀-intro Eq.refl)

  ≃₀-symmetric : Eq.Symmetric _≃₀_
  ≃₀-symmetric = Eq.symmetric (≃₀-intro ∘ Eq.sym ∘ _≃₀_.elim)

  ≃₀-transitive : Eq.Transitive _≃₀_
  ≃₀-transitive = Eq.transitive ≃₀-trans
    where
      ≃₀-trans : ∀ {p q r} → p ≃₀ q → q ≃₀ r → p ≃₀ r
      ≃₀-trans
        {p↑ // p↓ ~ _}
        {q↑ // q↓ ~ q↓≄0}
        {r↑ // r↓ ~ _}
        (≃₀-intro p↑q↓≃q↑p↓) (≃₀-intro q↑r↓≃r↑q↓) =
        let
          p↑r↓q↓≃r↑p↓q↓ =
            begin
              p↑ * r↓ * q↓
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
              r↑ * p↓ * q↓
            ∎
          instance _ = q↓≄0
          p↑r↓≃r↑p↓ = AA.cancel p↑r↓q↓≃r↑p↓q↓
        in ≃₀-intro p↑r↓≃r↑p↓

  eq : Eq ℚ
  eq = Eq.equivalence _≃₀_

  decEq : DecEq ℚ
  decEq = DecEq-intro _≃?₀_
    where
      _≃?₀_ : (x y : ℚ) {{_ : ⊤}} → Dec (x ≃ y)
      p ≃?₀ q = dec-map ≃₀-intro _≃₀_.elim ℤ≃?
        where
          ℤ≃? = ℚ.n p * ℚ.d q ≃? ℚ.n q * ℚ.d p

  from-ℤ-substitutive₁ : AA.Substitutive₁ {A = ℤ} (_as ℚ) _≃_ _≃_
  from-ℤ-substitutive₁ = AA.substitutive₁ (≃₀-intro ∘ AA.subst₂)

  from-ℤ-injective : AA.Injective (_as ℚ) _≃_ _≃_
  from-ℤ-injective = AA.injective {A = ℤ} (AA.cancel ∘ _≃₀_.elim)

literal≃ℤ-literal//1 :
  (n : Nat) → fromNatLiteral n ≃ (fromNatLiteral n) // 1 ~ ℤ.1≄0
literal≃ℤ-literal//1 n =
  begin
    fromNatLiteral n
  ≃⟨⟩
    (n as ℕ as ℤ as ℚ)
  ≃˘⟨ AA.subst₁ (ℤ.fromNatLiteral≃casts n) ⟩
    ((fromNatLiteral n) as ℚ)
  ≃⟨⟩
    (fromNatLiteral n) // 1 ~ ℤ.1≄0
  ∎

q≃0 : {q : ℚ} → ℚ.n q ≃ 0 → q ≃ 0
q≃0 q@{n // d ~ d≄0} n≃0 =
    begin
      q
    ≃⟨⟩
      n // d ~ d≄0
    ≃⟨ ≃₀-intro componentEq ⟩
      0 // 1 ~ ℤ.1≄0
    ≃⟨⟩
      (0 as ℚ)
    ≃⟨ AA.subst₁ (ℤ.fromNatLiteral≃casts 0) ⟩
      (0 as ℕ as ℤ as ℚ)
    ≃⟨⟩
      0
    ∎
  where
    componentEq =
      begin
        n * 1
      ≃⟨ AA.ident ⟩
        n
      ≃⟨ n≃0 ⟩
        0
      ≃˘⟨ AA.absorb ⟩
        0 * d
      ∎

q↑≃0 : ∀ {q} → q ≃ 0 → ℚ.n q ≃ 0
q↑≃0 q@{n // d ~ d≄0} (≃₀-intro n1≃[0-as-ℕ-as-ℤ]d) =
  begin
    ℚ.n q
  ≃⟨⟩
    n
  ≃˘⟨ AA.ident ⟩
    n * 1
  ≃⟨ n1≃[0-as-ℕ-as-ℤ]d ⟩
    (0 as ℕ as ℤ) * d
  ≃˘⟨ AA.subst₂ (ℤ.fromNatLiteral≃casts 0) ⟩
    0 * d
  ≃⟨ AA.absorb ⟩
    0
  ∎

subst↑ :
  ∀ {q↑₁ q↑₂ q↓} (q↓≄0 : q↓ ≄ 0) → q↑₁ ≃ q↑₂ →
    (q↑₁ // q↓ ~ q↓≄0) ≃ (q↑₂ // q↓ ~ q↓≄0)
subst↑ _ q↑₁≃q↑₂ = ≃₀-intro (AA.subst₂ q↑₁≃q↑₂)

subst↓ :
  ∀ {q↑ q↓₁ q↓₂} (q↓₁≄0 : q↓₁ ≄ 0) (q↓₂≄0 : q↓₂ ≄ 0) → q↓₁ ≃ q↓₂ →
    (q↑ // q↓₁ ~ q↓₁≄0) ≃ (q↑ // q↓₂ ~ q↓₂≄0)
subst↓ _ _ q↓₁≃q↓₂ = ≃₀-intro (AA.subst₂ (Eq.sym q↓₁≃q↓₂))

q≃1 : ∀ {q} → ℚ.n q ≃ ℚ.d q → q ≃ 1
q≃1 q@{q↑ // q↓ ~ q↓≄0} q↑≃q↓ =
  begin
    q
  ≃⟨⟩
    q↑ // q↓ ~ q↓≄0
  ≃⟨ subst↑ q↓≄0 q↑≃q↓ ⟩
    q↓ // q↓ ~ q↓≄0
  ≃⟨ ≃₀-intro AA.comm ⟩
    1 // 1 ~ ℤ.1≄0
  ≃⟨⟩
    (1 as ℚ)
  ≃⟨ AA.subst₁ (ℤ.fromNatLiteral≃casts 1) ⟩
    (1 as ℕ as ℤ as ℚ)
  ≃⟨⟩
    1
  ∎

q↑≃q↓ : ∀ {q} → q ≃ 1 → ℚ.n q ≃ ℚ.d q
q↑≃q↓ q@{q↑ // q↓ ~ q↓≄0} (≃₀-intro q↑1≃[1-as-ℕ-as-ℤ]q↓) =
  begin
    ℚ.n q
  ≃⟨⟩
    q↑
  ≃˘⟨ AA.ident ⟩
    q↑ * 1
  ≃⟨ q↑1≃[1-as-ℕ-as-ℤ]q↓ ⟩
    (1 as ℕ as ℤ) * q↓
  ≃˘⟨ AA.subst₂ (ℤ.fromNatLiteral≃casts 1) ⟩
    1 * q↓
  ≃⟨ AA.ident ⟩
    q↓
  ≃⟨⟩
    ℚ.d q
  ∎
