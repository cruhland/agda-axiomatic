open import Function using (_∘_)
open import Relation.Nullary.Decidable using (fromWitnessFalse)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_; _value_)
open import net.cruhland.axioms.DecEq using (_≃?_; DecEq)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_; Eq)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators using (_*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (⊤; ∨-forceᴸ; Dec; dec-map; yes; no)

module net.cruhland.models.Rationals.Equality (PA : PeanoArithmetic) where

private module ℕ = PeanoArithmetic PA
open import net.cruhland.models.Integers PA as ℤ using (ℤ)
open import net.cruhland.models.Rationals.Base PA as ℚ using (_//_~_; ℚ)
import net.cruhland.models.Rationals.Literals PA as ℚLit

infix 4 _≃₀_
record _≃₀_ (p q : ℚ) : Set where
  constructor ≃₀-intro
  field
    elim : ℚ.n p * ℚ.d q ≃ ℚ.n q * ℚ.d p

private
  1≄0 : (ℤ value 1) ≄ 0
  1≄0 = ℕ.step≄zero ∘ AA.inject

instance
  -- Exercise 4.2.1
  ≃₀-reflexive : Eq.Reflexive _≃₀_
  ≃₀-reflexive = record { refl = ≃₀-intro Eq.refl }

  ≃₀-symmetric : Eq.Symmetric _≃₀_
  ≃₀-symmetric = record { sym = ≃₀-intro ∘ Eq.sym ∘ _≃₀_.elim }

  ≃₀-transitive : Eq.Transitive _≃₀_
  ≃₀-transitive = record { trans = ≃₀-trans }
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
            ≃⟨ AA.assoc {A = ℤ} {{eq = ℤ.eq}} {_⊙_ = _*_}⟩
              p↑ * (r↓ * q↓)
            ≃⟨ AA.substᴿ AA.comm ⟩
              p↑ * (q↓ * r↓)
            ≃˘⟨ AA.assoc ⟩
              (p↑ * q↓) * r↓
            ≃⟨ AA.subst p↑q↓≃q↑p↓ ⟩
              (q↑ * p↓) * r↓
            ≃⟨ AA.subst {f = _* r↓} AA.comm ⟩
              (p↓ * q↑) * r↓
            ≃⟨ AA.assoc ⟩
              p↓ * (q↑ * r↓)
            ≃⟨ AA.substᴿ q↑r↓≃r↑q↓ ⟩
              p↓ * (r↑ * q↓)
            ≃˘⟨ AA.assoc ⟩
              (p↓ * r↑) * q↓
            ≃⟨ AA.subst {f = _* q↓} AA.comm  ⟩
              r↑ * p↓ * q↓
            ∎
          p↑r↓≃r↑p↓ = AA.cancelᴿ {{c = fromWitnessFalse q↓≄0}} p↑r↓q↓≃r↑p↓q↓
        in ≃₀-intro p↑r↓≃r↑p↓
 
  eq : Eq ℚ
  eq = record { _≃_ = _≃₀_ }

  decEq : DecEq ℚ
  decEq = record { Constraint = λ _ _ → ⊤ ; _≃?_ = _≃?₀_ }
    where
      _≃?₀_ : (x y : ℚ) {{_ : ⊤}} → Dec (x ≃ y)
      p ≃?₀ q = dec-map ≃₀-intro _≃₀_.elim ℤ≃?
        where
          ℤ≃? = ℚ.n p * ℚ.d q ≃? ℚ.n q * ℚ.d p

  from-ℤ-substitutive₁ : AA.Substitutive₁ {A = ℤ} (_as ℚ) _≃_ _≃_
  from-ℤ-substitutive₁ = record { subst = ≃₀-intro ∘ AA.subst }

  from-ℤ-injective : AA.Injective {A = ℤ} _≃_ _≃_ (_as ℚ)
  from-ℤ-injective =
    record { inject = AA.cancelᴿ {{c = fromWitnessFalse 1≄0}} ∘ _≃₀_.elim }

q≃0 : ∀ {q} → ℚ.n q ≃ 0 → q ≃ 0
q≃0 {q} n≃0 = ≃₀-intro n1≃0d
  where
    n1≃0d =
      begin
        (ℚ.n q) * 1
      ≃⟨ AA.identᴿ ⟩
        ℚ.n q
      ≃⟨ n≃0 ⟩
        0
      ≃˘⟨ AA.absorbᴸ ⟩
        0 * ℚ.d q
      ∎

q↑≃0 : ∀ {q} → q ≃ 0 → ℚ.n q ≃ 0
q↑≃0 {q} (≃₀-intro n1≃0d) =
  begin
    ℚ.n q
  ≃˘⟨ AA.identᴿ ⟩
    (ℚ.n q) * 1
  ≃⟨ n1≃0d ⟩
    0 * ℚ.d q
  ≃⟨ AA.absorbᴸ ⟩
    0
  ∎

subst↑ :
  ∀ {q↑₁ q↑₂ q↓} (q↓≄0 : q↓ ≄ 0) → q↑₁ ≃ q↑₂ →
    (q↑₁ // q↓ ~ q↓≄0) ≃ (q↑₂ // q↓ ~ q↓≄0)
subst↑ _ q↑₁≃q↑₂ = ≃₀-intro (AA.subst q↑₁≃q↑₂)

subst↓ :
  ∀ {q↑ q↓₁ q↓₂} (q↓₁≄0 : q↓₁ ≄ 0) (q↓₂≄0 : q↓₂ ≄ 0) → q↓₁ ≃ q↓₂ →
    (q↑ // q↓₁ ~ q↓₁≄0) ≃ (q↑ // q↓₂ ~ q↓₂≄0)
subst↓ _ _ q↓₁≃q↓₂ = ≃₀-intro (AA.substᴿ (Eq.sym q↓₁≃q↓₂))

q≃1 : ∀ {q} → ℚ.n q ≃ ℚ.d q → q ≃ 1
q≃1 {q↑ // q↓ ~ _} q↑≃q↓ = ≃₀-intro q↑1≃1q↓
  where
    q↑1≃1q↓ =
      begin
        q↑ * 1
      ≃⟨ AA.comm ⟩
        1 * q↑
      ≃⟨ AA.substᴿ q↑≃q↓ ⟩
        1 * q↓
      ∎

q↑≃q↓ : ∀ {q} → q ≃ 1 → ℚ.n q ≃ ℚ.d q
q↑≃q↓ (≃₀-intro q↑1≃1q↓) =
  AA.cancelᴸ {{c = fromWitnessFalse 1≄0}} (Eq.trans AA.comm q↑1≃1q↓)
