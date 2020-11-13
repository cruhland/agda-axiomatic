-- Needed for positive integer literals
import Agda.Builtin.FromNat as FromNat
open import Function using (_∘_)
open import Relation.Nullary.Decidable using (fromWitnessFalse)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.DecEq using (_≃?_; DecEq)
open import net.cruhland.axioms.Eq using
  (_≃_; _≄_; Eq; refl; sym; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.axioms.Operators using (_*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Logic using (⊤; ∨-forceᴸ; Dec; dec-map; yes; no)

module net.cruhland.models.Rationals.Equality (PA : PeanoArithmetic) where

private module ℕ = PeanoArithmetic PA
open import net.cruhland.models.Integers PA as ℤ using (ℤ)
open import net.cruhland.models.Rationals.Base PA as Base using (_//_~_; ℚ)

infix 4 _≃₀_
record _≃₀_ (p q : ℚ) : Set where
  constructor ≃₀-intro
  field
    elim : ℚ.n p * ℚ.d q ≃ ℚ.n q * ℚ.d p

-- Exercise 4.2.1
≃₀-refl : ∀ {q} → q ≃₀ q
≃₀-refl = ≃₀-intro refl

≃₀-sym : ∀ {p q} → p ≃₀ q → q ≃₀ p
≃₀-sym = ≃₀-intro ∘ sym ∘ _≃₀_.elim

≃₀-trans : ∀ {p q r} → p ≃₀ q → q ≃₀ r → p ≃₀ r
≃₀-trans
  {p↑ // p↓ ~ _}
  {q↑ // q↓ ~ q↓≄0}
  {r↑ // r↓ ~ _}
  (≃₀-intro p↑q↓≃q↑p↓) (≃₀-intro q↑r↓≃r↑q↓) with q↑ ≃? 0
... | yes q↑≃0 =
  let p↑q↓≃0 =
        begin
          p↑ * q↓
        ≃⟨ p↑q↓≃q↑p↓ ⟩
          q↑ * p↓
        ≃⟨ AA.substᴸ q↑≃0 ⟩
          0 * p↓
        ≃⟨ AA.absorbᴸ ⟩
          0
        ∎
      r↑q↓≃0 =
        begin
          r↑ * q↓
        ≃˘⟨ q↑r↓≃r↑q↓ ⟩
          q↑ * r↓
        ≃⟨ AA.substᴸ q↑≃0 ⟩
          0 * r↓
        ≃⟨ AA.absorbᴸ ⟩
          0
        ∎
      p↑≃0 = ∨-forceᴸ q↓≄0 (AA.zero-prod p↑q↓≃0)
      r↑≃0 = ∨-forceᴸ q↓≄0 (AA.zero-prod r↑q↓≃0)
      p↑r↓≃r↑p↓ =
        begin
          p↑ * r↓
        ≃⟨ AA.substᴸ p↑≃0 ⟩
          0 * r↓
        ≃⟨ AA.absorbᴸ ⟩
          0
        ≃˘⟨ AA.absorbᴸ ⟩
          0 * p↓
        ≃˘⟨ AA.substᴸ r↑≃0 ⟩
          r↑ * p↓
        ∎
   in ≃₀-intro p↑r↓≃r↑p↓
... | no q↑≄0 =
  let p↑r↓[q↑q↓]≃r↑p↓[q↑q↓] =
        begin
          (p↑ * r↓) * (q↑ * q↓)
        ≃⟨ AA.perm-adcb {a = p↑} {c = q↑} ⟩
          (p↑ * q↓) * (q↑ * r↓)
        ≃⟨ AA.[a≃b][c≃d] p↑q↓≃q↑p↓ q↑r↓≃r↑q↓ ⟩
          (q↑ * p↓) * (r↑ * q↓)
        ≃⟨ AA.perm-adcb {a = q↑} {c = r↑} ⟩
          (q↑ * q↓) * (r↑ * p↓)
        ≃⟨ AA.comm {a = q↑ * q↓} ⟩
          (r↑ * p↓) * (q↑ * q↓)
        ∎
      q↑q↓≄0 = AA.nonzero-prod q↑≄0 q↓≄0
      p↑r↓≃r↑p↓ =
        AA.cancelᴿ {{c = fromWitnessFalse q↑q↓≄0}} p↑r↓[q↑q↓]≃r↑p↓[q↑q↓]
   in ≃₀-intro p↑r↓≃r↑p↓

instance
  eq : Eq ℚ
  eq = record
    { _≃_ = _≃₀_
    ; refl = ≃₀-refl
    ; sym = ≃₀-sym
    ; trans = ≃₀-trans
    }

  decEq : DecEq ℚ
  decEq = record { Constraint = λ _ _ → ⊤ ; _≃?_ = _≃?₀_ }
    where
      _≃?₀_ : (x y : ℚ) {{_ : ⊤}} → Dec (x ≃ y)
      p ≃?₀ q = dec-map ≃₀-intro _≃₀_.elim ℤ≃?
        where
          ℤ≃? = ℚ.n p * ℚ.d q ≃? ℚ.n q * ℚ.d p

  from-ℤ-substitutive₁ : AA.Substitutive₁ {A = ℤ} (_as ℚ)
  from-ℤ-substitutive₁ = record { subst = ≃₀-intro ∘ AA.substᴸ }

  from-ℤ-injective : AA.Injective {A = ℤ} (_as ℚ)
  from-ℤ-injective =
      record { inject = AA.cancelᴿ {{c = fromWitnessFalse 1≄0}} ∘ _≃₀_.elim }
    where
      1≄0 = ℕ.step≄zero ∘ AA.inject

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