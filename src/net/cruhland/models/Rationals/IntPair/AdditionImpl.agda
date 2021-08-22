import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op using (_+_; _*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.models.Rationals.IntPair.AdditionImpl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.models.Rationals.IntPair.BaseDefn PA Z using (QB)

private
  module ℤ = Integers Z
  module ℚ where
    open import net.cruhland.axioms.Rationals.LiteralImpl PA Z QB public
    open import net.cruhland.models.Rationals.IntPair.BaseImpl PA Z public

open ℤ using (ℤ)
open ℚ using (_//_; ℚ)

_+₀_ : ℚ → ℚ → ℚ
(p↑ // p↓) +₀ (q↑ // q↓) =
  ((p↑ * q↓ + p↓ * q↑) // (p↓ * q↓)) {{AA.nonzero-prod}}

instance
  plus : Op.Plus ℚ
  plus = Op.plus _+₀_

  +-commutative : AA.Commutative _+_
  +-commutative = AA.commutative +-comm
    where
      +-comm : {p q : ℚ} → p + q ≃ q + p
      +-comm p@{(p↑ // p↓) {{p↓≄0}}} q@{(q↑ // q↓) {{q↓≄0}}} =
        let instance p↓q↓≄0 = AA.nonzero-prod {{a≄0 = p↓≄0}} {{q↓≄0}}
            instance q↓p↓≄0 = AA.nonzero-prod {{a≄0 = q↓≄0}} {{p↓≄0}}
         in begin
              p + q
            ≃⟨⟩
              (p↑ // p↓) + (q↑ // q↓)
            ≃⟨⟩
              (p↑ * q↓ + p↓ * q↑) // (p↓ * q↓)
            ≃⟨ AA.subst₂ AA.comm ⟩
              (p↓ * q↑ + p↑ * q↓) // (p↓ * q↓)
            ≃⟨ AA.subst₂ (AA.subst₂ AA.comm) ⟩
              (q↑ * p↓ + p↑ * q↓) // (p↓ * q↓)
            ≃⟨ AA.subst₂ (AA.subst₂ AA.comm) ⟩
              (q↑ * p↓ + q↓ * p↑) // (p↓ * q↓)
            ≃⟨ AA.subst₂ AA.comm ⟩
              (q↑ * p↓ + q↓ * p↑) // (q↓ * p↓)
            ≃⟨⟩
              (q↑ // q↓) + (p↑ // p↓)
            ≃⟨⟩
              q + p
            ∎

  +-substitutiveᴸ : AA.Substitutive₂ AA.handᴸ _+_ _≃_ _≃_
  +-substitutiveᴸ = AA.substitutive₂ +-substᴸ
    where
      +-substᴸ : {p₁ p₂ q : ℚ} → p₁ ≃ p₂ → p₁ + q ≃ p₂ + q
      +-substᴸ
        p₁@{p₁↑ // p₁↓} p₂@{p₂↑ // p₂↓} q@{q↑ // q↓}
        (ℚ.≃₀-intro p₁↑p₂↓≃p₂↑p₁↓) =
          begin
            p₁ + q
          ≃⟨⟩
            (p₁↑ // p₁↓) + (q↑ // q↓)
          ≃⟨⟩
            ((p₁↑ * q↓ + p₁↓ * q↑) // (p₁↓ * q↓)) {{AA.nonzero-prod}}
          ≃⟨ ℚ.≃₀-intro componentEq ⟩
            ((p₂↑ * q↓ + p₂↓ * q↑) // (p₂↓ * q↓)) {{AA.nonzero-prod}}
          ≃⟨⟩
            (p₂↑ // p₂↓) + (q↑ // q↓)
          ≃⟨⟩
            p₂ + q
          ∎
        where
          prepare :
            {u v w x y z : ℤ} →
              (w * x + u * v) * (y * z) ≃ w * y * (x * z) + v * u * (y * z)
          prepare {u} {v} {w} {x} {y} {z} =
            begin
              (w * x + u * v) * (y * z)
            ≃⟨ AA.distrib ⟩
              w * x * (y * z) + u * v * (y * z)
            ≃⟨ AA.subst₂ AA.transpose ⟩
              w * y * (x * z) + u * v * (y * z)
            ≃⟨ AA.subst₂ (AA.subst₂ AA.comm) ⟩
              w * y * (x * z) + v * u * (y * z)
            ∎
          componentEq =
            begin
              (p₁↑ * q↓ + p₁↓ * q↑) * (p₂↓ * q↓)
            ≃⟨ prepare ⟩
              p₁↑ * p₂↓ * (q↓ * q↓) + q↑ * p₁↓ * (p₂↓ * q↓)
            ≃⟨ AA.subst₂ (AA.subst₂ p₁↑p₂↓≃p₂↑p₁↓) ⟩
              p₂↑ * p₁↓ * (q↓ * q↓) + q↑ * p₁↓ * (p₂↓ * q↓)
            ≃⟨ AA.subst₂ AA.transpose ⟩
               p₂↑ * p₁↓ * (q↓ * q↓) + q↑ * p₂↓ * (p₁↓ * q↓)
            ≃˘⟨ prepare ⟩
              (p₂↑ * q↓ + p₂↓ * q↑) * (p₁↓ * q↓)
            ∎

  +-substitutiveᴿ : AA.Substitutive₂ AA.handᴿ _+_ _≃_ _≃_
  +-substitutiveᴿ = AA.substᴿ-from-substᴸ-comm {A = ℚ}

  +-substitutive : AA.Substitutive² _+_ _≃_ _≃_
  +-substitutive = AA.substitutive² {A = ℚ}

  +-compatible-ℤ : AA.Compatible₂ (AA.tc₁ (_as ℚ)) _+_ _+_ _≃_
  +-compatible-ℤ = AA.compatible₂ {A = ℤ} +-compat-ℤ
    where
      +-compat-ℤ : {a b : ℤ} → (a + b as ℚ) ≃ (a as ℚ) + (b as ℚ)
      +-compat-ℤ {a} {b} =
        begin
          (a + b as ℚ)
        ≃⟨⟩
          (a + b) // 1
        ≃˘⟨ AA.subst₂ (AA.subst₂ AA.ident) ⟩
          (a * 1 + b) // 1
        ≃˘⟨ AA.subst₂ (AA.subst₂ AA.ident) ⟩
          (a * 1 + 1 * b) // 1
        ≃˘⟨ AA.subst₂ {{c₁ = AA.nonzero-prod}} AA.identᴸ ⟩
          ((a * 1 + 1 * b) // (1 * 1)) {{AA.nonzero-prod}}
        ≃⟨⟩
          (a // 1) + (b // 1)
        ≃⟨⟩
          (a as ℚ) + (b as ℚ)
        ∎

  +-associative : AA.Associative _+_
  +-associative = AA.associative +-assoc
    where
      +-assoc : {p q r : ℚ} → (p + q) + r ≃ p + (q + r)
      +-assoc
          p@{(p↑ // p↓) {{p↓≄0}}}
          q@{(q↑ // q↓) {{q↓≄0}}}
          r@{(r↑ // r↓) {{r↓≄0}}} =
        let instance p↓q↓≄0 = AA.nonzero-prod {{a≄0 = p↓≄0}} {{q↓≄0}}
            instance q↓r↓≄0 = AA.nonzero-prod {{a≄0 = q↓≄0}} {{r↓≄0}}
            instance [p↓q↓]r↓≄0 = AA.nonzero-prod {{a≄0 = p↓q↓≄0}} {{r↓≄0}}
            instance p↓[q↓r↓]≄0 = AA.nonzero-prod {{a≄0 = p↓≄0}} {{q↓r↓≄0}}
         in begin
              (p + q) + r
            ≃⟨⟩
              ((p↑ // p↓) + (q↑ // q↓)) + (r↑ // r↓)
            ≃⟨⟩
              ((p↑ * q↓ + p↓ * q↑) // (p↓ * q↓)) + (r↑ // r↓)
            ≃⟨⟩
              ((p↑ * q↓ + p↓ * q↑) * r↓ + (p↓ * q↓) * r↑) // ((p↓ * q↓) * r↓)
            ≃⟨ AA.subst₂ (AA.subst₂ AA.distrib) ⟩
              (((p↑ * q↓) * r↓ + (p↓ * q↑) * r↓) + (p↓ * q↓) * r↑)
              // ((p↓ * q↓) * r↓)
            ≃⟨ AA.subst₂ AA.assoc ⟩
              ((p↑ * q↓) * r↓ + ((p↓ * q↑) * r↓ + (p↓ * q↓) * r↑))
              // ((p↓ * q↓) * r↓)
            ≃⟨ AA.subst₂ (AA.subst₂ AA.assoc) ⟩
              (p↑ * (q↓ * r↓) + ((p↓ * q↑) * r↓ + (p↓ * q↓) * r↑))
              // ((p↓ * q↓) * r↓)
            ≃⟨ AA.subst₂ (AA.subst₂ (AA.subst₂ AA.assoc)) ⟩
              (p↑ * (q↓ * r↓) + (p↓ * (q↑ * r↓) + (p↓ * q↓) * r↑))
              // ((p↓ * q↓) * r↓)
            ≃⟨ AA.subst₂ (AA.subst₂ (AA.subst₂ AA.assoc)) ⟩
              (p↑ * (q↓ * r↓) + (p↓ * (q↑ * r↓) + p↓ * (q↓ * r↑)))
              // ((p↓ * q↓) * r↓)
            ≃˘⟨ AA.subst₂ (AA.subst₂ AA.distrib) ⟩
              (p↑ * (q↓ * r↓) + p↓ * (q↑ * r↓ + q↓ * r↑)) // ((p↓ * q↓) * r↓)
            ≃⟨ AA.subst₂ AA.assoc ⟩
              (p↑ * (q↓ * r↓) + p↓ * (q↑ * r↓ + q↓ * r↑)) // (p↓ * (q↓ * r↓))
            ≃⟨⟩
              (p↑ // p↓) + ((q↑ * r↓ + q↓ * r↑) // (q↓ * r↓))
            ≃⟨⟩
              (p↑ // p↓) + ((q↑ // q↓) + (r↑ // r↓))
            ≃⟨⟩
              p + (q + r)
            ∎

  +-identityᴸ : AA.Identity AA.handᴸ _+_ 0
  +-identityᴸ = AA.identity +-identᴸ
    where
      +-identᴸ : {q : ℚ} → 0 + q ≃ q
      +-identᴸ q@{(q↑ // q↓) {{q↓≄0}}} =
        let instance 1*q↓≄0 = AA.nonzero-prod {{a≄0 = ℤ.1≄0}} {{q↓≄0}}
         in begin
              0 + q
            ≃⟨⟩
              (0 // 1) + (q↑ // q↓)
            ≃⟨⟩
              (0 * q↓ + 1 * q↑) // (1 * q↓)
            ≃⟨ AA.subst₂ AA.ident ⟩
              (0 * q↓ + 1 * q↑) // q↓
            ≃⟨ AA.subst₂ (AA.subst₂ AA.absorb) ⟩
              (0 + 1 * q↑) // q↓
            ≃⟨ AA.subst₂ AA.ident ⟩
              (1 * q↑) // q↓
            ≃⟨ AA.subst₂ AA.ident ⟩
              q↑ // q↓
            ≃⟨⟩
              q
            ∎

  +-identityᴿ : AA.Identity AA.handᴿ _+_ 0
  +-identityᴿ = AA.identityᴿ-from-identityᴸ {A = ℚ}

  +-identity : AA.Identity² _+_ 0
  +-identity = AA.identity² {A = ℚ}
