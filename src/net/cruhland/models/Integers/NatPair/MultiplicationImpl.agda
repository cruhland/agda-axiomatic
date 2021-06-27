import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators as Op using (_+_; -_; _*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.models.Integers.NatPair.MultiplicationImpl
  (PA : PeanoArithmetic) where

private open module ℕ = PeanoArithmetic PA using (ℕ)
import net.cruhland.models.Integers.NatPair.AdditionImpl PA as ℤ+
open import net.cruhland.models.Integers.NatPair.BaseImpl PA as ℤB
  using (_—_; ℤ; ≃₀-intro)
import net.cruhland.models.Integers.NatPair.NegationImpl PA as ℤ-

_*₀_ : ℤ → ℤ → ℤ
(a⁺ — a⁻) *₀ (b⁺ — b⁻) = (a⁺ * b⁺ + a⁻ * b⁻) — (a⁺ * b⁻ + a⁻ * b⁺)

instance
  star : Op.Star ℤ
  star = Op.star _*₀_

  *-commutative : AA.Commutative _*_
  *-commutative = AA.commutative *-comm
    where
      *-comm : {a b : ℤ} → a * b ≃ b * a
      *-comm a@{a⁺ — a⁻} b@{b⁺ — b⁻} =
        begin
          a * b
        ≃⟨⟩
          (a⁺ — a⁻) * (b⁺ — b⁻)
        ≃⟨⟩
          (a⁺ * b⁺ + a⁻ * b⁻) — (a⁺ * b⁻ + a⁻ * b⁺)
        ≃⟨ AA.subst₂ (AA.subst₂ AA.comm) ⟩
          (b⁺ * a⁺ + a⁻ * b⁻) — (a⁺ * b⁻ + a⁻ * b⁺)
        ≃⟨ AA.subst₂ (AA.subst₂ AA.comm) ⟩
          (b⁺ * a⁺ + b⁻ * a⁻) — (a⁺ * b⁻ + a⁻ * b⁺)
        ≃⟨ AA.subst₂ AA.comm ⟩
          (b⁺ * a⁺ + b⁻ * a⁻) — (a⁻ * b⁺ + a⁺ * b⁻)
        ≃⟨ AA.subst₂ (AA.subst₂ AA.comm) ⟩
          (b⁺ * a⁺ + b⁻ * a⁻) — (b⁺ * a⁻ + a⁺ * b⁻)
        ≃⟨ AA.subst₂ (AA.subst₂ AA.comm) ⟩
          (b⁺ * a⁺ + b⁻ * a⁻) — (b⁺ * a⁻ + b⁻ * a⁺)
        ≃⟨⟩
          (b⁺ — b⁻) * (a⁺ — a⁻)
        ≃⟨⟩
          b * a
        ∎

  *-substitutiveᴸ : AA.Substitutive₂ AA.handᴸ _*_ _≃_ _≃_
  *-substitutiveᴸ = AA.substitutive₂ *-substᴸ
    where
      *-substᴸ : {a₁ a₂ b : ℤ} → a₁ ≃ a₂ → a₁ * b ≃ a₂ * b
      *-substᴸ
        a₁@{a₁⁺ — a₁⁻} a₂@{a₂⁺ — a₂⁻} b@{b⁺ — b⁻} (≃₀-intro a₁⁺+a₂⁻≃a₂⁺+a₁⁻) =
          begin
            a₁ * b
          ≃⟨⟩
            (a₁⁺ — a₁⁻) * (b⁺ — b⁻)
          ≃⟨⟩
            (a₁⁺ * b⁺ + a₁⁻ * b⁻) — (a₁⁺ * b⁻ + a₁⁻ * b⁺)
          ≃⟨ ≃₀-intro componentEq ⟩
            (a₂⁺ * b⁺ + a₂⁻ * b⁻) — (a₂⁺ * b⁻ + a₂⁻ * b⁺)
          ≃⟨⟩
            (a₂⁺ — a₂⁻) * (b⁺ — b⁻)
          ≃⟨⟩
            a₂ * b
          ∎
        where
          rearr :
            ∀ {u v w x y z} →
              (w * u + x * v) + (y * v + z * u) ≃
                (w + z) * u + (y + x) * v
          rearr {u} {v} {w} {x} {y} {z} =
            begin
              (w * u + x * v) + (y * v + z * u)
            ≃⟨ AA.perm-adcb ⟩
              (w * u + z * u) + (y * v + x * v)
            ≃˘⟨ AA.distrib-twoᴿ ⟩
              (w + z) * u + (y + x) * v
            ∎

          componentEq =
            begin
              (a₁⁺ * b⁺ + a₁⁻ * b⁻) + (a₂⁺ * b⁻ + a₂⁻ * b⁺)
            ≃⟨ rearr {w = a₁⁺} {y = a₂⁺} ⟩
              (a₁⁺ + a₂⁻) * b⁺ + (a₂⁺ + a₁⁻) * b⁻
            ≃⟨ AA.subst₂ (AA.subst₂ a₁⁺+a₂⁻≃a₂⁺+a₁⁻) ⟩
              (a₂⁺ + a₁⁻) * b⁺ + (a₂⁺ + a₁⁻) * b⁻
            ≃˘⟨ AA.subst₂ (AA.subst₂ a₁⁺+a₂⁻≃a₂⁺+a₁⁻) ⟩
              (a₂⁺ + a₁⁻) * b⁺ + (a₁⁺ + a₂⁻) * b⁻
            ≃˘⟨ rearr {w = a₂⁺} {y = a₁⁺} ⟩
              (a₂⁺ * b⁺ + a₂⁻ * b⁻) + (a₁⁺ * b⁻ + a₁⁻ * b⁺)
            ∎

  *-substitutiveᴿ : AA.Substitutive₂ AA.handᴿ _*_ _≃_ _≃_
  *-substitutiveᴿ = AA.substᴿ-from-substᴸ-comm {A = ℤ}

  *-substitutive : AA.Substitutive² _*_ _≃_ _≃_
  *-substitutive = AA.substitutive² {A = ℤ}

  *-compatible-ℕ : AA.Compatible₂ (_as ℤ) _*_ _*_ _≃_
  *-compatible-ℕ = AA.compatible₂ {A = ℕ} *-compat-ℕ
    where
      *-compat-ℕ : {n m : ℕ} → (n * m as ℤ) ≃ (n as ℤ) * (m as ℤ)
      *-compat-ℕ {n} {m} =
        begin
          (n * m as ℤ)
        ≃⟨⟩
          (n * m) — 0
        ≃˘⟨ AA.subst₂ AA.ident ⟩
          (n * m + 0) — 0
        ≃˘⟨ AA.subst₂ (AA.subst₂ AA.absorbᴸ) ⟩
          (n * m + 0 * 0) — 0
        ≃˘⟨ AA.subst₂ AA.identᴸ ⟩
          (n * m + 0 * 0) — (0 + 0)
        ≃˘⟨ AA.subst₂ (AA.subst₂ AA.absorb) ⟩
          (n * m + 0 * 0) — (n * 0 + 0)
        ≃˘⟨ AA.subst₂ (AA.subst₂ AA.absorb) ⟩
          (n * m + 0 * 0) — (n * 0 + 0 * m)
        ≃⟨⟩
          n — 0 * m — 0
        ≃⟨⟩
          (n as ℤ) * (m as ℤ)
        ∎

  *-identityᴸ : AA.Identity AA.handᴸ _*_ 1
  *-identityᴸ = AA.identity *-identᴸ
    where
      *-identᴸ : {a : ℤ} → 1 * a ≃ a
      *-identᴸ a@{a⁺ — a⁻} =
          begin
            1 * a
          ≃⟨⟩
            (1 — 0) * (a⁺ — a⁻)
          ≃⟨⟩
            (1 * a⁺ + 0 * a⁻) — (1 * a⁻ + 0 * a⁺)
          ≃⟨ AA.subst₂ simplify ⟩
            a⁺ — (1 * a⁻ + 0 * a⁺)
          ≃⟨ AA.subst₂ simplify ⟩
            a⁺ — a⁻
          ≃⟨⟩
            a
          ∎
        where
          simplify : {n m : ℕ} → 1 * n + 0 * m ≃ n
          simplify {n} {m} =
            begin
              1 * n + 0 * m
            ≃⟨ AA.subst₂ AA.absorb ⟩
              1 * n + 0
            ≃⟨ AA.ident ⟩
              1 * n
            ≃⟨ AA.ident ⟩
              n
            ∎

  *-identityᴿ : AA.Identity AA.handᴿ _*_ 1
  *-identityᴿ = AA.identityᴿ-from-identityᴸ {A = ℤ}

  *-identity : AA.Identity² _*_ 1
  *-identity = AA.identity² {A = ℤ}

  private
    *-distributiveᴸ : AA.Distributive AA.handᴸ _*_ _+_
    *-distributiveᴸ = AA.distributive *-distribᴸ
      where
        *-distribᴸ : {a b c : ℤ} → a * (b + c) ≃ a * b + a * c
        *-distribᴸ a@{a⁺ — a⁻} b@{b⁺ — b⁻} c@{c⁺ — c⁻} =
            begin
              a * (b + c)
            ≃⟨⟩
              (a⁺ — a⁻) * ((b⁺ — b⁻) + (c⁺ — c⁻))
            ≃⟨⟩
              (a⁺ — a⁻) * ((b⁺ + c⁺) — (b⁻ + c⁻))
            ≃⟨⟩
              (a⁺ * (b⁺ + c⁺) + a⁻ * (b⁻ + c⁻)) —
                (a⁺ * (b⁻ + c⁻) + a⁻ * (b⁺ + c⁺))
            ≃⟨ AA.subst₂ refactor ⟩
              ((a⁺ * b⁺ + a⁻ * b⁻) + (a⁺ * c⁺ + a⁻ * c⁻)) —
                (a⁺ * (b⁻ + c⁻) + a⁻ * (b⁺ + c⁺))
            ≃⟨ AA.subst₂ refactor ⟩
              ((a⁺ * b⁺ + a⁻ * b⁻) + (a⁺ * c⁺ + a⁻ * c⁻)) —
                ((a⁺ * b⁻ + a⁻ * b⁺) + (a⁺ * c⁻ + a⁻ * c⁺))
            ≃⟨⟩
              ((a⁺ * b⁺ + a⁻ * b⁻) — (a⁺ * b⁻ + a⁻ * b⁺)) +
                ((a⁺ * c⁺ + a⁻ * c⁻) — (a⁺ * c⁻ + a⁻ * c⁺))
            ≃⟨⟩
              (a⁺ — a⁻) * (b⁺ — b⁻) + (a⁺ — a⁻) * (c⁺ — c⁻)
            ≃⟨⟩
              a * b + a * c
            ∎
          where
            refactor :
              {b₁ b₂ a₁ a₂ a₃ a₄ : ℕ} →
                b₁ * (a₁ + a₃) + b₂ * (a₂ + a₄) ≃
                  (b₁ * a₁ + b₂ * a₂) + (b₁ * a₃ + b₂ * a₄)
            refactor {b₁} {b₂} {a₁} {a₂} {a₃} {a₄} =
              begin
                b₁ * (a₁ + a₃) + b₂ * (a₂ + a₄)
              ≃⟨ AA.distrib-twoᴸ ⟩
                (b₁ * a₁ + b₁ * a₃) + (b₂ * a₂ + b₂ * a₄)
              ≃⟨ AA.transpose ⟩
                (b₁ * a₁ + b₂ * a₂) + (b₁ * a₃ + b₂ * a₄)
              ∎

    *-distributiveᴿ : AA.Distributive AA.handᴿ _*_ _+_
    *-distributiveᴿ = AA.distributiveᴿ-from-distributiveᴸ {A = ℤ}

  *-distributive : AA.Distributive² _*_ _+_
  *-distributive = AA.distributive² {A = ℤ}

  *-associative : AA.Associative _*_
  *-associative = AA.associative *-assoc
    where
      *-assoc : {a b c : ℤ} → (a * b) * c ≃ a * (b * c)
      *-assoc a@{a⁺ — a⁻} b@{b⁺ — b⁻} c@{c⁺ — c⁻} =
        begin
          (a * b) * c
        ≃⟨⟩
          ((a⁺ — a⁻) * (b⁺ — b⁻)) * (c⁺ — c⁻)
        ≃⟨⟩
          ((a⁺ * b⁺ + a⁻ * b⁻) — (a⁺ * b⁻ + a⁻ * b⁺)) * (c⁺ — c⁻)
        ≃⟨⟩
          ((a⁺ * b⁺ + a⁻ * b⁻) * c⁺ + (a⁺ * b⁻ + a⁻ * b⁺) * c⁻) —
            ((a⁺ * b⁺ + a⁻ * b⁻) * c⁻ + (a⁺ * b⁻ + a⁻ * b⁺) * c⁺)
        ≃⟨ AA.subst₂ AA.refactor ⟩
          (a⁺ * (b⁺ * c⁺ + b⁻ * c⁻) + a⁻ * (b⁺ * c⁻ + b⁻ * c⁺)) —
            ((a⁺ * b⁺ + a⁻ * b⁻) * c⁻ + (a⁺ * b⁻ + a⁻ * b⁺) * c⁺)
        ≃⟨ AA.subst₂ AA.refactor ⟩
          (a⁺ * (b⁺ * c⁺ + b⁻ * c⁻) + a⁻ * (b⁺ * c⁻ + b⁻ * c⁺)) —
            (a⁺ * (b⁺ * c⁻ + b⁻ * c⁺) + a⁻ * (b⁺ * c⁺ + b⁻ * c⁻))
        ≃⟨⟩
          (a⁺ — a⁻) * ((b⁺ * c⁺ + b⁻ * c⁻) — (b⁺ * c⁻ + b⁻ * c⁺))
        ≃⟨⟩
          (a⁺ — a⁻) * ((b⁺ — b⁻) * (c⁺ — c⁻))
        ≃⟨⟩
          a * (b * c)
        ∎

  private
    *-comm-with-negᴸ : AA.FnOpCommutative AA.handᴸ -_ _*_
    *-comm-with-negᴸ = AA.fnOpCommutative *-negᴸ
      where
        *-negᴸ : {a b : ℤ} → - (a * b) ≃ - a * b
        *-negᴸ a@{a⁺ — a⁻} b@{b⁺ — b⁻} =
          begin
            - (a * b)
          ≃⟨⟩
            - ((a⁺ — a⁻) * (b⁺ — b⁻))
          ≃⟨⟩
            - ((a⁺ * b⁺ + a⁻ * b⁻) — (a⁺ * b⁻ + a⁻ * b⁺))
          ≃⟨⟩
            (a⁺ * b⁻ + a⁻ * b⁺) — (a⁺ * b⁺ + a⁻ * b⁻)
          ≃⟨ AA.subst₂ AA.comm ⟩
            (a⁻ * b⁺ + a⁺ * b⁻) — (a⁺ * b⁺ + a⁻ * b⁻)
          ≃⟨ AA.subst₂ AA.comm ⟩
            (a⁻ * b⁺ + a⁺ * b⁻) — (a⁻ * b⁻ + a⁺ * b⁺)
          ≃⟨⟩
            (a⁻ — a⁺) * (b⁺ — b⁻)
          ≃⟨⟩
            - (a⁺ — a⁻) * (b⁺ — b⁻)
          ≃⟨⟩
            - a * b
          ∎

    *-comm-with-negᴿ : AA.FnOpCommutative AA.handᴿ -_ _*_
    *-comm-with-negᴿ = AA.fnOpCommutativeᴿ-from-fnOpCommutativeᴸ

  *-comm-with-neg : AA.FnOpCommutative² -_ _*_
  *-comm-with-neg = AA.fnOpCommutative²

-- Include all proofs from the partial impl
open import net.cruhland.models.Integers.NatPair.AdditionDefn PA using (Z+)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
open import net.cruhland.models.Integers.NatPair.NegationDefn PA using (Z-)
open import net.cruhland.models.Integers.NatPair.SignDefn PA using (ZS)

open import net.cruhland.axioms.Integers.MultiplicationPartialImpl
  PA ZB Z+ Z- ZS using (MultiplicationProperties)
open MultiplicationProperties (record {}) public
  hiding
    (*-associative; *-comm-with-neg; *-commutative; *-compatible-ℕ
    ; *-distributive; *-identity; *-substitutive; star
    )
