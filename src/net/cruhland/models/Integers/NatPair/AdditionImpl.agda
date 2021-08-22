import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators as Op using (_+_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.models.Integers.NatPair.AdditionImpl
  (PA : PeanoArithmetic) where

open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)

private
  module ℕ = PeanoArithmetic PA
  module ℤ where
    open import net.cruhland.axioms.Integers.LiteralImpl PA ZB public
    open import net.cruhland.models.Integers.NatPair.BaseImpl PA public

open ℕ using (ℕ)
open ℤ using (_—_; ℤ)

_+₀_ : ℤ → ℤ → ℤ
(a⁺ — a⁻) +₀ (b⁺ — b⁻) = (a⁺ + b⁺) — (a⁻ + b⁻)

instance
  plus : Op.Plus ℤ
  plus = Op.plus _+₀_

  +-commutative : AA.Commutative _+_
  +-commutative = AA.commutative +-comm
    where
      +-comm : {a b : ℤ} → a + b ≃ b + a
      +-comm a@{a⁺ — a⁻} b@{b⁺ — b⁻} =
        begin
          a + b
        ≃⟨⟩
          (a⁺ — a⁻) + (b⁺ — b⁻)
        ≃⟨⟩
          (a⁺ + b⁺) — (a⁻ + b⁻)
        ≃⟨ AA.subst₂ AA.comm ⟩
          (b⁺ + a⁺) — (a⁻ + b⁻)
        ≃⟨ AA.subst₂ AA.comm ⟩
          (b⁺ + a⁺) — (b⁻ + a⁻)
        ≃⟨⟩
          (b⁺ — b⁻) + (a⁺ — a⁻)
        ≃⟨⟩
          b + a
        ∎

  +-substitutiveᴸ : AA.Substitutive₂ AA.handᴸ _+_ _≃_ _≃_
  +-substitutiveᴸ = AA.substitutive₂ +-substᴸ
    where
      +-substᴸ : {a₁ a₂ b : ℤ} → a₁ ≃ a₂ → a₁ + b ≃ a₂ + b
      +-substᴸ
          a₁@{a₁⁺ — a₁⁻} a₂@{a₂⁺ — a₂⁻} b@{b⁺ — b⁻}
          (ℤ.≃₀-intro a₁⁺+a₂⁻≃a₂⁺+a₁⁻) =
            begin
              a₁ + b
            ≃⟨⟩
              (a₁⁺ — a₁⁻) + (b⁺ — b⁻)
            ≃⟨⟩
              (a₁⁺ + b⁺) — (a₁⁻ + b⁻)
            ≃⟨ ℤ.≃₀-intro componentEq ⟩
              (a₂⁺ + b⁺) — (a₂⁻ + b⁻)
            ≃⟨⟩
              (a₂⁺ — a₂⁻) + (b⁺ — b⁻)
            ≃⟨⟩
              a₂ + b
            ∎
        where
          componentEq =
            begin
              (a₁⁺ + b⁺) + (a₂⁻ + b⁻)
            ≃⟨ AA.transpose ⟩
              (a₁⁺ + a₂⁻) + (b⁺ + b⁻)
            ≃⟨ AA.subst₂ a₁⁺+a₂⁻≃a₂⁺+a₁⁻ ⟩
              (a₂⁺ + a₁⁻) + (b⁺ + b⁻)
            ≃⟨ AA.transpose ⟩
              (a₂⁺ + b⁺) + (a₁⁻ + b⁻)
            ∎

  +-substitutiveᴿ : AA.Substitutive₂ AA.handᴿ _+_ _≃_ _≃_
  +-substitutiveᴿ = AA.substᴿ-from-substᴸ-comm {A = ℤ}

  +-substitutive : AA.Substitutive² _+_ _≃_ _≃_
  +-substitutive = AA.substitutive² {A = ℤ}

  +-associative : AA.Associative _+_
  +-associative = record { assoc = +-assoc }
    where
      +-assoc : {a b c : ℤ} → (a + b) + c ≃ a + (b + c)
      +-assoc a@{a⁺ — a⁻} b@{b⁺ — b⁻} c@{c⁺ — c⁻} =
        begin
          (a + b) + c
        ≃⟨⟩
          ((a⁺ — a⁻) + (b⁺ — b⁻)) + (c⁺ — c⁻)
        ≃⟨⟩
          ((a⁺ + b⁺) — (a⁻ + b⁻)) + (c⁺ — c⁻)
        ≃⟨⟩
          ((a⁺ + b⁺) + c⁺) — ((a⁻ + b⁻) + c⁻)
        ≃⟨ AA.subst₂ AA.assoc ⟩
          (a⁺ + (b⁺ + c⁺)) — ((a⁻ + b⁻) + c⁻)
        ≃⟨ AA.subst₂ AA.assoc ⟩
          (a⁺ + (b⁺ + c⁺)) — (a⁻ + (b⁻ + c⁻))
        ≃⟨⟩
          (a⁺ — a⁻) + ((b⁺ + c⁺) — (b⁻ + c⁻))
        ≃⟨⟩
          (a⁺ — a⁻) + ((b⁺ — b⁻) + (c⁺ — c⁻))
        ≃⟨⟩
          a + (b + c)
        ∎

  +-compatible-ℕ : AA.Compatible₂ (AA.tc₁ (_as ℤ)) _+_ _+_ _≃_
  +-compatible-ℕ = AA.compatible₂ {A = ℕ} +-compat-ℕ
    where
      +-compat-ℕ : {n m : ℕ} → (n + m as ℤ) ≃ (n as ℤ) + (m as ℤ)
      +-compat-ℕ {n} {m} =
        begin
          (n + m as ℤ)
        ≃⟨⟩
          (n + m) — 0
        ≃˘⟨ AA.subst₂ AA.identᴸ ⟩
          (n + m) — (0 + 0)
        ≃⟨⟩
          (n — 0) + (m — 0)
        ≃⟨⟩
          (n as ℤ) + (m as ℤ)
        ∎

  +-identityᴸ : AA.Identity AA.handᴸ _+_ 0
  +-identityᴸ = AA.identity +-identᴸ
    where
      +-identᴸ : {a : ℤ} → 0 + a ≃ a
      +-identᴸ a@{a⁺ — a⁻} =
        begin
          0 + a
        ≃⟨⟩
          (0 — 0) + (a⁺ — a⁻)
        ≃⟨⟩
          (0 + a⁺) — (0 + a⁻)
        ≃⟨ AA.subst₂ AA.ident ⟩
          a⁺ — (0 + a⁻)
        ≃⟨ AA.subst₂ AA.ident ⟩
          a
        ∎

  +-identityᴿ : AA.Identity AA.handᴿ _+_ 0
  +-identityᴿ = AA.identityᴿ-from-identityᴸ {A = ℤ}

  +-identity : AA.Identity² _+_ 0
  +-identity = AA.identity² {A = ℤ}
