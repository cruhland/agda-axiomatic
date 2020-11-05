open import Agda.Builtin.FromNat using (Number)
import Agda.Builtin.Nat as Nat
open import Function using (_∘_)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_As_; _as_)
open import net.cruhland.axioms.Eq using (_≃_; sym; trans; module ≃-Reasoning)
open ≃-Reasoning
import net.cruhland.axioms.Operators as Op
open Op using (_+_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Logic using (⊤)

module net.cruhland.models.Integers.Addition (PA : PeanoArithmetic) where

private module ℕ = PeanoArithmetic PA
open ℕ using (ℕ)
open import net.cruhland.models.Integers.Base PA using (_—_; ℤ)
import net.cruhland.models.Integers.Equality PA as Equality
open Equality using (≃ᶻ-elim; ≃ᶻ-intro)

instance
  plus : Op.Plus ℤ
  plus = record { _+_ = _+₀_ }
    where
      infixl 6 _+₀_
      _+₀_ : ℤ → ℤ → ℤ
      a⁺ — a⁻ +₀ b⁺ — b⁻ = (a⁺ + b⁺) — (a⁻ + b⁻)

instance
  +-commutative : AA.Commutative _+_
  +-commutative = record { comm = +-comm }
    where
      +-comm : {a b : ℤ} → a + b ≃ b + a
      +-comm {a⁺ — a⁻} {b⁺ — b⁻} = ≃ᶻ-intro eq′
        where
          eq′ =
            begin
              (a⁺ + b⁺) + (b⁻ + a⁻)
            ≃⟨ AA.substᴸ AA.comm ⟩
              (b⁺ + a⁺) + (b⁻ + a⁻)
            ≃⟨ AA.substᴿ AA.comm ⟩
              (b⁺ + a⁺) + (a⁻ + b⁻)
            ∎

  +-substitutiveᴸ : AA.Substitutiveᴸ _+_
  +-substitutiveᴸ = record { substᴸ = +-substᴸ }
    where
      +-substᴸ : {a₁ a₂ b : ℤ} → a₁ ≃ a₂ → a₁ + b ≃ a₂ + b
      +-substᴸ {a₁⁺ — a₁⁻} {a₂⁺ — a₂⁻} {b⁺ — b⁻} a₁≃a₂ = ≃ᶻ-intro eq′
        where
          a₁⁺+a₂⁻≃a₂⁺+a₁⁻ = ≃ᶻ-elim a₁≃a₂
          eq′ =
            begin
              (a₁⁺ + b⁺) + (a₂⁻ + b⁻)
            ≃⟨ AA.transpose ⟩
              (a₁⁺ + a₂⁻) + (b⁺ + b⁻)
            ≃⟨ AA.substᴸ a₁⁺+a₂⁻≃a₂⁺+a₁⁻ ⟩
              (a₂⁺ + a₁⁻) + (b⁺ + b⁻)
            ≃⟨ AA.transpose ⟩
              (a₂⁺ + b⁺) + (a₁⁻ + b⁻)
            ∎

  +-substitutiveᴿ : AA.Substitutiveᴿ {A = ℤ} _+_
  +-substitutiveᴿ = AA.substitutiveᴿ

  +-associative : AA.Associative _+_
  +-associative = record { assoc = +-assoc }
    where
      +-assoc : {x y z : ℤ} → (x + y) + z ≃ x + (y + z)
      +-assoc {x⁺ — x⁻} {y⁺ — y⁻} {z⁺ — z⁻} = ≃ᶻ-intro eq′
        where
          eq′ =
            begin
              ((x⁺ + y⁺) + z⁺) + (x⁻ + (y⁻ + z⁻))
            ≃⟨ AA.substᴸ AA.assoc ⟩
              (x⁺ + (y⁺ + z⁺)) + (x⁻ + (y⁻ + z⁻))
            ≃˘⟨ AA.substᴿ AA.assoc ⟩
              (x⁺ + (y⁺ + z⁺)) + ((x⁻ + y⁻) + z⁻)
            ∎

instance
  number : Number ℤ
  number = record { Constraint = λ _ → ⊤ ; fromNat = fromNat }
    where
      fromNat : Nat.Nat → {{_ : ⊤}} → ℤ
      fromNat Nat.zero = 0 — 0
      fromNat (Nat.suc n) = 1 — 0 + fromNat n

  from-ℕ : ℕ As ℤ
  from-ℕ = record { cast = λ n → n — 0 }

  from-ℕ-substitutive₁ : AA.Substitutive₁ {A = ℕ} (_as ℤ)
  from-ℕ-substitutive₁ = record { subst = ≃ᶻ-intro ∘ AA.substᴸ }

ℤ≃→ℕ≃ : {n : ℕ} → (n as ℤ) ≃ 0 → n ≃ 0
ℤ≃→ℕ≃ {n} (≃ᶻ-intro n+0≃0+0) =
  begin
    n
  ≃˘⟨ AA.identᴿ ⟩
    n + 0
  ≃⟨ n+0≃0+0 ⟩
    0 + 0
  ≃⟨ AA.identᴸ ⟩
    0
  ∎

+-to-+ : {n m : ℕ} → (n + m as ℤ) ≃ (n as ℤ) + (m as ℤ)
+-to-+ = ≃ᶻ-intro (AA.substᴿ AA.identᴸ)

+-identityᴸ : {x : ℤ} → 0 + x ≃ x
+-identityᴸ {x⁺ — x⁻} = ≃ᶻ-intro [0+x⁺]+x⁻≃x⁺+[0+x⁻]
  where
    [0+x⁺]+x⁻≃x⁺+[0+x⁻] =
      begin
        0 + x⁺ + x⁻
      ≃⟨ AA.substᴸ AA.comm ⟩
        x⁺ + 0 + x⁻
      ≃⟨ AA.assoc ⟩
        x⁺ + (0 + x⁻)
      ∎

+-identityᴿ : {x : ℤ} → x + 0 ≃ x
+-identityᴿ {x} =
  begin
    x + 0
  ≃⟨ AA.comm ⟩
    0 + x
  ≃⟨ +-identityᴸ ⟩
    x
  ∎
