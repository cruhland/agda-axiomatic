open import Relation.Nullary.Decidable using (fromWitnessFalse)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq
  using (_≃_; _≄_; sym; trans; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.axioms.Operators as Op using (_+_; _*_; -_; _-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Sign
  using (Negative; Negativity; Positive; Positivity)
import net.cruhland.models.Function
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (_∨_; ∨-introᴸ; ∨-introᴿ)

module net.cruhland.models.Integers.Multiplication (PA : PeanoArithmetic) where

private module ℕ = PeanoArithmetic PA
open ℕ using (ℕ)
import net.cruhland.models.Integers.Addition PA as ℤ+
open import net.cruhland.models.Integers.Base PA as ℤ using (_—_; ℤ)
open import net.cruhland.models.Integers.Equality PA as ℤ≃ using (≃ᶻ-intro)
open import net.cruhland.models.Integers.Negation PA as ℤ-
import net.cruhland.models.Integers.Sign PA as ℤS

instance
  -- TODO: Avoid explicit re-declaration of instances
  private negativity : Negativity 0
  negativity = ℤS.negativity

  private positivity : Positivity 0
  positivity = ℤS.positivity

  star : Op.Star ℤ
  star = record { _*_ = _*₀_ }
    where
      infixl 7 _*₀_
      _*₀_ : ℤ → ℤ → ℤ
      a⁺ — a⁻ *₀ b⁺ — b⁻ = (a⁺ * b⁺ + a⁻ * b⁻) — (a⁺ * b⁻ + a⁻ * b⁺)

  *-commutative : AA.Commutative _*_
  *-commutative = AA.commutative *-comm
    where
      *-comm : {a b : ℤ} → a * b ≃ b * a
      *-comm {a⁺ — a⁻} {b⁺ — b⁻} = ≃ᶻ-intro eq′
        where
          eq′ =
            begin
              (a⁺ * b⁺ + a⁻ * b⁻) + (b⁺ * a⁻ + b⁻ * a⁺)
            ≃⟨ AA.subst₂ (AA.subst₂ AA.comm) ⟩
              (b⁺ * a⁺ + a⁻ * b⁻) + (b⁺ * a⁻ + b⁻ * a⁺)
            ≃⟨ AA.subst₂ (AA.subst₂ AA.comm) ⟩
              (b⁺ * a⁺ + b⁻ * a⁻) + (b⁺ * a⁻ + b⁻ * a⁺)
            ≃⟨ AA.subst₂ AA.comm ⟩
              (b⁺ * a⁺ + b⁻ * a⁻) + (b⁻ * a⁺ + b⁺ * a⁻)
            ≃⟨ AA.subst₂ (AA.subst₂ AA.comm) ⟩
              (b⁺ * a⁺ + b⁻ * a⁻) + (a⁺ * b⁻ + b⁺ * a⁻)
            ≃⟨ AA.subst₂ (AA.subst₂ AA.comm) ⟩
              (b⁺ * a⁺ + b⁻ * a⁻) + (a⁺ * b⁻ + a⁻ * b⁺)
            ∎

  *-substitutiveᴸ : AA.Substitutive₂ AA.handᴸ _*_ _≃_ _≃_
  *-substitutiveᴸ = AA.substitutive₂ *-substᴸ
    where
      *-substᴸ : {a₁ a₂ b : ℤ} → a₁ ≃ a₂ → a₁ * b ≃ a₂ * b
      *-substᴸ {a₁⁺ — a₁⁻} {a₂⁺ — a₂⁻} {b⁺ — b⁻} (≃ᶻ-intro a₁⁺a₂⁻≃a₂⁺a₁⁻) =
          ≃ᶻ-intro [a₁⁺b⁺+a₁⁻b⁻]+[a₂⁺b⁻+a₂⁻b⁺]≃[a₂⁺b⁺+a₂⁻b⁻]+[a₁⁺b⁻+a₁⁻b⁺]
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

          [a₁⁺b⁺+a₁⁻b⁻]+[a₂⁺b⁻+a₂⁻b⁺]≃[a₂⁺b⁺+a₂⁻b⁻]+[a₁⁺b⁻+a₁⁻b⁺] =
            begin
              (a₁⁺ * b⁺ + a₁⁻ * b⁻) + (a₂⁺ * b⁻ + a₂⁻ * b⁺)
            ≃⟨ rearr {w = a₁⁺} {y = a₂⁺} ⟩
              (a₁⁺ + a₂⁻) * b⁺ + (a₂⁺ + a₁⁻) * b⁻
            ≃⟨ AA.subst₂ (AA.subst₂ a₁⁺a₂⁻≃a₂⁺a₁⁻) ⟩
              (a₂⁺ + a₁⁻) * b⁺ + (a₂⁺ + a₁⁻) * b⁻
            ≃˘⟨ AA.subst₂ (AA.subst₂ a₁⁺a₂⁻≃a₂⁺a₁⁻) ⟩
              (a₂⁺ + a₁⁻) * b⁺ + (a₁⁺ + a₂⁻) * b⁻
            ≃˘⟨ rearr {w = a₂⁺} {y = a₁⁺} ⟩
              (a₂⁺ * b⁺ + a₂⁻ * b⁻) + (a₁⁺ * b⁻ + a₁⁻ * b⁺)
            ∎

  *-substitutiveᴿ : AA.Substitutive₂ AA.handᴿ _*_ _≃_ _≃_
  *-substitutiveᴿ = AA.substᴿ-from-substᴸ-comm {A = ℤ}

  *-substitutive : AA.Substitutive² _*_ _≃_ _≃_
  *-substitutive = AA.substitutive² {A = ℤ}

  *-compatible-ℕ : AA.Compatible₂ (_as ℤ) _*_
  *-compatible-ℕ = AA.compatible₂ {A = ℕ} _*_ *-compat-ℕ
    where
      *-compat-ℕ : {n m : ℕ} → (n * m as ℤ) ≃ (n as ℤ) * (m as ℤ)
      *-compat-ℕ {n} {m} = ≃ᶻ-intro nm+n0+0m≃nm+00+0
        where
          nm+n0+0m≃nm+00+0 =
            begin
              n * m + (n * 0 + 0 * m)
            ≃⟨ AA.subst₂ (AA.subst₂ AA.absorb) ⟩
              n * m + (0 + 0 * m)
            ≃˘⟨ AA.subst₂ (AA.subst₂ AA.absorbᴿ) ⟩
              n * m + (0 * 0 + 0 * m)
            ≃⟨ AA.subst₂ (AA.subst₂ AA.absorb) ⟩
              n * m + (0 * 0 + 0)
            ≃˘⟨ AA.assoc ⟩
              n * m + 0 * 0 + 0
            ∎

  *-identityᴸ : AA.Identity AA.handᴸ _*_ 1
  *-identityᴸ = AA.identity *-identᴸ
    where
      *-identᴸ : {x : ℤ} → 1 * x ≃ x
      *-identᴸ {x⁺ — x⁻} = ≃ᶻ-intro [1x⁺+0x⁻]+x⁻≃x⁺+[1x⁻+0x⁺]
        where
          [1x⁺+0x⁻]+x⁻≃x⁺+[1x⁻+0x⁺] =
            begin
              (1 * x⁺ + 0 * x⁻) + x⁻
            ≃⟨ AA.subst₂ (AA.subst₂ AA.ident) ⟩
              (x⁺ + 0 * x⁻) + x⁻
            ≃⟨ AA.subst₂ (AA.subst₂ AA.absorb) ⟩
              (x⁺ + 0) + x⁻
            ≃⟨ AA.subst₂ AA.ident ⟩
              x⁺ + x⁻
            ≃˘⟨ AA.subst₂ AA.ident ⟩
              x⁺ + (x⁻ + 0)
            ≃˘⟨ AA.subst₂ (AA.subst₂ AA.absorb) ⟩
              x⁺ + (x⁻ + 0 * x⁺)
            ≃˘⟨ AA.subst₂ (AA.subst₂ AA.ident) ⟩
              x⁺ + (1 * x⁻ + 0 * x⁺)
            ∎

  *-identityᴿ : AA.Identity AA.handᴿ _*_ 1
  *-identityᴿ = AA.identityᴿ-from-identityᴸ {A = ℤ}

  *-distributive-+ᴸ : AA.Distributive AA.handᴸ _*_ _+_
  *-distributive-+ᴸ = AA.distributive *-distrib-+ᴸ
    where
      *-distrib-+ᴸ : {x y z : ℤ} → x * (y + z) ≃ x * y + x * z
      *-distrib-+ᴸ {x⁺ — x⁻} {y⁺ — y⁻} {z⁺ — z⁻} =
          ≃ᶻ-intro
            (AA.[a≃b][c≃d] (refactor {x⁺} {x⁻})
            (sym (refactor {x⁺} {x⁻})))
        where
          refactor :
            ∀ {b₁ b₂ a₁ a₂ a₃ a₄} →
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

  *-distributive-+ᴿ : AA.Distributive AA.handᴿ _*_ _+_
  *-distributive-+ᴿ = AA.distributiveᴿ-from-distributiveᴸ {A = ℤ}

  *-associative : AA.Associative _*_
  *-associative = record { assoc = *-assoc }
    where
      *-assoc : {x y z : ℤ} → (x * y) * z ≃ x * (y * z)
      *-assoc {x⁺ — x⁻} {y⁺ — y⁻} {z⁺ — z⁻} = ≃ᶻ-intro ≃-assoc
        where
          ≃-assoc = AA.[a≃b][c≃d] AA.refactor (sym AA.refactor)

  *-fnOpCommutative-negᴸ : AA.FnOpCommutative AA.handᴸ -_ _*_
  *-fnOpCommutative-negᴸ = AA.fnOpCommutative *-negᴸ
    where
      *-negᴸ : {a b : ℤ} → - (a * b) ≃ - a * b
      *-negᴸ {a⁺ — a⁻} {b⁺ — b⁻} = ≃ᶻ-intro eqPrf
        where
          eqPrf =
            begin
              (a⁺ * b⁻ + a⁻ * b⁺) + (a⁻ * b⁻ + a⁺ * b⁺)
            ≃⟨ AA.subst₂ AA.comm ⟩
              (a⁺ * b⁻ + a⁻ * b⁺) + (a⁺ * b⁺ + a⁻ * b⁻)
            ≃⟨ AA.subst₂ AA.comm ⟩
              (a⁻ * b⁺ + a⁺ * b⁻) + (a⁺ * b⁺ + a⁻ * b⁻)
            ∎

  *-fnOpCommutative-negᴿ : AA.FnOpCommutative AA.handᴿ -_ _*_
  *-fnOpCommutative-negᴿ = AA.fnOpCommutativeᴿ-from-fnOpCommutativeᴸ

neg-mult : {a : ℤ} → - a ≃ -1 * a
neg-mult {a⁺ — a⁻} = AA.[a≃b][c≃d] x≃0y+1x x≃0y+1x
  where
    x≃0y+1x : {x y : ℕ} → x ≃ 0 * y + 1 * x
    x≃0y+1x {x} {y} =
      begin
        x
      ≃˘⟨ AA.ident ⟩
        0 + x
      ≃˘⟨ AA.subst₂ AA.absorb ⟩
        0 * y + x
      ≃˘⟨ AA.subst₂ AA.ident ⟩
        0 * y + 1 * x
      ∎

*-distrib-subᴸ : {a b c : ℤ} → c * (a - b) ≃ c * a - c * b
*-distrib-subᴸ {a} {b} {c} =
  begin
    c * (a - b)
  ≃⟨⟩
    c * (a + - b)
  ≃⟨ AA.distrib ⟩
    c * a + c * - b
  ≃˘⟨ AA.substᴿ {A = ℤ} AA.fnOpComm ⟩
    c * a + - (c * b)
  ≃⟨⟩
    c * a - c * b
  ∎

*-distrib-subᴿ : {a b c : ℤ} → (a - b) * c ≃ a * c - b * c
*-distrib-subᴿ {a} {b} {c} =
  begin
    (a - b) * c
  ≃⟨⟩
    (a + - b) * c
  ≃⟨ AA.distrib ⟩
    a * c + (- b) * c
  ≃˘⟨ AA.subst₂ AA.fnOpComm ⟩
    a * c + - (b * c)
  ≃⟨⟩
    a * c - b * c
  ∎

instance
  *-absorptiveᴸ : AA.Absorptive AA.handᴸ _*_ 0
  *-absorptiveᴸ = AA.absorptive *-zeroᴸ
    where
      *-zeroᴸ : {x : ℤ} → 0 * x ≃ 0
      *-zeroᴸ {x} =
        begin
          0 * x
        ≃˘⟨ AA.subst₂ AA.invᴿ ⟩
          (1 - 1) * x
        ≃⟨ *-distrib-subᴿ ⟩
          1 * x - 1 * x
        ≃⟨ AA.invᴿ ⟩
          0
        ∎

  *-absorptiveᴿ : AA.Absorptive AA.handᴿ _*_ 0
  *-absorptiveᴿ = AA.absorptiveᴿ-from-absorptiveᴸ {A = ℤ}

neg-sub-swap : ∀ {a b} → - (a - b) ≃ b - a
neg-sub-swap {a} {b} =
  begin
    - (a - b)
  ≃⟨ neg-mult ⟩
    -1 * (a - b)
  ≃⟨ *-distrib-subᴸ {a} {b} { -1} ⟩
    -1 * a - -1 * b
  ≃˘⟨ AA.subst₂ neg-mult ⟩
    - a - -1 * b
  ≃˘⟨ AA.subst₂ (AA.subst₁ neg-mult) ⟩
    - a - (- b)
  ≃⟨ AA.substᴿ neg-involutive ⟩
    - a + b
  ≃˘⟨ AA.comm ⟩
    b - a
  ∎

sub-sign-swap : {a b : ℤ} → Negative (a - b) → Positive (b - a)
sub-sign-swap a⁺+b⁻<a⁻+b⁺ = AA.substᴸ AA.comm (AA.substᴿ AA.comm a⁺+b⁻<a⁻+b⁺)

instance
  zero-product : AA.ZeroProduct _*_
  zero-product = AA.zeroProduct 0 *-either-zero
    where
      *-either-zero : {a b : ℤ} → a * b ≃ 0 → a ≃ 0 ∨ b ≃ 0
      *-either-zero
          a@{a⁺ — a⁻} b@{b⁺ — b⁻} (≃ᶻ-intro [a⁺b⁺+a⁻b⁻]+0≃0+[a⁺b⁻+a⁻b⁺])
            with AA.ExactlyOneOfThree.at-least-one (ℤS.trichotomy a)
      ... | AA.1st a⁺<a⁻ =
        let n = ℕ.<-diff a⁺<a⁻
            instance pos[n] = ℕ.<-diff-pos a⁺<a⁻
            a⁺+n≃a⁻ = ℕ.<-elim-diff a⁺<a⁻
            a⁺[b⁺+b⁻]+nb⁻≃a⁺[b⁺+b⁻]+nb⁺ =
              begin
                a⁺ * (b⁺ + b⁻) + n * b⁻
              ≃⟨ AA.subst₂ AA.distrib ⟩
                a⁺ * b⁺ + a⁺ * b⁻ + n * b⁻
              ≃⟨ AA.assoc ⟩
                a⁺ * b⁺ + (a⁺ * b⁻ + n * b⁻)
              ≃˘⟨ AA.subst₂ AA.distrib ⟩
                a⁺ * b⁺ + (a⁺ + n) * b⁻
              ≃⟨ AA.subst₂ (AA.subst₂ a⁺+n≃a⁻) ⟩
                a⁺ * b⁺ + a⁻ * b⁻
              ≃˘⟨ AA.ident ⟩
                a⁺ * b⁺ + a⁻ * b⁻ + 0
              ≃⟨ [a⁺b⁺+a⁻b⁻]+0≃0+[a⁺b⁻+a⁻b⁺] ⟩
                0 + (a⁺ * b⁻ + a⁻ * b⁺)
              ≃⟨ AA.ident ⟩
                a⁺ * b⁻ + a⁻ * b⁺
              ≃˘⟨ AA.subst₂ (AA.subst₂ a⁺+n≃a⁻) ⟩
                a⁺ * b⁻ + (a⁺ + n) * b⁺
              ≃⟨ AA.subst₂ AA.distrib ⟩
                a⁺ * b⁻ + (a⁺ * b⁺ + n * b⁺)
              ≃˘⟨ AA.assoc ⟩
                (a⁺ * b⁻ + a⁺ * b⁺) + n * b⁺
              ≃⟨ AA.subst₂ AA.comm ⟩
                (a⁺ * b⁺ + a⁺ * b⁻) + n * b⁺
              ≃˘⟨ AA.subst₂ AA.distrib ⟩
                a⁺ * (b⁺ + b⁻) + n * b⁺
              ∎
            nb⁻≃nb⁺ = AA.cancel a⁺[b⁺+b⁻]+nb⁻≃a⁺[b⁺+b⁻]+nb⁺
            b⁺+0≃0+b⁻ =
              begin
                b⁺ + 0
              ≃˘⟨ AA.subst₂ (AA.cancel nb⁻≃nb⁺) ⟩
                b⁻ + 0
              ≃⟨ AA.comm ⟩
                0 + b⁻
              ∎
         in ∨-introᴿ (≃ᶻ-intro b⁺+0≃0+b⁻)
      ... | AA.2nd a≃0 = ∨-introᴸ a≃0
      ... | AA.3rd a⁻<a⁺ =
        let n = ℕ.<-diff a⁻<a⁺
            instance pos[n] = ℕ.<-diff-pos a⁻<a⁺
            a⁻+n≃a⁺ = ℕ.<-elim-diff a⁻<a⁺
            a⁻[b⁻+b⁺]+nb⁺≃a⁻[b⁻+b⁺]+nb⁻ =
              begin
                a⁻ * (b⁻ + b⁺) + n * b⁺
              ≃⟨ AA.subst₂ AA.distrib ⟩
                (a⁻ * b⁻ + a⁻ * b⁺) + n * b⁺
              ≃⟨ AA.assoc ⟩
                a⁻ * b⁻ + (a⁻ * b⁺ + n * b⁺)
              ≃⟨ AA.comm ⟩
                (a⁻ * b⁺ + n * b⁺) + a⁻ * b⁻
              ≃˘⟨ AA.subst₂ AA.distrib ⟩
                (a⁻ + n) * b⁺ + a⁻ * b⁻
              ≃⟨ AA.subst₂ (AA.subst₂ a⁻+n≃a⁺) ⟩
                a⁺ * b⁺ + a⁻ * b⁻
              ≃˘⟨ AA.ident ⟩
                a⁺ * b⁺ + a⁻ * b⁻ + 0
              ≃⟨ [a⁺b⁺+a⁻b⁻]+0≃0+[a⁺b⁻+a⁻b⁺] ⟩
                0 + (a⁺ * b⁻ + a⁻ * b⁺)
              ≃⟨ AA.ident ⟩
                a⁺ * b⁻ + a⁻ * b⁺
              ≃˘⟨ AA.subst₂ (AA.subst₂ a⁻+n≃a⁺) ⟩
                (a⁻ + n) * b⁻ + a⁻ * b⁺
              ≃⟨ AA.subst₂ AA.distrib ⟩
                (a⁻ * b⁻ + n * b⁻) + a⁻ * b⁺
              ≃⟨ AA.assoc ⟩
                a⁻ * b⁻ + (n * b⁻ + a⁻ * b⁺)
              ≃⟨ AA.subst₂ AA.comm ⟩
                a⁻ * b⁻ + (a⁻ * b⁺ + n * b⁻)
              ≃˘⟨ AA.assoc ⟩
                (a⁻ * b⁻ + a⁻ * b⁺) + n * b⁻
              ≃˘⟨ AA.subst₂ AA.distrib ⟩
                a⁻ * (b⁻ + b⁺) + n * b⁻
              ∎
            nb⁺≃nb⁻ = AA.cancel a⁻[b⁻+b⁺]+nb⁺≃a⁻[b⁻+b⁺]+nb⁻
            b⁺+0≃0+b⁻ =
              begin
                b⁺ + 0
              ≃⟨ AA.subst₂ (AA.cancel nb⁺≃nb⁻) ⟩
                b⁻ + 0
              ≃⟨ AA.comm ⟩
                0 + b⁻
              ∎
         in ∨-introᴿ (≃ᶻ-intro b⁺+0≃0+b⁻)
