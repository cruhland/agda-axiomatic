import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators using (_+_; -_)
open import net.cruhland.axioms.Ordering using (_<_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Sign
  using (Negative; Negativity; Positive; Positivity)
open import net.cruhland.models.Function using (_⟨→⟩_; id)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (contra)

module net.cruhland.models.Integers.Sign.BaseImplLt (PA : PeanoArithmetic) where

private open module ℕ = PeanoArithmetic PA using (ℕ)
open import net.cruhland.models.Integers.Base PA as ℤ using (_—_; ℤ)
import net.cruhland.models.Integers.Equality PA as ℤ≃
import net.cruhland.models.Integers.Negation PA as ℤ-

Pos : ℤ → Set
Pos (x⁺ — x⁻) = x⁻ < x⁺

x≄0-from-Pos[x] : ∀ {x} → Pos x → x ≄ 0
x≄0-from-Pos[x] {x⁺ — x⁻} x⁻<x⁺ (ℤ≃.≃ᶻ-intro x⁺+0≃0+x⁻) =
  let x⁻≃x⁺ =
        begin
          x⁻
        ≃˘⟨ AA.ident ⟩
          0 + x⁻
        ≃˘⟨ x⁺+0≃0+x⁻ ⟩
          x⁺ + 0
        ≃⟨ AA.ident ⟩
          x⁺
        ∎
      x⁻≄x⁺ = ℕ.<-elim-≄ x⁻<x⁺
   in contra x⁻≃x⁺ x⁻≄x⁺

instance
  Pos-substitutive : AA.Substitutive₁ Pos _≃_ _⟨→⟩_
  Pos-substitutive = AA.substitutive₁ Pos-subst
    where
      Pos-subst : ∀ {a b} → a ≃ b → Pos a → Pos b
      Pos-subst {a⁺ — a⁻} {b⁺ — b⁻} (ℤ≃.≃ᶻ-intro a⁺+b⁻≃b⁺+a⁻) a⁻<a⁺ =
        let d = ℕ.<-diff a⁻<a⁺
            pos[d] = ℕ.<-diff-pos a⁻<a⁺
            a⁻+d≃a⁺ = ℕ.<-elim-diff a⁻<a⁺
            b⁻+d+a⁻≃b⁺+a⁻ =
              begin
                b⁻ + d + a⁻
              ≃⟨ AA.assoc ⟩
                b⁻ + (d + a⁻)
              ≃⟨ AA.subst₂ AA.comm ⟩
                b⁻ + (a⁻ + d)
              ≃⟨ AA.subst₂ a⁻+d≃a⁺ ⟩
                b⁻ + a⁺
              ≃⟨ AA.comm ⟩
                a⁺ + b⁻
              ≃⟨ a⁺+b⁻≃b⁺+a⁻ ⟩
                b⁺ + a⁻
              ∎
            b⁻+d≃b⁺ = AA.cancel b⁻+d+a⁻≃b⁺+a⁻
         in ℕ.<-intro-diff pos[d] b⁻+d≃b⁺

  positivity : Positivity {A = ℤ} 0
  positivity = record { Positive = Pos ; pos≄0 = x≄0-from-Pos[x] }

pos-intro-ℕ : {n : ℕ} {x : ℤ} → Positive n → (n as ℤ) ≃ x → Positive x
pos-intro-ℕ {n} {x⁺ — x⁻} pos[n] (ℤ≃.≃ᶻ-intro n+x⁻≃x⁺+0) =
  let x⁻+n≃x⁺ =
        begin
          x⁻ + n
        ≃⟨ AA.comm ⟩
          n + x⁻
        ≃⟨ n+x⁻≃x⁺+0 ⟩
          x⁺ + 0
        ≃⟨ AA.ident ⟩
          x⁺
        ∎
   in ℕ.<-intro-diff pos[n] x⁻+n≃x⁺

pos-ℕ : {x : ℤ} → Positive x → ℕ
pos-ℕ = ℕ.<-diff

pos-ℕ-pos : {x : ℤ} (pos[x] : Positive x) → Positive (pos-ℕ pos[x])
pos-ℕ-pos = ℕ.<-diff-pos

pos-ℕ-eq : {x : ℤ} (pos[x] : Positive x) → (pos-ℕ pos[x] as ℤ) ≃ x
pos-ℕ-eq {x⁺ — x⁻} x⁻<x⁺ =
  let d = ℕ.<-diff x⁻<x⁺
      x⁻+d≃x⁺ = ℕ.<-elim-diff x⁻<x⁺
      d+x⁻≃x⁺+0 =
        begin
          d + x⁻
        ≃⟨ AA.comm ⟩
          x⁻ + d
        ≃⟨ x⁻+d≃x⁺ ⟩
          x⁺
        ≃˘⟨ AA.ident ⟩
          x⁺ + 0
        ∎
   in ℤ≃.≃ᶻ-intro d+x⁻≃x⁺+0

pos-intro-proj : {x : ℤ} → ℤ.neg x < ℤ.pos x → Positive x
pos-intro-proj = id

pos-elim-proj : {x : ℤ} → Positive x → ℤ.neg x < ℤ.pos x
pos-elim-proj = id

Neg : ℤ → Set
Neg (x⁺ — x⁻) = x⁺ < x⁻

x≄0-from-Neg[x] : ∀ {x} → Neg x → x ≄ 0
x≄0-from-Neg[x] {x⁺ — x⁻} x⁺<x⁻ (ℤ≃.≃ᶻ-intro x⁺+0≃0+x⁻) =
  let x⁺≃x⁻ =
        begin
          x⁺
        ≃˘⟨ AA.ident ⟩
          x⁺ + 0
        ≃⟨ x⁺+0≃0+x⁻ ⟩
          0 + x⁻
        ≃⟨ AA.ident ⟩
          x⁻
        ∎
      x⁺≄x⁻ = ℕ.<-elim-≄ x⁺<x⁻
   in contra x⁺≃x⁻ x⁺≄x⁻

instance
  Neg-substitutive : AA.Substitutive₁ Neg _≃_ _⟨→⟩_
  Neg-substitutive = AA.substitutive₁ Neg-subst
    where
      Neg-subst : ∀ {a b} → a ≃ b → Neg a → Neg b
      Neg-subst {a⁺ — a⁻} {b⁺ — b⁻} (ℤ≃.≃ᶻ-intro a⁺+b⁻≃b⁺+a⁻) a⁺<a⁻ =
        let d = ℕ.<-diff a⁺<a⁻
            pos[d] = ℕ.<-diff-pos a⁺<a⁻
            a⁺+d≃a⁻ = ℕ.<-elim-diff a⁺<a⁻
            a⁺+[b⁺+d]≃a⁺+b⁻ =
              begin
                a⁺ + (b⁺ + d)
              ≃˘⟨ AA.assoc ⟩
                (a⁺ + b⁺) + d
              ≃⟨ AA.subst₂ AA.comm ⟩
                (b⁺ + a⁺) + d
              ≃⟨ AA.assoc ⟩
                b⁺ + (a⁺ + d)
              ≃⟨ AA.subst₂ a⁺+d≃a⁻ ⟩
                b⁺ + a⁻
              ≃˘⟨ a⁺+b⁻≃b⁺+a⁻ ⟩
                a⁺ + b⁻
              ∎
            b⁺+d≃b⁻ = AA.cancel a⁺+[b⁺+d]≃a⁺+b⁻
         in ℕ.<-intro-diff pos[d] b⁺+d≃b⁻

  negativity : Negativity {A = ℤ} 0
  negativity = record { Negative = Neg ; neg≄0 = x≄0-from-Neg[x] }

neg-intro-ℕ : {n : ℕ} {x : ℤ} → Positive n → - (n as ℤ) ≃ x → Negative x
neg-intro-ℕ {n} {x⁺ — x⁻} pos[n] (ℤ≃.≃ᶻ-intro 0+x⁻≃x⁺+n) =
  let x⁺+n≃x⁻ =
        begin
          x⁺ + n
        ≃˘⟨ 0+x⁻≃x⁺+n ⟩
          0 + x⁻
        ≃⟨ AA.ident ⟩
          x⁻
        ∎
   in ℕ.<-intro-diff pos[n] x⁺+n≃x⁻

neg-ℕ : {x : ℤ} → Negative x → ℕ
neg-ℕ = ℕ.<-diff

neg-ℕ-pos : {x : ℤ} (neg[x] : Negative x) → Positive (neg-ℕ neg[x])
neg-ℕ-pos = ℕ.<-diff-pos

neg-ℕ-eq : {x : ℤ} (neg[x] : Negative x) → - (neg-ℕ neg[x] as ℤ) ≃ x
neg-ℕ-eq {x⁺ — x⁻} x⁺<x⁻ =
  let d = ℕ.<-diff x⁺<x⁻
      x⁺+d≃x⁻ = ℕ.<-elim-diff x⁺<x⁻
      0+x⁻≃x⁺+d =
        begin
          0 + x⁻
        ≃⟨ AA.ident ⟩
          x⁻
        ≃˘⟨ x⁺+d≃x⁻ ⟩
          x⁺ + d
        ∎
   in ℤ≃.≃ᶻ-intro 0+x⁻≃x⁺+d

neg-intro-proj : {x : ℤ} → ℤ.pos x < ℤ.neg x → Negative x
neg-intro-proj = id

neg-elim-proj : {x : ℤ} → Negative x → ℤ.pos x < ℤ.neg x
neg-elim-proj = id
