import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators using (_+_; -_)
open import net.cruhland.axioms.Ordering using (_<_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Sign
  using (Negative; Negativity; Positive; Positivity; pos≄0)
open import net.cruhland.models.Function using (_⟨→⟩_)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (contra)

module net.cruhland.models.Integers.Sign.BaseImplEq (PA : PeanoArithmetic) where

private open module ℕ = PeanoArithmetic PA using (ℕ)
open import net.cruhland.models.Integers.Base PA as ℤ using (_—_; ℤ)
import net.cruhland.models.Integers.Equality PA as ℤ≃
import net.cruhland.models.Integers.Negation PA as ℤ-

record posℕ≃ (x : ℤ) : Set where
  constructor posℕ≃-intro
  field
    {n} : ℕ
    pos[n] : Positive n
    n≃x : (n as ℤ) ≃ x

x≄0-from-posℕ≃x : ∀ {x} → posℕ≃ x → x ≄ 0
x≄0-from-posℕ≃x
    {x⁺ — x⁻}
    (posℕ≃-intro pos[n] (ℤ≃.≃ᶻ-intro n+x⁻≃x⁺+0))
    (ℤ≃.≃ᶻ-intro x⁺+0≃0+x⁻) =
  let n+x⁻≃0+x⁻ = Eq.trans n+x⁻≃x⁺+0 x⁺+0≃0+x⁻
      n≃0 = AA.cancel n+x⁻≃0+x⁻
      n≄0 = pos≄0 pos[n]
   in contra n≃0 n≄0

instance
  posℕ≃-substitutive : AA.Substitutive₁ posℕ≃ _≃_ _⟨→⟩_
  posℕ≃-substitutive = AA.substitutive₁ posℕ≃-subst
    where
      posℕ≃-subst : ∀ {a b} → a ≃ b → posℕ≃ a → posℕ≃ b
      posℕ≃-subst a≃b (posℕ≃-intro pos[n] n≃a) =
        posℕ≃-intro pos[n] (Eq.trans n≃a a≃b)

  positivity : Positivity {A = ℤ} 0
  positivity = record { Positive = posℕ≃ ; pos≄0 = x≄0-from-posℕ≃x }

pos-intro-ℕ : {n : ℕ} {x : ℤ} → Positive n → (n as ℤ) ≃ x → Positive x
pos-intro-ℕ = posℕ≃-intro

pos-ℕ : {x : ℤ} → Positive x → ℕ
pos-ℕ = posℕ≃.n

pos-ℕ-pos : {x : ℤ} (pos[x] : Positive x) → Positive (pos-ℕ pos[x])
pos-ℕ-pos = posℕ≃.pos[n]

pos-ℕ-eq : {x : ℤ} (pos[x] : Positive x) → (pos-ℕ pos[x] as ℤ) ≃ x
pos-ℕ-eq = posℕ≃.n≃x

pos-intro-proj : {x : ℤ} → ℤ.neg x < ℤ.pos x → Positive x
pos-intro-proj {x⁺ — x⁻} x⁻<x⁺ =
  let n = ℕ.<-diff x⁻<x⁺
      pos[n] = ℕ.<-diff-pos x⁻<x⁺
      x⁻+n≃x⁺ = ℕ.<-elim-diff x⁻<x⁺
      n+x⁻≃x⁺+0 =
        begin
          n + x⁻
        ≃⟨ AA.comm ⟩
          x⁻ + n
        ≃⟨ x⁻+n≃x⁺ ⟩
          x⁺
        ≃˘⟨ AA.ident ⟩
          x⁺ + 0
        ∎
      n≃x = ℤ≃.≃ᶻ-intro n+x⁻≃x⁺+0
   in posℕ≃-intro pos[n] n≃x

pos-elim-proj : {x : ℤ} → Positive x → ℤ.neg x < ℤ.pos x
pos-elim-proj {x⁺ — x⁻} (posℕ≃-intro {n} pos[n] (ℤ≃.≃ᶻ-intro n+x⁻≃x⁺+0)) =
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

record negℕ≃ (x : ℤ) : Set where
  constructor negℕ≃-intro
  field
    {n} : ℕ
    pos[n] : Positive n
    -n≃x : - (n as ℤ) ≃ x

x≄0-from-negℕ≃x : ∀ {x} → negℕ≃ x → x ≄ 0
x≄0-from-negℕ≃x
    {x⁺ — x⁻}
    (negℕ≃-intro pos[n] (ℤ≃.≃ᶻ-intro 0+x⁻≃x⁺+n))
    (ℤ≃.≃ᶻ-intro x⁺+0≃0+x⁻) =
  let x⁺+0≃x⁺+n = Eq.trans x⁺+0≃0+x⁻ 0+x⁻≃x⁺+n
      n≃0 = Eq.sym (AA.cancel x⁺+0≃x⁺+n)
      n≄0 = pos≄0 pos[n]
   in contra n≃0 n≄0

instance
  negℕ≃-substitutive : AA.Substitutive₁ negℕ≃ _≃_ _⟨→⟩_
  negℕ≃-substitutive = AA.substitutive₁ negℕ≃-subst
    where
      negℕ≃-subst : ∀ {a b} → a ≃ b → negℕ≃ a → negℕ≃ b
      negℕ≃-subst a≃b (negℕ≃-intro pos[n] -n≃a) =
        negℕ≃-intro pos[n] (Eq.trans -n≃a a≃b)

  negativity : Negativity {A = ℤ} 0
  negativity = record { Negative = negℕ≃ ; neg≄0 = x≄0-from-negℕ≃x }

neg-intro-ℕ : {n : ℕ} {x : ℤ} → Positive n → - (n as ℤ) ≃ x → Negative x
neg-intro-ℕ = negℕ≃-intro

neg-ℕ : {x : ℤ} → Negative x → ℕ
neg-ℕ = negℕ≃.n

neg-ℕ-pos : {x : ℤ} (neg[x] : Negative x) → Positive (neg-ℕ neg[x])
neg-ℕ-pos = negℕ≃.pos[n]

neg-ℕ-eq : {x : ℤ} (neg[x] : Negative x) → - (neg-ℕ neg[x] as ℤ) ≃ x
neg-ℕ-eq = negℕ≃.-n≃x

neg-intro-proj : {x : ℤ} → ℤ.pos x < ℤ.neg x → Negative x
neg-intro-proj {x⁺ — x⁻} x⁺<x⁻ =
  let n = ℕ.<-diff x⁺<x⁻
      pos[n] = ℕ.<-diff-pos x⁺<x⁻
      x⁺+n≃x⁻ = ℕ.<-elim-diff x⁺<x⁻
      0+x⁻≃x⁺+n =
        begin
          0 + x⁻
        ≃⟨ AA.ident ⟩
          x⁻
        ≃˘⟨ x⁺+n≃x⁻ ⟩
          x⁺ + n
        ∎
      -n≃x = ℤ≃.≃ᶻ-intro 0+x⁻≃x⁺+n
   in negℕ≃-intro pos[n] -n≃x

neg-elim-proj : {x : ℤ} → Negative x → ℤ.pos x < ℤ.neg x
neg-elim-proj {x⁺ — x⁻} (negℕ≃-intro {n} pos[n] (ℤ≃.≃ᶻ-intro 0+x⁻≃x⁺+n)) =
  let x⁺+n≃x⁻ =
        begin
          x⁺ + n
        ≃˘⟨ 0+x⁻≃x⁺+n ⟩
          0 + x⁻
        ≃⟨ AA.ident ⟩
          x⁻
        ∎
   in ℕ.<-intro-diff pos[n] x⁺+n≃x⁻
