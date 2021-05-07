open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Operators using (-_)
open import net.cruhland.axioms.Ordering using (_<_)
open import net.cruhland.axioms.Sign
  using (Negative; Negativity; Positive; Positivity)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.models.Integers.Sign.BaseDecl (PA : PeanoArithmetic) where

private open module ℕ = PeanoArithmetic PA using (ℕ)
open import net.cruhland.models.Integers.Base PA as ℤ using (ℤ; from-ℕ)
import net.cruhland.models.Integers.Equality PA as ℤ≃
import net.cruhland.models.Integers.Negation PA as ℤ-

record SignBase : Set₁ where
  field
    {{positivity}} : Positivity {A = ℤ} 0
    pos-intro-ℕ : {n : ℕ} {x : ℤ} → Positive n → (n as ℤ) ≃ x → Positive x
    pos-ℕ : {x : ℤ} → Positive x → ℕ
    pos-ℕ-pos : {x : ℤ} (pos[x] : Positive x) → Positive (pos-ℕ pos[x])
    pos-ℕ-eq : {x : ℤ} (pos[x] : Positive x) → (pos-ℕ pos[x] as ℤ) ≃ x

    pos-intro-proj : {x : ℤ} → ℤ.neg x < ℤ.pos x → Positive x
    pos-elim-proj : {x : ℤ} → Positive x → ℤ.neg x < ℤ.pos x

    {{negativity}} : Negativity {A = ℤ} 0
    neg-intro-ℕ : {n : ℕ} {x : ℤ} → Positive n → - (n as ℤ) ≃ x → Negative x
    neg-ℕ : {x : ℤ} → Negative x → ℕ
    neg-ℕ-pos : {x : ℤ} (neg[x] : Negative x) → Positive (neg-ℕ neg[x])
    neg-ℕ-eq : {x : ℤ} (neg[x] : Negative x) → - (neg-ℕ neg[x] as ℤ) ≃ x

    neg-intro-proj : {x : ℤ} → ℤ.pos x < ℤ.neg x → Negative x
    neg-elim-proj : {x : ℤ} → Negative x → ℤ.pos x < ℤ.neg x
