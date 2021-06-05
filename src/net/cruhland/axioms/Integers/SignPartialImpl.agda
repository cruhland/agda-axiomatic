import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
import net.cruhland.axioms.Eq as Eq
open import net.cruhland.axioms.Integers.BaseDecl using (Base)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Sign using (Positive; Positivity)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Integers.SignPartialImpl
  (PA : PeanoArithmetic) (ZB : Base PA) where

private open module ℕ = PeanoArithmetic PA using (ℕ)
private open module ℤB = Base ZB using (ℤ)

record SignProperties : Set₁ where
  field
    {{positivity}} : Positivity {A = ℤ} 0
    from-ℕ-preserves-pos : {n : ℕ} → Positive n → Positive (n as ℤ)

  fromNatLiteral-preserves-pos :
    (n : Nat) → Positive {A = ℕ} (fromNatLiteral n) →
    Positive {A = ℤ} (fromNatLiteral n)
  fromNatLiteral-preserves-pos n pos[n] =
    let pos[a] = from-ℕ-preserves-pos pos[n]
     in AA.subst₁ (Eq.sym (ℤB.fromNatLiteral≃casts n)) pos[a]

  1-Positive : Positive 1
  1-Positive = fromNatLiteral-preserves-pos 1 (ℕ.Pos-intro-≄0 ℕ.step≄zero)
