import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators using (_/_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Rationals.AdditionDecl using (Addition)
open import net.cruhland.axioms.Rationals.BaseDecl using (Base)
open import net.cruhland.axioms.Rationals.MultiplicationDecl
  using (Multiplication)
open import net.cruhland.axioms.Rationals.ReciprocalDecl using (Reciprocal)
import net.cruhland.axioms.Sign as S
open import net.cruhland.models.Function using (_⟨→⟩_)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (_↯_)

module net.cruhland.axioms.Rationals.SignDefaultImpl
  (PA : PeanoArithmetic)
  (Z : Integers PA)
  (QB : Base PA Z)
  (QA : Addition PA Z QB)
  (QM : Multiplication PA Z QB QA)
  (QR : Reciprocal PA Z QB QA QM)
  where

import net.cruhland.axioms.Rationals.LiteralImpl PA Z as LiteralImpl

private module ℤ = Integers Z
private module ℚ where
  open Addition QA public
  open Base QB public
  open LiteralImpl QB public
  open Multiplication QM public
  open Reciprocal QR public

open ℤ using (ℤ)
open ℚ using (ℚ)

record Positive₀ (q : ℚ) : Set where
  constructor Positive₀-intro
  field
    {a b} : ℤ
    pos[a] : S.Positive a
    pos[b] : S.Positive b
    q≃a/b : let instance b≄0 = S.pos≄0 pos[b] in q ≃ a / b

q≄0-from-pos[q] : {q : ℚ} → Positive₀ q → q ≄ 0
q≄0-from-pos[q] {q} (Positive₀-intro {a} {b} pos[a] pos[b] q≃a/b) =
  Eq.≄-intro λ q≃0 →
    let instance
          b≄0 = S.pos≄0 pos[b]
        a/b≃0 =
          begin
            a / b
          ≃˘⟨ q≃a/b ⟩
            q
          ≃⟨ q≃0 ⟩
            0
          ∎
        a≃0 = ℚ.a≃0-from-a/b≃0 a/b≃0
        a≄0 = S.pos≄0 pos[a]
     in a≃0 ↯ a≄0

instance
  Positive₀-substitutive : AA.Substitutive₁ Positive₀ _≃_ _⟨→⟩_
  Positive₀-substitutive = AA.substitutive₁ pos-subst
    where
      pos-subst : {p q : ℚ} → p ≃ q → Positive₀ p → Positive₀ q
      pos-subst p≃q (Positive₀-intro pos[a] pos[b] p≃a/b) =
        Positive₀-intro pos[a] pos[b] (Eq.trans (Eq.sym p≃q) p≃a/b)

  positivity : S.Positivity 0
  positivity = record { Positive = Positive₀ ; pos≄0 = q≄0-from-pos[q] }
